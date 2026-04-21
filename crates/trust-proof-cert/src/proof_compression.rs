// trust-proof-cert proof compression
//
// Compress proof certificates to reduce storage and transmission size.
// Supports deduplication, structural sharing (hash-consing), and DAG compaction.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::CertError;
use trust_types::fx::FxHashSet;

/// Compression methods for proof certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum CompressionMethod {
    /// Deduplicate identical byte sequences.
    Dedup,
    /// Share common subtrees via hash-consing.
    StructuralSharing,
    /// Compact proof DAG by merging equivalent nodes.
    DagCompaction,
}

/// A compressed proof certificate with metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CompressedCert {
    /// Compressed byte payload.
    pub data: Vec<u8>,
    /// Compression method used.
    pub method: CompressionMethod,
    /// Original (uncompressed) size in bytes.
    pub original_size: usize,
    /// Compressed size in bytes.
    pub compressed_size: usize,
    /// SHA-256 hash of the original uncompressed data for integrity verification.
    pub original_hash: [u8; 32],
}

/// Statistics tracking compression effectiveness.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct CompressionStats {
    /// Total bytes before compression.
    pub total_original_bytes: usize,
    /// Total bytes after compression.
    pub total_compressed_bytes: usize,
    /// Number of certificates compressed.
    pub certificates_compressed: usize,
    /// Number of duplicate subtrees found and shared.
    pub dedup_hits: usize,
    /// Number of DAG nodes merged.
    pub nodes_merged: usize,
}

impl Default for CompressionStats {
    fn default() -> Self {
        Self::new()
    }
}

impl CompressionStats {
    /// Create empty stats.
    pub fn new() -> Self {
        CompressionStats {
            total_original_bytes: 0,
            total_compressed_bytes: 0,
            certificates_compressed: 0,
            dedup_hits: 0,
            nodes_merged: 0,
        }
    }

    /// Record a compression operation.
    pub fn record(&mut self, original: usize, compressed: usize, dedup: usize, merged: usize) {
        self.total_original_bytes += original;
        self.total_compressed_bytes += compressed;
        self.certificates_compressed += 1;
        self.dedup_hits += dedup;
        self.nodes_merged += merged;
    }

    /// Overall compression ratio (0.0 = no savings, 1.0 = fully eliminated).
    /// Returns 0.0 if no data has been compressed.
    pub fn overall_ratio(&self) -> f64 {
        if self.total_original_bytes == 0 {
            return 0.0;
        }
        1.0 - (self.total_compressed_bytes as f64 / self.total_original_bytes as f64)
    }
}

/// Compute the compression ratio for given sizes.
///
/// Returns a value between 0.0 (no savings) and 1.0 (fully eliminated).
/// Returns 0.0 if `original_size` is 0.
pub(crate) fn compression_ratio(original_size: usize, compressed_size: usize) -> f64 {
    if original_size == 0 {
        return 0.0;
    }
    1.0 - (compressed_size as f64 / original_size as f64)
}

/// Compute SHA-256 hash of a byte slice.
fn hash_bytes(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// Compress certificate data using the specified method.
///
/// Serializes the certificate to JSON, then applies the selected compression
/// strategy. The compressed result includes the original hash for integrity
/// verification on decompression.
pub(crate) fn compress_certificate(
    cert: &crate::ProofCertificate,
    method: CompressionMethod,
) -> Result<CompressedCert, CertError> {
    let json = cert.to_json()?;
    let original_bytes = json.as_bytes();
    let original_size = original_bytes.len();
    let original_hash = hash_bytes(original_bytes);

    let compressed_data = match method {
        CompressionMethod::Dedup => dedup_compress(original_bytes),
        CompressionMethod::StructuralSharing => structural_sharing_compress(original_bytes),
        CompressionMethod::DagCompaction => dag_compact_compress(original_bytes),
    };

    Ok(CompressedCert {
        compressed_size: compressed_data.len(),
        data: compressed_data,
        method,
        original_size,
        original_hash,
    })
}

/// Decompress a compressed certificate back to its original form.
///
/// Verifies the SHA-256 hash of the decompressed data against the stored
/// original hash for integrity checking.
pub(crate) fn decompress_certificate(
    compressed: &CompressedCert,
) -> Result<crate::ProofCertificate, CertError> {
    let decompressed = match compressed.method {
        CompressionMethod::Dedup => dedup_decompress(&compressed.data)?,
        CompressionMethod::StructuralSharing => {
            structural_sharing_decompress(&compressed.data)?
        }
        CompressionMethod::DagCompaction => dag_compact_decompress(&compressed.data)?,
    };

    // Integrity check
    let actual_hash = hash_bytes(&decompressed);
    if actual_hash != compressed.original_hash {
        return Err(CertError::VerificationFailed {
            reason: "decompressed data hash does not match original hash".to_string(),
        });
    }

    let json = String::from_utf8(decompressed).map_err(|e| CertError::SerializationFailed {
        reason: format!("decompressed data is not valid UTF-8: {e}"),
    })?;

    crate::ProofCertificate::from_json(&json)
}

/// Deduplicate common subtrees in a collection of proof certificate byte slices.
///
/// Uses hash-consing: each unique chunk is stored once, and duplicates are
/// replaced with references to the canonical copy. Returns a map from
/// hash -> canonical bytes, plus the number of dedup hits.
pub(crate) fn dedup_subtrees(chunks: &[Vec<u8>]) -> (FxHashMap<[u8; 32], Vec<u8>>, usize) {
    let mut store: FxHashMap<[u8; 32], Vec<u8>> = FxHashMap::default();
    let mut hits = 0usize;

    for chunk in chunks {
        let h = hash_bytes(chunk);
        if let std::collections::hash_map::Entry::Vacant(e) = store.entry(h) {
            e.insert(chunk.clone());
        } else {
            hits += 1;
        }
    }

    (store, hits)
}

// ---------------------------------------------------------------------------
// Internal compression strategies
// ---------------------------------------------------------------------------

/// Dedup compression: split input into fixed-size chunks, deduplicate identical
/// chunks, and store a table of unique chunks + a sequence of chunk hashes.
///
/// Wire format:
///   [4 bytes: chunk_size as u32 LE]
///   [4 bytes: num_unique_chunks as u32 LE]
///   [4 bytes: num_chunk_refs as u32 LE]
///   For each unique chunk:
///     [32 bytes: SHA-256 hash]
///     [4 bytes: chunk_len as u32 LE]
///     [chunk_len bytes: chunk data]
///   For each chunk ref in order:
///     [32 bytes: SHA-256 hash referencing a unique chunk]
fn dedup_compress(data: &[u8]) -> Vec<u8> {
    const CHUNK_SIZE: usize = 64;

    let chunks: Vec<&[u8]> = data.chunks(CHUNK_SIZE).collect();
    let mut unique: FxHashMap<[u8; 32], Vec<u8>> = FxHashMap::default();
    let mut refs: Vec<[u8; 32]> = Vec::with_capacity(chunks.len());

    for chunk in &chunks {
        let h = hash_bytes(chunk);
        unique.entry(h).or_insert_with(|| chunk.to_vec());
        refs.push(h);
    }

    let mut out = Vec::new();
    out.extend_from_slice(&(CHUNK_SIZE as u32).to_le_bytes());
    out.extend_from_slice(&(unique.len() as u32).to_le_bytes());
    out.extend_from_slice(&(refs.len() as u32).to_le_bytes());

    // Deterministic ordering for unique chunks
    let mut sorted_unique: Vec<_> = unique.into_iter().collect();
    sorted_unique.sort_by_key(|(h, _)| *h);

    for (h, chunk_data) in &sorted_unique {
        out.extend_from_slice(h);
        out.extend_from_slice(&(chunk_data.len() as u32).to_le_bytes());
        out.extend_from_slice(chunk_data);
    }

    for r in &refs {
        out.extend_from_slice(r);
    }

    out
}

fn dedup_decompress(data: &[u8]) -> Result<Vec<u8>, CertError> {
    if data.len() < 12 {
        return Err(CertError::SerializationFailed {
            reason: "dedup compressed data too short".to_string(),
        });
    }

    let mut pos = 0;
    let _chunk_size = u32::from_le_bytes(
        data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
            reason: "dedup header: invalid chunk_size bytes".to_string(),
        })?,
    ) as usize;
    pos += 4;
    let num_unique = u32::from_le_bytes(
        data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
            reason: "dedup header: invalid num_unique bytes".to_string(),
        })?,
    ) as usize;
    pos += 4;
    let num_refs = u32::from_le_bytes(
        data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
            reason: "dedup header: invalid num_refs bytes".to_string(),
        })?,
    ) as usize;
    pos += 4;

    let mut table: FxHashMap<[u8; 32], Vec<u8>> = FxHashMap::with_capacity_and_hasher(num_unique, Default::default());
    for _ in 0..num_unique {
        if pos + 36 > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "dedup data truncated in unique chunk table".to_string(),
            });
        }
        let h: [u8; 32] = data[pos..pos + 32].try_into().map_err(|_| CertError::SerializationFailed {
            reason: "dedup: invalid hash bytes in unique chunk table".to_string(),
        })?;
        pos += 32;
        let chunk_len = u32::from_le_bytes(
            data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
                reason: "dedup: invalid chunk length bytes".to_string(),
            })?,
        ) as usize;
        pos += 4;
        if pos + chunk_len > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "dedup data truncated in chunk data".to_string(),
            });
        }
        table.insert(h, data[pos..pos + chunk_len].to_vec());
        pos += chunk_len;
    }

    let mut result = Vec::new();
    for _ in 0..num_refs {
        if pos + 32 > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "dedup data truncated in chunk refs".to_string(),
            });
        }
        let h: [u8; 32] = data[pos..pos + 32].try_into().map_err(|_| CertError::SerializationFailed {
            reason: "dedup: invalid hash bytes in chunk refs".to_string(),
        })?;
        pos += 32;
        let chunk_data = table.get(&h).ok_or_else(|| CertError::SerializationFailed {
            reason: "dedup chunk reference not found in table".to_string(),
        })?;
        result.extend_from_slice(chunk_data);
    }

    Ok(result)
}

/// Structural sharing compression: identify repeated JSON string values and
/// replace them with short references. Stores a string table followed by the
/// rewritten data.
///
/// Wire format:
///   [4 bytes: num_entries as u32 LE]
///   For each string table entry:
///     [2 bytes: key_len as u16 LE]
///     [key_len bytes: replacement key]
///     [4 bytes: value_len as u32 LE]
///     [value_len bytes: original string]
///   [remaining bytes: rewritten payload]
fn structural_sharing_compress(data: &[u8]) -> Vec<u8> {
    // Find repeated substrings of length >= 16 that appear 2+ times.
    let text = String::from_utf8_lossy(data);
    let mut freq: FxHashMap<&str, usize> = FxHashMap::default();

    // Scan for quoted JSON strings as candidate shared values.
    let mut candidates: Vec<&str> = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                if bytes[i] == b'\\' {
                    i += 1; // skip escaped char
                }
                i += 1;
            }
            if i < bytes.len() {
                i += 1; // closing quote
                let candidate = &text[start..i];
                if candidate.len() >= 16 {
                    candidates.push(candidate);
                    *freq.entry(candidate).or_default() += 1;
                }
            }
        } else {
            i += 1;
        }
    }

    // Build string table from strings appearing 2+ times, sorted by savings.
    let mut table_entries: Vec<(String, String)> = Vec::new();
    let mut seen = FxHashSet::default();
    let mut key_idx = 0u32;

    let mut repeated: Vec<_> = freq.iter()
        .filter(|&(_, &count)| count >= 2)
        .collect();
    repeated.sort_by(|a, b| {
        let savings_a = a.0.len() * (a.1 - 1);
        let savings_b = b.0.len() * (b.1 - 1);
        savings_b.cmp(&savings_a)
    });

    for &(&s, _) in &repeated {
        if seen.contains(s) {
            continue;
        }
        let key = format!("__S{key_idx}__");
        table_entries.push((key, s.to_string()));
        seen.insert(s);
        key_idx += 1;
    }

    // Rewrite payload, replacing occurrences with keys.
    let mut payload = text.to_string();
    for (key, original) in &table_entries {
        payload = payload.replace(original.as_str(), key);
    }

    // Serialize
    let mut out = Vec::new();
    out.extend_from_slice(&(table_entries.len() as u32).to_le_bytes());
    for (key, value) in &table_entries {
        let key_bytes = key.as_bytes();
        out.extend_from_slice(&(key_bytes.len() as u16).to_le_bytes());
        out.extend_from_slice(key_bytes);
        let val_bytes = value.as_bytes();
        out.extend_from_slice(&(val_bytes.len() as u32).to_le_bytes());
        out.extend_from_slice(val_bytes);
    }
    out.extend_from_slice(payload.as_bytes());

    out
}

fn structural_sharing_decompress(data: &[u8]) -> Result<Vec<u8>, CertError> {
    if data.len() < 4 {
        return Err(CertError::SerializationFailed {
            reason: "structural sharing compressed data too short".to_string(),
        });
    }

    let mut pos = 0;
    let num_entries = u32::from_le_bytes(
        data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
            reason: "structural sharing: invalid entry count bytes".to_string(),
        })?,
    ) as usize;
    pos += 4;

    let mut table: Vec<(String, String)> = Vec::with_capacity(num_entries);
    for _ in 0..num_entries {
        if pos + 2 > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "structural sharing data truncated in string table key".to_string(),
            });
        }
        let key_len = u16::from_le_bytes(
            data[pos..pos + 2].try_into().map_err(|_| CertError::SerializationFailed {
                reason: "structural sharing: invalid key length bytes".to_string(),
            })?,
        ) as usize;
        pos += 2;
        if pos + key_len > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "structural sharing data truncated in key bytes".to_string(),
            });
        }
        let key = String::from_utf8(data[pos..pos + key_len].to_vec()).map_err(|e| {
            CertError::SerializationFailed {
                reason: format!("invalid UTF-8 in string table key: {e}"),
            }
        })?;
        pos += key_len;

        if pos + 4 > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "structural sharing data truncated in value length".to_string(),
            });
        }
        let val_len = u32::from_le_bytes(
            data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
                reason: "structural sharing: invalid value length bytes".to_string(),
            })?,
        ) as usize;
        pos += 4;
        if pos + val_len > data.len() {
            return Err(CertError::SerializationFailed {
                reason: "structural sharing data truncated in value bytes".to_string(),
            });
        }
        let value = String::from_utf8(data[pos..pos + val_len].to_vec()).map_err(|e| {
            CertError::SerializationFailed {
                reason: format!("invalid UTF-8 in string table value: {e}"),
            }
        })?;
        pos += val_len;

        table.push((key, value));
    }

    let mut payload = String::from_utf8(data[pos..].to_vec()).map_err(|e| {
        CertError::SerializationFailed {
            reason: format!("invalid UTF-8 in payload: {e}"),
        }
    })?;

    // Reverse substitution: replace keys back with original values.
    // Process in reverse order to handle any nesting correctly.
    for (key, value) in table.iter().rev() {
        payload = payload.replace(key.as_str(), value);
    }

    Ok(payload.into_bytes())
}

/// DAG compaction: run-length encode repeated byte sequences.
///
/// Wire format:
///   Sequence of segments:
///     [1 byte: tag] 0x00 = literal, 0x01 = run
///     If literal:
///       [4 bytes: length as u32 LE]
///       [length bytes: literal data]
///     If run:
///       [4 bytes: count as u32 LE]
///       [1 byte: repeated byte value]
fn dag_compact_compress(data: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;

    while i < data.len() {
        // Check for a run of repeated bytes (min length 4).
        let b = data[i];
        let mut run_len = 1;
        while i + run_len < data.len() && data[i + run_len] == b && run_len < u32::MAX as usize {
            run_len += 1;
        }

        if run_len >= 4 {
            out.push(0x01);
            out.extend_from_slice(&(run_len as u32).to_le_bytes());
            out.push(b);
            i += run_len;
        } else {
            // Collect literal bytes until we hit a run of 4+.
            let lit_start = i;
            while i < data.len() {
                let b2 = data[i];
                let mut ahead = 1;
                while i + ahead < data.len() && data[i + ahead] == b2 {
                    ahead += 1;
                }
                if ahead >= 4 {
                    break;
                }
                i += 1;
            }
            let lit_data = &data[lit_start..i];
            out.push(0x00);
            out.extend_from_slice(&(lit_data.len() as u32).to_le_bytes());
            out.extend_from_slice(lit_data);
        }
    }

    out
}

fn dag_compact_decompress(data: &[u8]) -> Result<Vec<u8>, CertError> {
    let mut result = Vec::new();
    let mut pos = 0;

    while pos < data.len() {
        let tag = data[pos];
        pos += 1;

        match tag {
            0x00 => {
                // Literal
                if pos + 4 > data.len() {
                    return Err(CertError::SerializationFailed {
                        reason: "dag compact data truncated in literal length".to_string(),
                    });
                }
                let len = u32::from_le_bytes(
                    data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
                        reason: "dag compact: invalid literal length bytes".to_string(),
                    })?,
                ) as usize;
                pos += 4;
                if pos + len > data.len() {
                    return Err(CertError::SerializationFailed {
                        reason: "dag compact data truncated in literal data".to_string(),
                    });
                }
                result.extend_from_slice(&data[pos..pos + len]);
                pos += len;
            }
            0x01 => {
                // Run
                if pos + 5 > data.len() {
                    return Err(CertError::SerializationFailed {
                        reason: "dag compact data truncated in run segment".to_string(),
                    });
                }
                let count = u32::from_le_bytes(
                    data[pos..pos + 4].try_into().map_err(|_| CertError::SerializationFailed {
                        reason: "dag compact: invalid run count bytes".to_string(),
                    })?,
                ) as usize;
                pos += 4;
                let byte_val = data[pos];
                pos += 1;
                result.resize(result.len() + count, byte_val);
            }
            other => {
                return Err(CertError::SerializationFailed {
                    reason: format!("dag compact: unknown segment tag {other:#x}"),
                });
            }
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::{FunctionHash, ProofCertificate, SolverInfo, VcSnapshot};

    fn sample_solver_info() -> SolverInfo {
        SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "must hold".to_string() },
            function: function.to_string(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn sample_certificate(function: &str, timestamp: &str) -> ProofCertificate {
        let vc_snapshot =
            VcSnapshot::from_vc(&sample_vc(function)).expect("snapshot should serialize");
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            vc_snapshot,
            sample_solver_info(),
            vec![1, 2, 3, 4],
            timestamp.to_string(),
        )
    }

    // -------------------------------------------------------------------
    // Compression ratio
    // -------------------------------------------------------------------

    #[test]
    fn test_compression_ratio_basic() {
        assert!((compression_ratio(100, 50) - 0.5).abs() < f64::EPSILON);
        assert!((compression_ratio(100, 100) - 0.0).abs() < f64::EPSILON);
        assert!((compression_ratio(100, 0) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_compression_ratio_zero_original() {
        assert!((compression_ratio(0, 0) - 0.0).abs() < f64::EPSILON);
        assert!((compression_ratio(0, 10) - 0.0).abs() < f64::EPSILON);
    }

    // -------------------------------------------------------------------
    // Dedup compress/decompress roundtrip
    // -------------------------------------------------------------------

    #[test]
    fn test_dedup_roundtrip() {
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let compressed =
            compress_certificate(&cert, CompressionMethod::Dedup).expect("dedup compress");
        assert_eq!(compressed.method, CompressionMethod::Dedup);
        assert!(compressed.original_size > 0);

        let restored = decompress_certificate(&compressed).expect("dedup decompress");
        assert_eq!(restored, cert);
    }

    // -------------------------------------------------------------------
    // Structural sharing compress/decompress roundtrip
    // -------------------------------------------------------------------

    #[test]
    fn test_structural_sharing_roundtrip() {
        let cert = sample_certificate("crate::bar", "2026-03-27T13:00:00Z");
        let compressed = compress_certificate(&cert, CompressionMethod::StructuralSharing)
            .expect("structural sharing compress");
        assert_eq!(compressed.method, CompressionMethod::StructuralSharing);

        let restored = decompress_certificate(&compressed).expect("structural sharing decompress");
        assert_eq!(restored, cert);
    }

    // -------------------------------------------------------------------
    // DAG compaction compress/decompress roundtrip
    // -------------------------------------------------------------------

    #[test]
    fn test_dag_compaction_roundtrip() {
        let cert = sample_certificate("crate::baz", "2026-03-27T14:00:00Z");
        let compressed = compress_certificate(&cert, CompressionMethod::DagCompaction)
            .expect("dag compaction compress");
        assert_eq!(compressed.method, CompressionMethod::DagCompaction);

        let restored = decompress_certificate(&compressed).expect("dag compaction decompress");
        assert_eq!(restored, cert);
    }

    // -------------------------------------------------------------------
    // Compressed metadata
    // -------------------------------------------------------------------

    #[test]
    fn test_compressed_cert_metadata() {
        let cert = sample_certificate("crate::meta", "2026-03-27T15:00:00Z");
        let compressed =
            compress_certificate(&cert, CompressionMethod::Dedup).expect("compress");

        assert_eq!(compressed.original_size, cert.to_json().unwrap().len());
        assert!(compressed.compressed_size > 0);
        assert_eq!(compressed.data.len(), compressed.compressed_size);
    }

    // -------------------------------------------------------------------
    // Integrity check on tampered data
    // -------------------------------------------------------------------

    #[test]
    fn test_decompress_detects_tampered_hash() {
        let cert = sample_certificate("crate::tamper", "2026-03-27T16:00:00Z");
        let mut compressed =
            compress_certificate(&cert, CompressionMethod::DagCompaction).expect("compress");

        // Tamper with the original hash
        compressed.original_hash[0] ^= 0xFF;

        let result = decompress_certificate(&compressed);
        assert!(result.is_err());
        match result.unwrap_err() {
            CertError::VerificationFailed { reason } => {
                assert!(reason.contains("hash does not match"));
            }
            other => panic!("expected VerificationFailed, got: {other:?}"),
        }
    }

    // -------------------------------------------------------------------
    // dedup_subtrees
    // -------------------------------------------------------------------

    #[test]
    fn test_dedup_subtrees_finds_duplicates() {
        let a = vec![1, 2, 3];
        let b = vec![4, 5, 6];
        let c = vec![1, 2, 3]; // duplicate of a
        let d = vec![4, 5, 6]; // duplicate of b

        let (store, hits) = dedup_subtrees(&[a, b, c, d]);
        assert_eq!(store.len(), 2); // two unique chunks
        assert_eq!(hits, 2); // two duplicates found
    }

    #[test]
    fn test_dedup_subtrees_no_duplicates() {
        let a = vec![1];
        let b = vec![2];
        let c = vec![3];

        let (store, hits) = dedup_subtrees(&[a, b, c]);
        assert_eq!(store.len(), 3);
        assert_eq!(hits, 0);
    }

    // -------------------------------------------------------------------
    // CompressionStats
    // -------------------------------------------------------------------

    #[test]
    fn test_compression_stats_tracking() {
        let mut stats = CompressionStats::new();
        assert_eq!(stats.certificates_compressed, 0);
        assert!((stats.overall_ratio() - 0.0).abs() < f64::EPSILON);

        stats.record(1000, 500, 3, 2);
        assert_eq!(stats.certificates_compressed, 1);
        assert_eq!(stats.total_original_bytes, 1000);
        assert_eq!(stats.total_compressed_bytes, 500);
        assert_eq!(stats.dedup_hits, 3);
        assert_eq!(stats.nodes_merged, 2);
        assert!((stats.overall_ratio() - 0.5).abs() < f64::EPSILON);

        stats.record(1000, 250, 1, 0);
        assert_eq!(stats.certificates_compressed, 2);
        assert_eq!(stats.total_original_bytes, 2000);
        assert_eq!(stats.total_compressed_bytes, 750);
        assert!((stats.overall_ratio() - 0.625).abs() < f64::EPSILON);
    }

    // -------------------------------------------------------------------
    // All methods produce valid CompressedCert
    // -------------------------------------------------------------------

    #[test]
    fn test_all_methods_produce_valid_compressed_cert() {
        let cert = sample_certificate("crate::all_methods", "2026-03-27T17:00:00Z");
        let methods = [
            CompressionMethod::Dedup,
            CompressionMethod::StructuralSharing,
            CompressionMethod::DagCompaction,
        ];

        for method in &methods {
            let compressed =
                compress_certificate(&cert, *method).expect("compression should succeed");
            assert!(compressed.original_size > 0, "method {method:?}: original_size must be > 0");
            assert!(compressed.compressed_size > 0, "method {method:?}: compressed_size must be > 0");

            let restored =
                decompress_certificate(&compressed).expect("decompression should succeed");
            assert_eq!(restored, cert, "method {method:?}: roundtrip failed");
        }
    }

    // -------------------------------------------------------------------
    // Dedup with repetitive proof trace
    // -------------------------------------------------------------------

    #[test]
    fn test_dedup_with_repetitive_data() {
        // Create a certificate with a large repetitive proof trace to exercise dedup.
        let vc_snapshot = VcSnapshot::from_vc(&sample_vc("crate::rep"))
            .expect("snapshot should serialize");
        let mut cert = ProofCertificate::new_trusted(
            "crate::rep".to_string(),
            FunctionHash::from_bytes(b"crate::rep-body"),
            vc_snapshot,
            sample_solver_info(),
            // 256 bytes of repeating pattern
            (0..256).map(|i| (i % 4) as u8).collect(),
            "2026-03-27T18:00:00Z".to_string(),
        );
        cert.proof_steps = vec![
            crate::ProofStep {
                index: 0,
                rule: "resolution".to_string(),
                description: "initial clause".to_string(),
                premises: vec![],
            },
            crate::ProofStep {
                index: 1,
                rule: "resolution".to_string(),
                description: "derived clause".to_string(),
                premises: vec![0],
            },
        ];

        let compressed =
            compress_certificate(&cert, CompressionMethod::Dedup).expect("compress");
        let restored = decompress_certificate(&compressed).expect("decompress");
        assert_eq!(restored, cert);
    }
}
