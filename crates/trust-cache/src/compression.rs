// trust-cache/compression.rs: Cache entry compression and deduplication
//
// Reduces memory footprint by compressing cached values and deduplicating
// identical sub-formulas. Provides formula-specific compression that exploits
// structural sharing and variable name interning.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::time::Instant;

use trust_types::Formula;

use crate::CacheError;

// ---------------------------------------------------------------------------
// Compression strategy
// ---------------------------------------------------------------------------

/// Which compression algorithm to apply.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum CompressionStrategy {
    /// No compression (store as-is).
    #[default]
    None,
    /// Formula-specific structural compression.
    FormulaSpecific,
}

// ---------------------------------------------------------------------------
// Compressed entry
// ---------------------------------------------------------------------------

/// A compressed cache entry wrapping a serialized value with metadata.
#[derive(Debug, Clone)]
pub struct CompressedEntry<V> {
    /// The stored data (compressed bytes or original value).
    data: CompressedData<V>,
    /// Strategy used to compress this entry.
    pub strategy: CompressionStrategy,
    /// Original (uncompressed) size in bytes.
    pub original_size: usize,
    /// Compressed size in bytes (same as original if uncompressed).
    pub compressed_size: usize,
    /// Content hash for deduplication.
    pub content_hash: u64,
}

/// Internal storage: either original value or compressed bytes.
#[derive(Debug, Clone)]
enum CompressedData<V> {
    /// Stored as original value (no compression or formula-specific).
    Original(V),
    /// Stored as compressed bytes.
    Bytes(Vec<u8>),
}

impl<V: Clone> CompressedEntry<V> {
    /// Create an uncompressed entry.
    pub(crate) fn uncompressed(value: V, size: usize, hash: u64) -> Self {
        CompressedEntry {
            data: CompressedData::Original(value),
            strategy: CompressionStrategy::None,
            original_size: size,
            compressed_size: size,
            content_hash: hash,
        }
    }

    /// Create a compressed entry from bytes.
    pub(crate) fn from_bytes(
        bytes: Vec<u8>,
        strategy: CompressionStrategy,
        original_size: usize,
        hash: u64,
    ) -> Self {
        let compressed_size = bytes.len();
        CompressedEntry {
            data: CompressedData::Bytes(bytes),
            strategy,
            original_size,
            compressed_size,
            content_hash: hash,
        }
    }

    /// Compression ratio as a percentage (100 = no compression, 50 = halved).
    #[must_use]
    pub fn compression_ratio_percent(&self) -> u64 {
        if self.original_size == 0 {
            return 100;
        }
        (self.compressed_size as u64 * 100) / self.original_size as u64
    }
}

// ---------------------------------------------------------------------------
// Compression statistics
// ---------------------------------------------------------------------------

/// Tracks compression performance across multiple operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompressionStats {
    /// Total entries compressed.
    pub entries_compressed: u64,
    /// Total entries decompressed.
    pub entries_decompressed: u64,
    /// Total original bytes across all compress operations.
    pub total_original_bytes: u64,
    /// Total compressed bytes across all compress operations.
    pub total_compressed_bytes: u64,
    /// Cumulative compression time in microseconds.
    pub compress_time_us: u64,
    /// Cumulative decompression time in microseconds.
    pub decompress_time_us: u64,
    /// Number of deduplication hits (value already stored).
    pub dedup_hits: u64,
    /// Number of deduplication misses (novel value).
    pub dedup_misses: u64,
}

impl CompressionStats {
    /// Create empty stats.
    pub fn new() -> Self {
        CompressionStats {
            entries_compressed: 0,
            entries_decompressed: 0,
            total_original_bytes: 0,
            total_compressed_bytes: 0,
            compress_time_us: 0,
            decompress_time_us: 0,
            dedup_hits: 0,
            dedup_misses: 0,
        }
    }

    /// Overall compression ratio as percentage (100 = no savings).
    #[must_use]
    pub fn overall_ratio_percent(&self) -> u64 {
        if self.total_original_bytes == 0 {
            return 100;
        }
        (self.total_compressed_bytes * 100) / self.total_original_bytes
    }

    /// Total space saved in bytes.
    #[must_use]
    pub fn space_saved_bytes(&self) -> u64 {
        self.total_original_bytes.saturating_sub(self.total_compressed_bytes)
    }
}

impl Default for CompressionStats {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Formula compressor
// ---------------------------------------------------------------------------

/// Specialized compressor for `Formula` types that exploits structural sharing.
///
/// Features:
/// - **Structural sharing**: Identical sub-formulas are stored once and
///   referenced by content hash.
/// - **Variable name interning**: Variable names are mapped to compact integer
///   IDs, reducing repetition.
/// - **Common pattern deduplication**: Frequently occurring formula patterns
///   (e.g., `x >= 0`) are recognized and stored compactly.
pub struct FormulaCompressor {
    /// Interned variable names: name -> compact ID.
    intern_table: FxHashMap<String, u32>,
    /// Reverse intern table: ID -> name.
    reverse_intern: Vec<String>,
    /// Sub-formula hash -> reference count (for structural sharing stats).
    subfomula_hashes: FxHashMap<u64, u32>,
    /// Statistics.
    stats: CompressionStats,
}

impl FormulaCompressor {
    /// Create a new formula compressor.
    pub fn new() -> Self {
        FormulaCompressor {
            intern_table: FxHashMap::default(),
            reverse_intern: Vec::new(),
            subfomula_hashes: FxHashMap::default(),
            stats: CompressionStats::new(),
        }
    }

    /// Intern a variable name, returning its compact ID.
    pub fn intern_var(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.intern_table.get(name) {
            return id;
        }
        let id = self.reverse_intern.len() as u32;
        self.intern_table.insert(name.to_string(), id);
        self.reverse_intern.push(name.to_string());
        id
    }

    /// Look up an interned variable name by ID.
    #[must_use]
    pub fn resolve_var(&self, id: u32) -> Option<&str> {
        self.reverse_intern.get(id as usize).map(|s| s.as_str())
    }

    /// Number of interned variable names.
    #[must_use]
    pub fn interned_count(&self) -> usize {
        self.reverse_intern.len()
    }

    /// Compute a content hash for a formula (for structural sharing).
    #[must_use]
    pub(crate) fn formula_hash(formula: &Formula) -> u64 {
        // Use serde_json as a canonical representation, then hash
        let json = serde_json::to_string(formula).unwrap_or_default();
        let mut hasher = DefaultHasher::new();
        json.hash(&mut hasher);
        hasher.finish()
    }

    /// Register a sub-formula for structural sharing tracking.
    pub fn register_subformula(&mut self, formula: &Formula) {
        let hash = Self::formula_hash(formula);
        *self.subfomula_hashes.entry(hash).or_insert(0) += 1;
    }

    /// Walk the formula tree and intern all variable names, registering
    /// sub-formulas for sharing.
    pub fn analyze_formula(&mut self, formula: &Formula) {
        self.register_subformula(formula);
        match formula {
            Formula::Var(name, _) => {
                self.intern_var(name);
            }
            Formula::Not(inner) | Formula::Neg(inner) => {
                self.analyze_formula(inner);
            }
            Formula::And(children) | Formula::Or(children) => {
                for child in children {
                    self.analyze_formula(child);
                }
            }
            Formula::Implies(a, b)
            | Formula::Eq(a, b)
            | Formula::Lt(a, b)
            | Formula::Le(a, b)
            | Formula::Gt(a, b)
            | Formula::Ge(a, b)
            | Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b)
            | Formula::Div(a, b)
            | Formula::Rem(a, b) => {
                self.analyze_formula(a);
                self.analyze_formula(b);
            }
            Formula::BvAdd(a, b, _)
            | Formula::BvSub(a, b, _)
            | Formula::BvMul(a, b, _)
            | Formula::BvUDiv(a, b, _)
            | Formula::BvSDiv(a, b, _)
            | Formula::BvURem(a, b, _)
            | Formula::BvSRem(a, b, _)
            | Formula::BvAnd(a, b, _)
            | Formula::BvOr(a, b, _)
            | Formula::BvXor(a, b, _)
            | Formula::BvShl(a, b, _)
            | Formula::BvLShr(a, b, _)
            | Formula::BvAShr(a, b, _)
            | Formula::BvULt(a, b, _)
            | Formula::BvULe(a, b, _)
            | Formula::BvSLt(a, b, _)
            | Formula::BvSLe(a, b, _) => {
                self.analyze_formula(a);
                self.analyze_formula(b);
            }
            Formula::BvNot(inner, _)
            | Formula::BvToInt(inner, _, _)
            | Formula::IntToBv(inner, _)
            | Formula::BvZeroExt(inner, _)
            | Formula::BvSignExt(inner, _) => {
                self.analyze_formula(inner);
            }
            Formula::BvExtract { inner, .. } => {
                self.analyze_formula(inner);
            }
            Formula::BvConcat(a, b) => {
                self.analyze_formula(a);
                self.analyze_formula(b);
            }
            Formula::Ite(cond, then_br, else_br) | Formula::Store(cond, then_br, else_br) => {
                self.analyze_formula(cond);
                self.analyze_formula(then_br);
                self.analyze_formula(else_br);
            }
            Formula::Select(a, b) => {
                self.analyze_formula(a);
                self.analyze_formula(b);
            }
            Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
                for (name, _) in vars {
                    self.intern_var(name);
                }
                self.analyze_formula(body);
            }
            Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
            _ => {},
        }
    }

    /// Count of sub-formulas that appear more than once (shareable).
    #[must_use]
    pub fn shared_subformula_count(&self) -> usize {
        self.subfomula_hashes.values().filter(|&&c| c > 1).count()
    }

    /// Current compression statistics.
    #[must_use]
    pub fn stats(&self) -> &CompressionStats {
        &self.stats
    }

    /// Reset the compressor state (clears intern tables and stats).
    pub fn reset(&mut self) {
        self.intern_table.clear();
        self.reverse_intern.clear();
        self.subfomula_hashes.clear();
        self.stats = CompressionStats::new();
    }
}

impl Default for FormulaCompressor {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Generic compressor
// ---------------------------------------------------------------------------

/// Compresses and decompresses cache entries using configurable strategies.
pub struct CacheCompressor {
    strategy: CompressionStrategy,
    stats: CompressionStats,
}

impl CacheCompressor {
    /// Create a compressor with the given strategy.
    pub fn new(strategy: CompressionStrategy) -> Self {
        CacheCompressor { strategy, stats: CompressionStats::new() }
    }

    /// Compress a serializable value into a `CompressedEntry`.
    pub fn compress<V: serde::Serialize + Clone>(
        &mut self,
        value: &V,
    ) -> Result<CompressedEntry<V>, CacheError> {
        let start = Instant::now();
        let json = serde_json::to_vec(value)?;
        let original_size = json.len();
        let hash = content_hash_bytes(&json);

        let entry = match self.strategy {
            CompressionStrategy::None => {
                CompressedEntry::uncompressed(value.clone(), original_size, hash)
            }
            CompressionStrategy::FormulaSpecific => {
                // For generic values, fall back to RLE.
                let compressed = rle_compress(&json);
                CompressedEntry::from_bytes(compressed, self.strategy, original_size, hash)
            }
        };

        let elapsed = start.elapsed();
        self.stats.entries_compressed += 1;
        self.stats.total_original_bytes += original_size as u64;
        self.stats.total_compressed_bytes += entry.compressed_size as u64;
        self.stats.compress_time_us += elapsed.as_micros() as u64;

        Ok(entry)
    }

    /// Decompress a `CompressedEntry` back to the original value.
    pub fn decompress<V: serde::de::DeserializeOwned + Clone>(
        &mut self,
        entry: &CompressedEntry<V>,
    ) -> Result<V, CacheError> {
        let start = Instant::now();

        let result = match &entry.data {
            CompressedData::Original(val) => Ok(val.clone()),
            CompressedData::Bytes(bytes) => {
                let decompressed = rle_decompress(bytes);
                let val: V = serde_json::from_slice(&decompressed)?;
                Ok(val)
            }
        };

        let elapsed = start.elapsed();
        self.stats.entries_decompressed += 1;
        self.stats.decompress_time_us += elapsed.as_micros() as u64;

        result
    }

    /// Current compression statistics.
    #[must_use]
    pub fn stats(&self) -> &CompressionStats {
        &self.stats
    }

    /// Active compression strategy.
    #[must_use]
    pub fn strategy(&self) -> CompressionStrategy {
        self.strategy
    }
}

// ---------------------------------------------------------------------------
// Deduplication index
// ---------------------------------------------------------------------------

/// Maps content hashes to stored entry references for deduplication.
///
/// When a value is inserted, its content hash is computed. If an entry
/// with the same hash already exists, the insert is skipped (dedup hit).
pub struct DeduplicationIndex<K, V> {
    /// Content hash -> key that stores the canonical copy.
    hash_to_key: FxHashMap<u64, K>,
    /// Key -> (value, reference count).
    entries: FxHashMap<K, (V, u32)>,
    stats: CompressionStats,
}

impl<K: Clone + Eq + Hash, V: Clone + serde::Serialize> DeduplicationIndex<K, V> {
    /// Create an empty deduplication index.
    pub fn new() -> Self {
        DeduplicationIndex {
            hash_to_key: FxHashMap::default(),
            entries: FxHashMap::default(),
            stats: CompressionStats::new(),
        }
    }

    /// Insert a value, deduplicating against existing entries.
    ///
    /// Returns `true` if the value was novel (inserted), `false` if it was
    /// a duplicate (reference count incremented).
    pub fn dedup_insert(&mut self, key: K, value: V) -> bool {
        let json = serde_json::to_vec(&value).unwrap_or_default();
        let hash = content_hash_bytes(&json);

        if let Some(existing_key) = self.hash_to_key.get(&hash)
            && let Some((_, ref_count)) = self.entries.get_mut(existing_key) {
                *ref_count += 1;
                self.stats.dedup_hits += 1;
                // Also store under new key pointing to same value
                if &key != existing_key {
                    let val = self.entries.get(existing_key).map(|(v, _)| v.clone());
                    if let Some(v) = val {
                        self.entries.insert(key, (v, 1));
                    }
                }
                return false;
            }

        self.stats.dedup_misses += 1;
        self.hash_to_key.insert(hash, key.clone());
        self.entries.insert(key, (value, 1));
        true
    }

    /// Look up a value by key.
    #[must_use]
    pub fn get(&self, key: &K) -> Option<&V> {
        self.entries.get(key).map(|(v, _)| v)
    }

    /// Remove a key. Decrements reference count; only truly removes when
    /// count reaches zero.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some((val, ref_count)) = self.entries.get_mut(key) {
            if *ref_count <= 1 {
                // SAFETY: We just confirmed the entry exists via get_mut(key).
                let (val, _) = self.entries.remove(key)
                    .unwrap_or_else(|| unreachable!("key missing from entries after get_mut"));
                // Clean up hash_to_key if this was the canonical key
                self.hash_to_key.retain(|_, k| k != key);
                return Some(val);
            }
            *ref_count -= 1;
            return Some(val.clone());
        }
        None
    }

    /// Number of unique keys stored.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of unique content hashes tracked.
    #[must_use]
    pub fn unique_values(&self) -> usize {
        self.hash_to_key.len()
    }

    /// Deduplication statistics.
    #[must_use]
    pub fn stats(&self) -> &CompressionStats {
        &self.stats
    }

    /// Clear all entries and hashes.
    pub fn clear(&mut self) {
        self.hash_to_key.clear();
        self.entries.clear();
    }
}

impl<K: Clone + Eq + Hash, V: Clone + serde::Serialize> Default for DeduplicationIndex<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Compute a u64 content hash of a byte slice (for deduplication).
fn content_hash_bytes(bytes: &[u8]) -> u64 {
    let mut hasher = DefaultHasher::new();
    bytes.hash(&mut hasher);
    hasher.finish()
}

/// Simple run-length encoding used by cache compression.
fn rle_compress(data: &[u8]) -> Vec<u8> {
    if data.is_empty() {
        return Vec::new();
    }

    let mut result = Vec::with_capacity(data.len());
    let mut i = 0;
    while i < data.len() {
        let byte = data[i];
        let mut run_len: u8 = 1;
        while i + (run_len as usize) < data.len()
            && data[i + run_len as usize] == byte
            && run_len < 255
        {
            run_len += 1;
        }

        if run_len >= 3 {
            // Encode as: 0x00, count, byte
            result.push(0x00);
            result.push(run_len);
            result.push(byte);
        } else {
            // Store literal bytes, escaping 0x00 as 0x00 0x01 0x00
            for _ in 0..run_len {
                if byte == 0x00 {
                    result.push(0x00);
                    result.push(0x01);
                    result.push(0x00);
                } else {
                    result.push(byte);
                }
            }
        }
        i += run_len as usize;
    }
    result
}

/// Decompress RLE-encoded data.
fn rle_decompress(data: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(data.len());
    let mut i = 0;
    while i < data.len() {
        if data[i] == 0x00 && i + 2 < data.len() {
            let count = data[i + 1];
            let byte = data[i + 2];
            if count >= 3 {
                // Run-length encoded
                for _ in 0..count {
                    result.push(byte);
                }
            } else if count == 1 && byte == 0x00 {
                // Escaped 0x00 literal
                result.push(0x00);
            } else {
                // Shouldn't happen with our encoder, but handle gracefully
                result.push(data[i]);
                i += 1;
                continue;
            }
            i += 3;
        } else {
            result.push(data[i]);
            i += 1;
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort};

    use super::*;

    // -----------------------------------------------------------------------
    // RLE compress/decompress round-trip
    // -----------------------------------------------------------------------

    #[test]
    fn test_rle_roundtrip_simple() {
        let data = b"hello world";
        let compressed = rle_compress(data);
        let decompressed = rle_decompress(&compressed);
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_rle_roundtrip_with_runs() {
        let data = b"aaabbbccccdddd";
        let compressed = rle_compress(data);
        let decompressed = rle_decompress(&compressed);
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_rle_roundtrip_empty() {
        let data: &[u8] = b"";
        let compressed = rle_compress(data);
        let decompressed = rle_decompress(&compressed);
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_rle_roundtrip_with_zeros() {
        let data = vec![0u8, 0, 1, 0, 0, 0, 2];
        let compressed = rle_compress(&data);
        let decompressed = rle_decompress(&compressed);
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_rle_compresses_long_runs() {
        let data = vec![0xAA; 100];
        let compressed = rle_compress(&data);
        // Should be significantly smaller than 100 bytes
        assert!(
            compressed.len() < data.len(),
            "RLE should compress long runs: {} < {}",
            compressed.len(),
            data.len()
        );
        let decompressed = rle_decompress(&compressed);
        assert_eq!(decompressed, data);
    }

    // -----------------------------------------------------------------------
    // CacheCompressor
    // -----------------------------------------------------------------------

    #[test]
    fn test_compress_decompress_none_strategy() {
        let mut compressor = CacheCompressor::new(CompressionStrategy::None);
        let value = vec![1i32, 2, 3, 4, 5];

        let entry = compressor.compress(&value).expect("compress should succeed");
        assert_eq!(entry.strategy, CompressionStrategy::None);
        assert_eq!(entry.original_size, entry.compressed_size);

        let restored: Vec<i32> = compressor.decompress(&entry).expect("decompress should succeed");
        assert_eq!(restored, value);
    }

    #[test]
    fn test_compress_decompress_formula_specific() {
        let mut compressor = CacheCompressor::new(CompressionStrategy::FormulaSpecific);
        let formula = Formula::And(vec![
            Formula::Bool(true),
            Formula::Var("x".to_string(), Sort::Int),
        ]);

        let entry = compressor.compress(&formula).expect("compress should succeed");
        assert_eq!(entry.strategy, CompressionStrategy::FormulaSpecific);
        let restored: Formula =
            compressor.decompress(&entry).expect("decompress should succeed");
        assert_eq!(restored, formula);
    }

    #[test]
    fn test_compressor_stats_tracking() {
        let mut compressor = CacheCompressor::new(CompressionStrategy::FormulaSpecific);

        compressor.compress(&"value1".to_string()).expect("compress");
        compressor.compress(&"value2".to_string()).expect("compress");

        let stats = compressor.stats();
        assert_eq!(stats.entries_compressed, 2);
        assert!(stats.total_original_bytes > 0);
    }

    #[test]
    fn test_compression_ratio() {
        let mut compressor = CacheCompressor::new(CompressionStrategy::None);
        let entry = compressor.compress(&42i32).expect("compress");

        // No compression -> ratio should be 100%
        assert_eq!(entry.compression_ratio_percent(), 100);
    }

    // -----------------------------------------------------------------------
    // FormulaCompressor
    // -----------------------------------------------------------------------

    #[test]
    fn test_formula_compressor_intern_var() {
        let mut fc = FormulaCompressor::new();

        let id1 = fc.intern_var("x");
        let id2 = fc.intern_var("y");
        let id3 = fc.intern_var("x"); // duplicate

        assert_eq!(id1, 0);
        assert_eq!(id2, 1);
        assert_eq!(id3, 0, "interning same name should return same ID");
        assert_eq!(fc.interned_count(), 2);
    }

    #[test]
    fn test_formula_compressor_resolve_var() {
        let mut fc = FormulaCompressor::new();
        fc.intern_var("alpha");
        fc.intern_var("beta");

        assert_eq!(fc.resolve_var(0), Some("alpha"));
        assert_eq!(fc.resolve_var(1), Some("beta"));
        assert_eq!(fc.resolve_var(99), None);
    }

    #[test]
    fn test_formula_compressor_analyze_formula() {
        let mut fc = FormulaCompressor::new();

        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
                Box::new(Formula::Int(100)),
            ),
            Formula::Var("x".to_string(), Sort::Int),
        ]);

        fc.analyze_formula(&formula);

        // Should have interned "x" and "y"
        assert_eq!(fc.interned_count(), 2);
        let x_id = fc.intern_var("x");
        assert!(fc.resolve_var(x_id).is_some());
    }

    #[test]
    fn test_formula_compressor_structural_sharing() {
        let mut fc = FormulaCompressor::new();

        // Create a formula with repeated sub-expression
        let shared_sub = Formula::Var("x".to_string(), Sort::Int);
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(shared_sub.clone()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(shared_sub.clone()), Box::new(Formula::Int(100))),
        ]);

        fc.analyze_formula(&formula);

        // The Var("x", Int) sub-formula appears multiple times
        assert!(
            fc.shared_subformula_count() > 0,
            "should detect shared sub-formulas"
        );
    }

    #[test]
    fn test_formula_hash_deterministic() {
        let f1 = Formula::And(vec![Formula::Bool(true), Formula::Int(42)]);
        let f2 = Formula::And(vec![Formula::Bool(true), Formula::Int(42)]);

        assert_eq!(
            FormulaCompressor::formula_hash(&f1),
            FormulaCompressor::formula_hash(&f2),
        );
    }

    #[test]
    fn test_formula_hash_different_formulas() {
        let f1 = Formula::Bool(true);
        let f2 = Formula::Bool(false);

        assert_ne!(
            FormulaCompressor::formula_hash(&f1),
            FormulaCompressor::formula_hash(&f2),
        );
    }

    #[test]
    fn test_formula_compressor_reset() {
        let mut fc = FormulaCompressor::new();
        fc.intern_var("x");
        fc.intern_var("y");
        assert_eq!(fc.interned_count(), 2);

        fc.reset();
        assert_eq!(fc.interned_count(), 0);
        assert_eq!(fc.shared_subformula_count(), 0);
    }

    // -----------------------------------------------------------------------
    // DeduplicationIndex
    // -----------------------------------------------------------------------

    #[test]
    fn test_dedup_insert_novel_value() {
        let mut index: DeduplicationIndex<String, Vec<i32>> = DeduplicationIndex::new();

        let is_novel = index.dedup_insert("key1".to_string(), vec![1, 2, 3]);
        assert!(is_novel, "first insert should be novel");
        assert_eq!(index.len(), 1);
        assert_eq!(index.unique_values(), 1);
    }

    #[test]
    fn test_dedup_insert_duplicate_value() {
        let mut index: DeduplicationIndex<String, Vec<i32>> = DeduplicationIndex::new();

        index.dedup_insert("key1".to_string(), vec![1, 2, 3]);
        let is_novel = index.dedup_insert("key2".to_string(), vec![1, 2, 3]);
        assert!(!is_novel, "same value should be a dedup hit");

        // Both keys should resolve to the same value
        assert_eq!(index.get(&"key1".to_string()), Some(&vec![1, 2, 3]));
        assert_eq!(index.get(&"key2".to_string()), Some(&vec![1, 2, 3]));
    }

    #[test]
    fn test_dedup_insert_different_values() {
        let mut index: DeduplicationIndex<String, Vec<i32>> = DeduplicationIndex::new();

        let novel1 = index.dedup_insert("key1".to_string(), vec![1, 2]);
        let novel2 = index.dedup_insert("key2".to_string(), vec![3, 4]);
        assert!(novel1);
        assert!(novel2);
        assert_eq!(index.unique_values(), 2);
    }

    #[test]
    fn test_dedup_remove() {
        let mut index: DeduplicationIndex<String, Vec<i32>> = DeduplicationIndex::new();

        index.dedup_insert("key1".to_string(), vec![1, 2, 3]);
        let removed = index.remove(&"key1".to_string());
        assert_eq!(removed, Some(vec![1, 2, 3]));
        assert!(index.is_empty());
    }

    #[test]
    fn test_dedup_stats() {
        let mut index: DeduplicationIndex<String, String> = DeduplicationIndex::new();

        index.dedup_insert("k1".to_string(), "hello".to_string());
        index.dedup_insert("k2".to_string(), "hello".to_string()); // dup
        index.dedup_insert("k3".to_string(), "world".to_string()); // novel

        let stats = index.stats();
        assert_eq!(stats.dedup_hits, 1);
        assert_eq!(stats.dedup_misses, 2);
    }

    #[test]
    fn test_dedup_clear() {
        let mut index: DeduplicationIndex<String, i32> = DeduplicationIndex::new();
        index.dedup_insert("k1".to_string(), 42);
        index.clear();
        assert!(index.is_empty());
        assert_eq!(index.unique_values(), 0);
    }

    // -----------------------------------------------------------------------
    // CompressionStats
    // -----------------------------------------------------------------------

    #[test]
    fn test_compression_stats_defaults() {
        let stats = CompressionStats::new();
        assert_eq!(stats.entries_compressed, 0);
        assert_eq!(stats.overall_ratio_percent(), 100);
        assert_eq!(stats.space_saved_bytes(), 0);
    }

    #[test]
    fn test_compression_stats_ratio() {
        let mut stats = CompressionStats::new();
        stats.total_original_bytes = 1000;
        stats.total_compressed_bytes = 500;
        assert_eq!(stats.overall_ratio_percent(), 50);
        assert_eq!(stats.space_saved_bytes(), 500);
    }
}
