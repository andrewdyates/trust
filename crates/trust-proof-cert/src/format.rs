//! Binary serialization for proof certificates.
//!
//! Uses bincode for deterministic, compact binary encoding.
//! Same input always produces the same bytes.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{CertError, ProofCertificate};

/// Magic bytes identifying a tRust proof certificate binary file.
const MAGIC: &[u8; 4] = b"tRPC";

/// Binary format version.
const FORMAT_VERSION: u8 = 1;

/// Serialize a proof certificate to deterministic binary bytes.
///
/// Format: `MAGIC (4 bytes) | VERSION (1 byte) | bincode payload`
///
/// Deterministic: the same certificate always produces the same bytes.
pub(crate) fn serialize(cert: &ProofCertificate) -> Result<Vec<u8>, CertError> {
    let payload = bincode::serialize(cert)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

    let mut bytes = Vec::with_capacity(MAGIC.len() + 1 + payload.len());
    bytes.extend_from_slice(MAGIC);
    bytes.push(FORMAT_VERSION);
    bytes.extend_from_slice(&payload);
    Ok(bytes)
}

/// Deserialize a proof certificate from binary bytes.
///
/// Validates the magic bytes and format version before decoding.
pub(crate) fn deserialize(bytes: &[u8]) -> Result<ProofCertificate, CertError> {
    let header_len = MAGIC.len() + 1;
    if bytes.len() < header_len {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "binary too short: expected at least {header_len} bytes, got {}",
                bytes.len()
            ),
        });
    }

    if &bytes[..MAGIC.len()] != MAGIC {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "invalid magic bytes: expected {:?}, got {:?}",
                MAGIC,
                &bytes[..MAGIC.len()]
            ),
        });
    }

    let version = bytes[MAGIC.len()];
    if version != FORMAT_VERSION {
        return Err(CertError::SerializationFailed {
            reason: format!(
                "unsupported format version: expected {FORMAT_VERSION}, got {version}"
            ),
        });
    }

    let payload = &bytes[header_len..];
    bincode::deserialize(payload)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofStep, SolverInfo,
        VcSnapshot,
    };

    fn make_test_cert() -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 8,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let steps = vec![ProofStep {
            index: 0,
            rule: "axiom".to_string(),
            description: "true by axiom".to_string(),
            premises: vec![],
        }];
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "z4".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 8,
            timestamp: "2026-03-28T00:00:00Z".to_string(),
        });

        ProofCertificate::new_trusted(
            "crate::example".to_string(),
            FunctionHash::from_bytes(b"example-body"),
            vc_snapshot,
            solver,
            vec![0xCA, 0xFE],
            "2026-03-28T00:00:00Z".to_string(),
        )
        .with_proof_steps(steps)
        .with_witness(vec![0x01, 0x02])
        .with_chain(chain)
    }

    #[test]
    fn test_binary_roundtrip() {
        let cert = make_test_cert();
        let bytes = serialize(&cert).expect("serialization should succeed");
        let restored = deserialize(&bytes).expect("deserialization should succeed");
        assert_eq!(restored, cert);
    }

    #[test]
    fn test_deterministic_encoding() {
        let cert = make_test_cert();
        let bytes1 = serialize(&cert).expect("first serialization");
        let bytes2 = serialize(&cert).expect("second serialization");
        assert_eq!(bytes1, bytes2, "same input must produce same bytes");
    }

    #[test]
    fn test_magic_bytes_present() {
        let cert = make_test_cert();
        let bytes = serialize(&cert).expect("serialization");
        assert_eq!(&bytes[..4], b"tRPC", "magic bytes should be tRPC");
        assert_eq!(bytes[4], 1, "format version should be 1");
    }

    #[test]
    fn test_deserialize_too_short() {
        let err = deserialize(b"tR").expect_err("should fail on short input");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("too short"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_deserialize_wrong_magic() {
        let err = deserialize(b"XXXX\x01payload").expect_err("should fail on wrong magic");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("invalid magic"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_deserialize_wrong_version() {
        let err = deserialize(b"tRPC\x99payload").expect_err("should fail on wrong version");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("unsupported format version"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }
}
