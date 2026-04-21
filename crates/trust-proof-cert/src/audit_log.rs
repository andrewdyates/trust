// trust-proof-cert audit logging
//
// Structured audit logging for proof certificate lifecycle events.
// Provides an append-only, hash-chained log with time-range and
// certificate-scoped queries plus tamper-detection via integrity checks.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};

use crate::error::CertError;

/// Certificate lifecycle events that can be recorded in the audit log.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum AuditEvent {
    /// A new proof certificate was created.
    Created,
    /// A proof certificate was successfully verified.
    Verified,
    /// A proof certificate was invalidated (e.g. source changed).
    Invalidated,
    /// Ownership or responsibility for a certificate was transferred.
    Transferred,
    /// A proof certificate expired (TTL exceeded).
    Expired,
}

/// A single audit record in the log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AuditRecord {
    /// The lifecycle event that occurred.
    pub event: AuditEvent,
    /// Unix epoch seconds when the event was recorded.
    pub timestamp: u64,
    /// The certificate this event pertains to.
    pub certificate_id: String,
    /// Who or what triggered the event (e.g. "trust-driver", "lean5").
    pub actor: String,
    /// Human-readable description of the event.
    pub details: String,
    /// SHA-256 hash of the previous record (hash chain). Zero for the first.
    prev_hash: [u8; 32],
}

impl AuditRecord {
    /// Create a new audit record. The `prev_hash` is managed internally by
    /// `AuditLog` and is set to zero here.
    pub fn new(
        event: AuditEvent,
        timestamp: u64,
        certificate_id: &str,
        actor: &str,
        details: &str,
    ) -> Self {
        AuditRecord {
            event,
            timestamp,
            certificate_id: certificate_id.to_string(),
            actor: actor.to_string(),
            details: details.to_string(),
            prev_hash: [0u8; 32],
        }
    }

    /// Compute the SHA-256 content hash of this record.
    ///
    /// Includes the `prev_hash` field to chain records together.
    fn content_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(format!("{:?}", self.event).as_bytes());
        hasher.update(b"|");
        hasher.update(self.timestamp.to_le_bytes());
        hasher.update(b"|");
        hasher.update(self.certificate_id.as_bytes());
        hasher.update(b"|");
        hasher.update(self.actor.as_bytes());
        hasher.update(b"|");
        hasher.update(self.details.as_bytes());
        hasher.update(b"|");
        hasher.update(self.prev_hash);
        hasher.finalize().into()
    }
}

/// An append-only, hash-chained audit log for proof certificate events.
///
/// Each record's `prev_hash` is the content hash of the preceding record,
/// forming a tamper-evident chain.
#[derive(Debug, Clone)]
pub(crate) struct AuditLog {
    records: Vec<AuditRecord>,
}

impl AuditLog {
    /// Create a new empty audit log.
    pub fn new() -> Self {
        AuditLog { records: Vec::new() }
    }

    /// Record an audit event, appending it to the log.
    ///
    /// Automatically chains the record to the previous entry via its hash.
    pub fn log_event(
        &mut self,
        event: AuditEvent,
        timestamp: u64,
        certificate_id: &str,
        actor: &str,
        details: &str,
    ) {
        let prev_hash = self.last_hash();
        let mut record = AuditRecord::new(event, timestamp, certificate_id, actor, details);
        record.prev_hash = prev_hash;
        self.records.push(record);
    }

    /// Find all audit records for a given certificate ID.
    pub fn query_by_cert(&self, certificate_id: &str) -> Vec<&AuditRecord> {
        self.records
            .iter()
            .filter(|r| r.certificate_id == certificate_id)
            .collect()
    }

    /// Find all audit records within a time range (inclusive on both ends).
    pub fn query_by_time(&self, start: u64, end: u64) -> Vec<&AuditRecord> {
        self.records
            .iter()
            .filter(|r| r.timestamp >= start && r.timestamp <= end)
            .collect()
    }

    /// Verify the integrity of the entire audit log via its hash chain.
    ///
    /// Returns `Ok(())` if the chain is intact, or an error describing the
    /// first broken link.
    pub fn integrity_check(&self) -> Result<(), CertError> {
        if self.records.is_empty() {
            return Ok(());
        }

        // First record must have zero prev_hash.
        if self.records[0].prev_hash != [0u8; 32] {
            return Err(CertError::VerificationFailed {
                reason: "first audit record has non-zero prev_hash".to_string(),
            });
        }

        // Each subsequent record's prev_hash must match the prior's content hash.
        for i in 1..self.records.len() {
            let expected = self.records[i - 1].content_hash();
            if self.records[i].prev_hash != expected {
                return Err(CertError::VerificationFailed {
                    reason: format!(
                        "hash chain broken at record {i}: expected {:x?}, got {:x?}",
                        &expected[..4],
                        &self.records[i].prev_hash[..4],
                    ),
                });
            }
        }

        Ok(())
    }

    /// Returns the number of records in the log.
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Returns true if the log contains no records.
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Returns all records as a slice.
    pub fn records(&self) -> &[AuditRecord] {
        &self.records
    }

    /// The content hash of the last record, or zero for an empty log.
    fn last_hash(&self) -> [u8; 32] {
        self.records
            .last()
            .map(|r| r.content_hash())
            .unwrap_or([0u8; 32])
    }
}

impl Default for AuditLog {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Basic append and query ---

    #[test]
    fn test_log_event_and_len() {
        let mut log = AuditLog::new();
        assert!(log.is_empty());
        assert_eq!(log.len(), 0);

        log.log_event(AuditEvent::Created, 1000, "cert-1", "driver", "new cert");
        assert_eq!(log.len(), 1);
        assert!(!log.is_empty());

        log.log_event(AuditEvent::Verified, 1001, "cert-1", "verifier", "ok");
        assert_eq!(log.len(), 2);
    }

    #[test]
    fn test_query_by_cert_returns_matching_records() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "");
        log.log_event(AuditEvent::Created, 101, "cert-2", "driver", "");
        log.log_event(AuditEvent::Verified, 102, "cert-1", "verifier", "");

        let results = log.query_by_cert("cert-1");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].event, AuditEvent::Created);
        assert_eq!(results[1].event, AuditEvent::Verified);
    }

    #[test]
    fn test_query_by_cert_no_match() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "");

        assert!(log.query_by_cert("nonexistent").is_empty());
    }

    #[test]
    fn test_query_by_time_inclusive_range() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "c1", "d", "");
        log.log_event(AuditEvent::Verified, 200, "c2", "d", "");
        log.log_event(AuditEvent::Invalidated, 300, "c3", "d", "");
        log.log_event(AuditEvent::Expired, 400, "c4", "d", "");

        let results = log.query_by_time(200, 300);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].certificate_id, "c2");
        assert_eq!(results[1].certificate_id, "c3");
    }

    #[test]
    fn test_query_by_time_no_match() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "c1", "d", "");

        assert!(log.query_by_time(200, 300).is_empty());
    }

    // --- Integrity checks ---

    #[test]
    fn test_integrity_check_empty_log() {
        let log = AuditLog::new();
        log.integrity_check().expect("empty log should pass integrity check");
    }

    #[test]
    fn test_integrity_check_valid_chain() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "created");
        log.log_event(AuditEvent::Verified, 200, "cert-1", "verifier", "ok");
        log.log_event(AuditEvent::Transferred, 300, "cert-1", "admin", "to team-b");

        log.integrity_check().expect("valid chain should pass");
    }

    #[test]
    fn test_integrity_check_detects_tampered_record() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "ok");
        log.log_event(AuditEvent::Verified, 200, "cert-1", "verifier", "ok");

        // Tamper with the first record's details.
        log.records[0].details = "tampered!".to_string();

        let err = log.integrity_check().expect_err("tampered log should fail");
        match err {
            CertError::VerificationFailed { reason } => {
                assert!(reason.contains("hash chain broken"), "reason: {reason}");
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_integrity_check_detects_corrupted_prev_hash() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "");
        log.log_event(AuditEvent::Expired, 200, "cert-1", "gc", "");

        // Corrupt the second record's prev_hash.
        log.records[1].prev_hash[0] ^= 0xFF;

        assert!(log.integrity_check().is_err());
    }

    #[test]
    fn test_integrity_check_detects_bad_first_entry() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "");

        // First entry must have zero prev_hash; corrupt it.
        log.records[0].prev_hash[0] = 1;

        let err = log.integrity_check().expect_err("bad first entry should fail");
        match err {
            CertError::VerificationFailed { reason } => {
                assert!(reason.contains("first audit record"), "reason: {reason}");
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    // --- All event types ---

    #[test]
    fn test_all_event_types_recorded() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "c1", "a", "");
        log.log_event(AuditEvent::Verified, 101, "c1", "a", "");
        log.log_event(AuditEvent::Invalidated, 102, "c1", "a", "");
        log.log_event(AuditEvent::Transferred, 103, "c1", "a", "");
        log.log_event(AuditEvent::Expired, 104, "c1", "a", "");

        assert_eq!(log.len(), 5);
        log.integrity_check().expect("all event types should chain correctly");

        assert_eq!(log.records()[0].event, AuditEvent::Created);
        assert_eq!(log.records()[1].event, AuditEvent::Verified);
        assert_eq!(log.records()[2].event, AuditEvent::Invalidated);
        assert_eq!(log.records()[3].event, AuditEvent::Transferred);
        assert_eq!(log.records()[4].event, AuditEvent::Expired);
    }

    // --- Hash chain linking ---

    #[test]
    fn test_hash_chain_first_entry_has_zero_prev() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "");

        assert_eq!(log.records()[0].prev_hash, [0u8; 32]);
    }

    #[test]
    fn test_hash_chain_second_entry_links_to_first() {
        let mut log = AuditLog::new();
        log.log_event(AuditEvent::Created, 100, "cert-1", "driver", "");
        log.log_event(AuditEvent::Verified, 200, "cert-1", "verifier", "");

        let expected = log.records()[0].content_hash();
        assert_eq!(log.records()[1].prev_hash, expected);
    }

    // --- Record field access ---

    #[test]
    fn test_record_fields_preserved() {
        let mut log = AuditLog::new();
        log.log_event(
            AuditEvent::Transferred,
            1234567890,
            "cert-abc",
            "admin-bot",
            "moved to team-x",
        );

        let r = &log.records()[0];
        assert_eq!(r.event, AuditEvent::Transferred);
        assert_eq!(r.timestamp, 1234567890);
        assert_eq!(r.certificate_id, "cert-abc");
        assert_eq!(r.actor, "admin-bot");
        assert_eq!(r.details, "moved to team-x");
    }

    // --- Default trait ---

    #[test]
    fn test_default_creates_empty_log() {
        let log = AuditLog::default();
        assert!(log.is_empty());
        log.integrity_check().expect("default log should pass");
    }
}
