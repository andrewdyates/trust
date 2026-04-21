// trust-proof-cert audit trail
//
// AuditLog: append-only, hash-chained log of certificate lifecycle events.
// Each entry records an action, certificate ID, timestamp, actor, and details.
// Supports queries by certificate, action, time range, and statistics.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};
use serde::{Deserialize, Serialize};

use crate::timestamp::Timestamp;
use trust_types::fx::FxHashSet;

/// Actions that can be recorded in the audit log.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum AuditAction {
    /// A new certificate was created.
    Created,
    /// A certificate was verified (integrity check passed).
    Verified,
    /// A certificate was revoked (e.g. source changed, proof invalidated).
    Revoked,
    /// A certificate expired (TTL exceeded).
    Expired,
    /// The certificate chain was extended (e.g. lean5 certification added).
    ChainExtended,
    /// A certificate was looked up / queried.
    Queried,
    /// A certificate's integrity check failed.
    IntegrityFailed,
}

/// A single entry in the audit log.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct AuditEntry {
    /// What action was performed.
    pub action: AuditAction,
    /// The certificate this action applies to.
    pub certificate_id: String,
    /// When the action occurred.
    pub timestamp: Timestamp,
    /// Who or what performed the action (e.g. "trust-driver", "lean5", "user").
    pub actor: String,
    /// Additional human-readable details.
    pub details: String,
    /// SHA-256 hash of the previous entry (hash chain). Zero for the first entry.
    pub prev_hash: [u8; 32],
}

impl AuditEntry {
    /// Compute the SHA-256 hash of this entry's content (excluding `prev_hash`
    /// to avoid circularity, but including the previous entry's hash for chaining).
    pub(crate) fn content_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(format!("{:?}", self.action).as_bytes());
        hasher.update(b"|");
        hasher.update(self.certificate_id.as_bytes());
        hasher.update(b"|");
        hasher.update(self.timestamp.unix_secs.to_le_bytes());
        hasher.update(self.timestamp.nanos.to_le_bytes());
        hasher.update(b"|");
        hasher.update(self.actor.as_bytes());
        hasher.update(b"|");
        hasher.update(self.details.as_bytes());
        hasher.update(b"|");
        hasher.update(self.prev_hash);
        hasher.finalize().into()
    }
}

/// Summary statistics for an audit log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AuditStats {
    /// Total number of entries.
    pub total_entries: usize,
    /// Count of Created actions.
    pub created: usize,
    /// Count of Verified actions.
    pub verified: usize,
    /// Count of Revoked actions.
    pub revoked: usize,
    /// Count of Expired actions.
    pub expired: usize,
    /// Count of ChainExtended actions.
    pub chain_extended: usize,
    /// Count of Queried actions.
    pub queried: usize,
    /// Count of IntegrityFailed actions.
    pub integrity_failed: usize,
    /// Number of distinct certificate IDs.
    pub distinct_certs: usize,
    /// Number of distinct actors.
    pub distinct_actors: usize,
}

/// An append-only, hash-chained audit log.
///
/// Each entry's `prev_hash` is the content hash of the preceding entry,
/// forming a tamper-evident chain (similar to a blockchain).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct AuditLog {
    entries: Vec<AuditEntry>,
}

impl AuditLog {
    /// Create a new empty audit log.
    pub fn new() -> Self {
        AuditLog { entries: Vec::new() }
    }

    /// Append an entry to the log.
    ///
    /// Automatically sets `prev_hash` to the content hash of the last entry
    /// (or zero for the first entry).
    pub fn append(&mut self, mut entry: AuditEntry) {
        entry.prev_hash = self.last_hash();
        self.entries.push(entry);
    }

    /// Convenience: record a lifecycle event with the current time.
    pub fn record(
        &mut self,
        action: AuditAction,
        certificate_id: &str,
        actor: &str,
        details: &str,
    ) {
        self.append(AuditEntry {
            action,
            certificate_id: certificate_id.to_string(),
            timestamp: Timestamp::now(),
            actor: actor.to_string(),
            details: details.to_string(),
            prev_hash: [0u8; 32], // will be overwritten by append()
        });
    }

    /// Query all entries for a specific certificate ID.
    pub fn query_by_cert(&self, cert_id: &str) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.certificate_id == cert_id).collect()
    }

    /// Query all entries for a specific action type.
    pub fn query_by_action(&self, action: &AuditAction) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| &e.action == action).collect()
    }

    /// Query entries within a time range (inclusive on both ends).
    pub fn query_by_time_range(&self, start: &Timestamp, end: &Timestamp) -> Vec<&AuditEntry> {
        self.entries
            .iter()
            .filter(|e| e.timestamp >= *start && e.timestamp <= *end)
            .collect()
    }

    /// Query entries by actor.
    pub fn query_by_actor(&self, actor: &str) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.actor == actor).collect()
    }

    /// Query entries matching a certificate ID and action type.
    pub fn query_by_cert_and_action(
        &self,
        cert_id: &str,
        action: &AuditAction,
    ) -> Vec<&AuditEntry> {
        self.entries
            .iter()
            .filter(|e| e.certificate_id == cert_id && &e.action == action)
            .collect()
    }

    /// Get the most recent action for a given certificate.
    pub fn latest_action_for(&self, cert_id: &str) -> Option<&AuditEntry> {
        self.entries
            .iter()
            .rev()
            .find(|e| e.certificate_id == cert_id)
    }

    /// Compute summary statistics for this audit log.
    pub fn stats(&self) -> AuditStats {
        let mut created = 0usize;
        let mut verified = 0usize;
        let mut revoked = 0usize;
        let mut expired = 0usize;
        let mut chain_extended = 0usize;
        let mut queried = 0usize;
        let mut integrity_failed = 0usize;
        let mut cert_ids = FxHashSet::default();
        let mut actors = FxHashSet::default();

        for entry in &self.entries {
            match entry.action {
                AuditAction::Created => created += 1,
                AuditAction::Verified => verified += 1,
                AuditAction::Revoked => revoked += 1,
                AuditAction::Expired => expired += 1,
                AuditAction::ChainExtended => chain_extended += 1,
                AuditAction::Queried => queried += 1,
                AuditAction::IntegrityFailed => integrity_failed += 1,
            }
            cert_ids.insert(&entry.certificate_id);
            actors.insert(&entry.actor);
        }

        AuditStats {
            total_entries: self.entries.len(),
            created,
            verified,
            revoked,
            expired,
            chain_extended,
            queried,
            integrity_failed,
            distinct_certs: cert_ids.len(),
            distinct_actors: actors.len(),
        }
    }

    /// Verify the integrity of the entire audit log.
    ///
    /// Checks that each entry's `prev_hash` matches the content hash of
    /// the preceding entry. Returns `true` if the chain is intact.
    pub fn verify_integrity(&self) -> bool {
        if self.entries.is_empty() {
            return true;
        }

        // First entry must have zero prev_hash
        if self.entries[0].prev_hash != [0u8; 32] {
            return false;
        }

        // Each subsequent entry's prev_hash must match the prior entry's content hash
        for i in 1..self.entries.len() {
            let expected = self.entries[i - 1].content_hash();
            if self.entries[i].prev_hash != expected {
                return false;
            }
        }

        true
    }

    /// Returns the number of entries in the log.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true if the log has no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns all entries as a slice.
    pub fn entries(&self) -> &[AuditEntry] {
        &self.entries
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, crate::CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| crate::CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        serde_json::from_str(json)
            .map_err(|e| crate::CertError::SerializationFailed { reason: e.to_string() })
    }

    /// The content hash of the last entry, or zero for an empty log.
    fn last_hash(&self) -> [u8; 32] {
        self.entries.last().map(|e| e.content_hash()).unwrap_or([0u8; 32])
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

    fn make_entry(action: AuditAction, cert_id: &str, actor: &str) -> AuditEntry {
        AuditEntry {
            action,
            certificate_id: cert_id.to_string(),
            timestamp: Timestamp::new(1000, 0),
            actor: actor.to_string(),
            details: String::new(),
            prev_hash: [0u8; 32], // will be set by append()
        }
    }

    fn make_entry_at(
        action: AuditAction,
        cert_id: &str,
        actor: &str,
        secs: u64,
    ) -> AuditEntry {
        AuditEntry {
            action,
            certificate_id: cert_id.to_string(),
            timestamp: Timestamp::new(secs, 0),
            actor: actor.to_string(),
            details: String::new(),
            prev_hash: [0u8; 32],
        }
    }

    // --- Basic append and query ---

    #[test]
    fn test_audit_log_append_and_query() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "trust-driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Created, "cert-2", "trust-driver"));

        assert_eq!(log.len(), 3);

        let cert1_entries = log.query_by_cert("cert-1");
        assert_eq!(cert1_entries.len(), 2);
        assert_eq!(cert1_entries[0].action, AuditAction::Created);
        assert_eq!(cert1_entries[1].action, AuditAction::Verified);

        let cert2_entries = log.query_by_cert("cert-2");
        assert_eq!(cert2_entries.len(), 1);
    }

    #[test]
    fn test_audit_log_query_by_action() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Created, "cert-2", "driver"));

        let created = log.query_by_action(&AuditAction::Created);
        assert_eq!(created.len(), 2);

        let verified = log.query_by_action(&AuditAction::Verified);
        assert_eq!(verified.len(), 1);

        let revoked = log.query_by_action(&AuditAction::Revoked);
        assert!(revoked.is_empty());
    }

    // --- Integrity tests ---

    #[test]
    fn test_audit_log_integrity_valid() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::ChainExtended, "cert-1", "lean5"));

        assert!(log.verify_integrity());
    }

    #[test]
    fn test_audit_log_integrity_empty() {
        let log = AuditLog::new();
        assert!(log.verify_integrity());
    }

    #[test]
    fn test_audit_log_integrity_tampered() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));

        // Tamper with the first entry's details
        log.entries[0].details = "tampered!".to_string();

        assert!(!log.verify_integrity(), "tampered log should fail integrity check");
    }

    #[test]
    fn test_audit_log_integrity_bad_prev_hash() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));

        // Corrupt the second entry's prev_hash
        log.entries[1].prev_hash[0] ^= 0xFF;

        assert!(!log.verify_integrity());
    }

    #[test]
    fn test_audit_log_integrity_bad_first_entry() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));

        // First entry should have zero prev_hash; corrupt it
        log.entries[0].prev_hash[0] = 1;

        assert!(!log.verify_integrity());
    }

    #[test]
    fn test_audit_log_hash_chain_links() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));

        // First entry prev_hash is zero
        assert_eq!(log.entries()[0].prev_hash, [0u8; 32]);
        // Second entry prev_hash should be content hash of first
        let expected = log.entries()[0].content_hash();
        assert_eq!(log.entries()[1].prev_hash, expected);
    }

    // --- JSON roundtrip ---

    #[test]
    fn test_audit_log_json_roundtrip() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Revoked, "cert-1", "driver"));

        let json = log.to_json().expect("should serialize");
        let restored = AuditLog::from_json(&json).expect("should deserialize");

        assert_eq!(restored, log);
        assert!(restored.verify_integrity());
    }

    // --- All actions ---

    #[test]
    fn test_audit_log_all_actions() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::ChainExtended, "cert-1", "lean5"));
        log.append(make_entry(AuditAction::Expired, "cert-1", "gc"));
        log.append(make_entry(AuditAction::Revoked, "cert-1", "driver"));

        assert_eq!(log.len(), 5);
        assert!(log.verify_integrity());
    }

    #[test]
    fn test_audit_log_query_empty_cert() {
        let log = AuditLog::new();
        assert!(log.query_by_cert("nonexistent").is_empty());
    }

    #[test]
    fn test_audit_entry_content_hash_deterministic() {
        let entry = make_entry(AuditAction::Created, "cert-1", "driver");
        let h1 = entry.content_hash();
        let h2 = entry.content_hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_audit_entry_content_hash_differs() {
        let e1 = make_entry(AuditAction::Created, "cert-1", "driver");
        let e2 = make_entry(AuditAction::Created, "cert-2", "driver");
        assert_ne!(e1.content_hash(), e2.content_hash());
    }

    // --- New: time range queries ---

    #[test]
    fn test_query_by_time_range() {
        let mut log = AuditLog::new();
        log.append(make_entry_at(AuditAction::Created, "cert-1", "driver", 100));
        log.append(make_entry_at(AuditAction::Verified, "cert-1", "verifier", 200));
        log.append(make_entry_at(AuditAction::Created, "cert-2", "driver", 300));
        log.append(make_entry_at(AuditAction::Revoked, "cert-1", "driver", 400));

        let start = Timestamp::new(150, 0);
        let end = Timestamp::new(350, 0);
        let results = log.query_by_time_range(&start, &end);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].certificate_id, "cert-1");
        assert_eq!(results[0].action, AuditAction::Verified);
        assert_eq!(results[1].certificate_id, "cert-2");
    }

    #[test]
    fn test_query_by_time_range_empty() {
        let mut log = AuditLog::new();
        log.append(make_entry_at(AuditAction::Created, "cert-1", "driver", 100));

        let start = Timestamp::new(200, 0);
        let end = Timestamp::new(300, 0);
        assert!(log.query_by_time_range(&start, &end).is_empty());
    }

    #[test]
    fn test_query_by_time_range_inclusive() {
        let mut log = AuditLog::new();
        log.append(make_entry_at(AuditAction::Created, "cert-1", "driver", 100));
        log.append(make_entry_at(AuditAction::Verified, "cert-1", "verifier", 200));

        let start = Timestamp::new(100, 0);
        let end = Timestamp::new(200, 0);
        let results = log.query_by_time_range(&start, &end);
        assert_eq!(results.len(), 2);
    }

    // --- New: query by actor ---

    #[test]
    fn test_query_by_actor() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Created, "cert-2", "driver"));

        let driver_entries = log.query_by_actor("driver");
        assert_eq!(driver_entries.len(), 2);

        let verifier_entries = log.query_by_actor("verifier");
        assert_eq!(verifier_entries.len(), 1);

        assert!(log.query_by_actor("nobody").is_empty());
    }

    // --- New: query by cert and action ---

    #[test]
    fn test_query_by_cert_and_action() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Created, "cert-2", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-2", "verifier"));

        let results = log.query_by_cert_and_action("cert-1", &AuditAction::Verified);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].certificate_id, "cert-1");
        assert_eq!(results[0].action, AuditAction::Verified);
    }

    // --- New: latest action for cert ---

    #[test]
    fn test_latest_action_for() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Revoked, "cert-1", "driver"));

        let latest = log.latest_action_for("cert-1").expect("should find entry");
        assert_eq!(latest.action, AuditAction::Revoked);
    }

    #[test]
    fn test_latest_action_for_nonexistent() {
        let log = AuditLog::new();
        assert!(log.latest_action_for("cert-1").is_none());
    }

    // --- New: statistics ---

    #[test]
    fn test_audit_stats() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Created, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Verified, "cert-1", "verifier"));
        log.append(make_entry(AuditAction::Created, "cert-2", "driver"));
        log.append(make_entry(AuditAction::Revoked, "cert-1", "driver"));
        log.append(make_entry(AuditAction::Expired, "cert-2", "gc"));

        let stats = log.stats();
        assert_eq!(stats.total_entries, 5);
        assert_eq!(stats.created, 2);
        assert_eq!(stats.verified, 1);
        assert_eq!(stats.revoked, 1);
        assert_eq!(stats.expired, 1);
        assert_eq!(stats.chain_extended, 0);
        assert_eq!(stats.queried, 0);
        assert_eq!(stats.integrity_failed, 0);
        assert_eq!(stats.distinct_certs, 2);
        assert_eq!(stats.distinct_actors, 3); // driver, verifier, gc
    }

    #[test]
    fn test_audit_stats_empty() {
        let log = AuditLog::new();
        let stats = log.stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.distinct_certs, 0);
        assert_eq!(stats.distinct_actors, 0);
    }

    #[test]
    fn test_audit_stats_new_actions() {
        let mut log = AuditLog::new();
        log.append(make_entry(AuditAction::Queried, "cert-1", "client"));
        log.append(make_entry(AuditAction::IntegrityFailed, "cert-1", "verifier"));

        let stats = log.stats();
        assert_eq!(stats.queried, 1);
        assert_eq!(stats.integrity_failed, 1);
    }

    // --- New: record convenience method ---

    #[test]
    fn test_record_convenience() {
        let mut log = AuditLog::new();
        log.record(AuditAction::Created, "cert-1", "driver", "initial creation");
        log.record(AuditAction::Verified, "cert-1", "verifier", "all checks passed");

        assert_eq!(log.len(), 2);
        assert!(log.verify_integrity());
        assert_eq!(log.entries()[0].details, "initial creation");
        assert_eq!(log.entries()[1].details, "all checks passed");
        // Timestamps should be non-zero (system clock)
        assert!(log.entries()[0].timestamp.unix_secs > 0);
    }
}
