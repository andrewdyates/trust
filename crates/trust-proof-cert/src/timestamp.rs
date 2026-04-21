// trust-proof-cert certificate timestamping
//
// Timestamp: high-resolution time point (unix seconds + nanos).
// CertificateTimestamp: binds a certificate digest to a time and chain position.
// TimestampAuthority: trait for stamping certificate digests.
// Expiration: validity period checking for certificates.
// Clock skew tolerance: graceful handling of minor clock differences.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::integrity::CertificateDigest;

/// Default certificate validity period: 90 days in seconds.
pub(crate) const DEFAULT_VALIDITY_SECS: u64 = 90 * 24 * 60 * 60;

/// Default clock skew tolerance: 5 seconds.
pub(crate) const DEFAULT_SKEW_TOLERANCE_SECS: u64 = 5;

/// A high-resolution timestamp: Unix seconds plus nanosecond fractional part.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct Timestamp {
    /// Seconds since Unix epoch (1970-01-01T00:00:00Z).
    pub unix_secs: u64,
    /// Nanosecond fractional part (0..999_999_999).
    pub nanos: u32,
}

impl Timestamp {
    /// Create a new timestamp.
    pub fn new(unix_secs: u64, nanos: u32) -> Self {
        Timestamp { unix_secs, nanos }
    }

    /// Create a timestamp from the system clock.
    pub fn now() -> Self {
        let dur = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default();
        Timestamp {
            unix_secs: dur.as_secs(),
            nanos: dur.subsec_nanos(),
        }
    }

    /// Total nanoseconds since epoch (for comparison).
    pub fn as_nanos(&self) -> u128 {
        self.unix_secs as u128 * 1_000_000_000 + self.nanos as u128
    }

    /// Returns the absolute difference in seconds between two timestamps.
    pub fn diff_secs(&self, other: &Timestamp) -> u64 {
        let a = self.unix_secs;
        let b = other.unix_secs;
        a.abs_diff(b)
    }

    /// Add seconds to this timestamp.
    #[must_use]
    pub fn add_secs(&self, secs: u64) -> Timestamp {
        Timestamp {
            unix_secs: self.unix_secs + secs,
            nanos: self.nanos,
        }
    }

    /// Subtract seconds from this timestamp, saturating at zero.
    #[must_use]
    pub fn sub_secs(&self, secs: u64) -> Timestamp {
        Timestamp {
            unix_secs: self.unix_secs.saturating_sub(secs),
            nanos: self.nanos,
        }
    }
}

/// A timestamped certificate digest with chain position.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CertificateTimestamp {
    /// The digest of the certificate being timestamped.
    pub cert_digest: CertificateDigest,
    /// When the timestamp was issued.
    pub timestamp: Timestamp,
    /// Position in the certificate chain (0-based index).
    pub chain_position: usize,
}

/// Trait for authorities that produce certificate timestamps.
///
/// A timestamp authority binds a certificate digest to a verifiable time point.
pub(crate) trait TimestampAuthority {
    /// Stamp a certificate digest, producing a `CertificateTimestamp`.
    ///
    /// `chain_position` indicates where this certificate sits in the chain.
    fn stamp(
        &self,
        digest: &CertificateDigest,
        chain_position: usize,
    ) -> CertificateTimestamp;
}

/// A local timestamp authority that uses the system clock.
///
/// Suitable for development and single-machine verification.
/// For distributed or adversarial settings, use a remote TSA.
pub(crate) struct LocalTimestampAuthority;

impl TimestampAuthority for LocalTimestampAuthority {
    fn stamp(
        &self,
        digest: &CertificateDigest,
        chain_position: usize,
    ) -> CertificateTimestamp {
        CertificateTimestamp {
            cert_digest: digest.clone(),
            timestamp: Timestamp::now(),
            chain_position,
        }
    }
}

/// Verify that a sequence of certificate timestamps is in strictly
/// monotonically increasing order.
///
/// Returns `true` if all timestamps are strictly ordered by time.
/// An empty or single-element sequence is trivially ordered.
pub(crate) fn verify_timestamp_order(chain: &[CertificateTimestamp]) -> bool {
    chain.windows(2).all(|w| w[0].timestamp < w[1].timestamp)
}

/// Certificate validity period configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ValidityPolicy {
    /// How long a certificate is valid, in seconds.
    pub validity_secs: u64,
    /// Clock skew tolerance in seconds. Timestamps within this window
    /// of the current time are accepted even if slightly in the future.
    pub skew_tolerance_secs: u64,
}

impl ValidityPolicy {
    /// Create a policy with custom validity and skew.
    pub fn new(validity_secs: u64, skew_tolerance_secs: u64) -> Self {
        ValidityPolicy { validity_secs, skew_tolerance_secs }
    }
}

impl Default for ValidityPolicy {
    fn default() -> Self {
        ValidityPolicy {
            validity_secs: DEFAULT_VALIDITY_SECS,
            skew_tolerance_secs: DEFAULT_SKEW_TOLERANCE_SECS,
        }
    }
}

/// Result of checking a certificate timestamp's validity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValidityStatus {
    /// The certificate is within its validity period.
    Valid,
    /// The certificate has expired. Contains seconds past expiration.
    Expired { seconds_past: u64 },
    /// The certificate timestamp is in the future, beyond skew tolerance.
    FutureTimestamp { seconds_ahead: u64 },
    /// The certificate is within the skew tolerance window (slightly future).
    ValidWithSkew,
}

impl ValidityStatus {
    /// Returns `true` if the status indicates the certificate is acceptable.
    pub fn is_acceptable(&self) -> bool {
        matches!(self, ValidityStatus::Valid | ValidityStatus::ValidWithSkew)
    }
}

/// Check whether a certificate timestamp is valid given the current time
/// and a validity policy.
///
/// A certificate is valid if:
/// 1. Its timestamp is not more than `skew_tolerance_secs` in the future.
/// 2. Its age does not exceed `validity_secs`.
pub(crate) fn check_validity(
    cert_time: &Timestamp,
    now: &Timestamp,
    policy: &ValidityPolicy,
) -> ValidityStatus {
    // Check for future timestamps
    if cert_time.unix_secs > now.unix_secs + policy.skew_tolerance_secs {
        let ahead = cert_time.unix_secs - now.unix_secs;
        return ValidityStatus::FutureTimestamp { seconds_ahead: ahead };
    }

    // Check for slight future (within skew tolerance)
    if cert_time.unix_secs > now.unix_secs {
        return ValidityStatus::ValidWithSkew;
    }

    // Check expiration
    let age = now.unix_secs - cert_time.unix_secs;
    if age > policy.validity_secs {
        let past = age - policy.validity_secs;
        return ValidityStatus::Expired { seconds_past: past };
    }

    ValidityStatus::Valid
}

/// Check whether a timestamp sequence is monotonic within a skew tolerance.
///
/// Each consecutive pair must satisfy: `t[i+1] >= t[i] - skew_tolerance`.
/// This is more lenient than strict monotonicity, allowing for minor
/// clock drift between distributed verification steps.
pub(crate) fn verify_timestamp_order_with_skew(
    chain: &[CertificateTimestamp],
    skew_tolerance_secs: u64,
) -> bool {
    chain.windows(2).all(|w| {
        let prev = &w[0].timestamp;
        let next = &w[1].timestamp;
        // next must be at least (prev - skew_tolerance)
        next.unix_secs + skew_tolerance_secs >= prev.unix_secs
    })
}

/// Batch-check validity for a slice of certificate timestamps.
///
/// Returns a vec of (chain_position, status) pairs.
pub(crate) fn batch_check_validity(
    timestamps: &[CertificateTimestamp],
    now: &Timestamp,
    policy: &ValidityPolicy,
) -> Vec<(usize, ValidityStatus)> {
    timestamps
        .iter()
        .map(|ct| (ct.chain_position, check_validity(&ct.timestamp, now, policy)))
        .collect()
}

/// Parse an ISO 8601 timestamp to approximate Unix epoch seconds.
///
/// Handles the common `YYYY-MM-DDThh:mm:ssZ` format without pulling in chrono.
/// Used by both `store.rs` (staleness pruning) and `registry.rs` (GC expiration).
pub(crate) fn parse_timestamp_epoch(ts: &str) -> Option<u64> {
    // Minimal parser for "2026-03-27T12:00:00Z" format
    let ts = ts.trim_end_matches('Z');
    let parts: Vec<&str> = ts.split('T').collect();
    if parts.len() != 2 {
        return None;
    }
    let date_parts: Vec<&str> = parts[0].split('-').collect();
    let time_parts: Vec<&str> = parts[1].split(':').collect();
    if date_parts.len() != 3 || time_parts.len() != 3 {
        return None;
    }

    let year: u64 = date_parts[0].parse().ok()?;
    let month: u64 = date_parts[1].parse().ok()?;
    let day: u64 = date_parts[2].parse().ok()?;
    let hour: u64 = time_parts[0].parse().ok()?;
    let min: u64 = time_parts[1].parse().ok()?;
    let sec: u64 = time_parts[2].parse().ok()?;

    // Approximate days since epoch (good enough for ordering comparisons)
    let days_since_epoch = (year.saturating_sub(1970)) * 365
        + (year.saturating_sub(1969)) / 4
        + cumulative_month_days(month)
        + day.saturating_sub(1);
    Some(days_since_epoch * 86400 + hour * 3600 + min * 60 + sec)
}

/// Approximate cumulative days before a given month (Jan=1).
pub(crate) fn cumulative_month_days(month: u64) -> u64 {
    match month {
        1 => 0,
        2 => 31,
        3 => 59,
        4 => 90,
        5 => 120,
        6 => 151,
        7 => 181,
        8 => 212,
        9 => 243,
        10 => 273,
        11 => 304,
        12 => 334,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_digest(val: u8) -> CertificateDigest {
        let mut bytes = [0u8; 32];
        bytes[0] = val;
        CertificateDigest(bytes)
    }

    fn make_ts(secs: u64, nanos: u32, position: usize) -> CertificateTimestamp {
        CertificateTimestamp {
            cert_digest: make_digest(position as u8),
            timestamp: Timestamp::new(secs, nanos),
            chain_position: position,
        }
    }

    // --- Timestamp basics ---

    #[test]
    fn test_timestamp_ordering() {
        let t1 = Timestamp::new(1000, 0);
        let t2 = Timestamp::new(1000, 1);
        let t3 = Timestamp::new(1001, 0);
        assert!(t1 < t2);
        assert!(t2 < t3);
        assert!(t1 < t3);
    }

    #[test]
    fn test_timestamp_equality() {
        let t1 = Timestamp::new(1000, 500);
        let t2 = Timestamp::new(1000, 500);
        assert_eq!(t1, t2);
    }

    #[test]
    fn test_timestamp_as_nanos() {
        let t = Timestamp::new(1, 500_000_000);
        assert_eq!(t.as_nanos(), 1_500_000_000);
    }

    #[test]
    fn test_timestamp_now_nonzero() {
        let t = Timestamp::now();
        assert!(t.unix_secs > 0, "system clock should return nonzero seconds");
    }

    #[test]
    fn test_timestamp_diff_secs() {
        let t1 = Timestamp::new(1000, 0);
        let t2 = Timestamp::new(1042, 0);
        assert_eq!(t1.diff_secs(&t2), 42);
        assert_eq!(t2.diff_secs(&t1), 42);
    }

    #[test]
    fn test_timestamp_add_secs() {
        let t = Timestamp::new(1000, 500);
        let t2 = t.add_secs(60);
        assert_eq!(t2.unix_secs, 1060);
        assert_eq!(t2.nanos, 500);
    }

    #[test]
    fn test_timestamp_sub_secs_saturating() {
        let t = Timestamp::new(10, 0);
        let t2 = t.sub_secs(100);
        assert_eq!(t2.unix_secs, 0);
    }

    // --- Order verification ---

    #[test]
    fn test_verify_timestamp_order_valid() {
        let chain = vec![
            make_ts(1000, 0, 0),
            make_ts(1001, 0, 1),
            make_ts(1002, 0, 2),
        ];
        assert!(verify_timestamp_order(&chain));
    }

    #[test]
    fn test_verify_timestamp_order_equal_fails() {
        let chain = vec![
            make_ts(1000, 0, 0),
            make_ts(1000, 0, 1), // same time
        ];
        assert!(!verify_timestamp_order(&chain));
    }

    #[test]
    fn test_verify_timestamp_order_backwards_fails() {
        let chain = vec![
            make_ts(1002, 0, 0),
            make_ts(1001, 0, 1),
        ];
        assert!(!verify_timestamp_order(&chain));
    }

    #[test]
    fn test_verify_timestamp_order_empty() {
        assert!(verify_timestamp_order(&[]));
    }

    #[test]
    fn test_verify_timestamp_order_single() {
        let chain = vec![make_ts(1000, 0, 0)];
        assert!(verify_timestamp_order(&chain));
    }

    #[test]
    fn test_verify_timestamp_order_nanos_monotonic() {
        let chain = vec![
            make_ts(1000, 100, 0),
            make_ts(1000, 200, 1),
            make_ts(1000, 300, 2),
        ];
        assert!(verify_timestamp_order(&chain));
    }

    // --- TSA tests ---

    #[test]
    fn test_local_timestamp_authority_stamps() {
        let authority = LocalTimestampAuthority;
        let digest = make_digest(42);
        let ts = authority.stamp(&digest, 0);
        assert_eq!(ts.cert_digest, digest);
        assert_eq!(ts.chain_position, 0);
        assert!(ts.timestamp.unix_secs > 0);
    }

    #[test]
    fn test_local_timestamp_authority_monotonic() {
        let authority = LocalTimestampAuthority;
        let d1 = make_digest(1);
        let d2 = make_digest(2);
        let ts1 = authority.stamp(&d1, 0);
        // Small busy-wait to ensure clock advances
        let start = std::time::Instant::now();
        while start.elapsed().as_nanos() < 100 {
            std::hint::black_box(0);
        }
        let ts2 = authority.stamp(&d2, 1);
        assert!(
            ts1.timestamp <= ts2.timestamp,
            "local TSA should produce non-decreasing timestamps"
        );
    }

    #[test]
    fn test_certificate_timestamp_serialization() {
        let ts = make_ts(1000, 500, 3);
        let json = serde_json::to_string(&ts).expect("should serialize");
        let restored: CertificateTimestamp =
            serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(restored, ts);
    }

    // --- Validity / expiration tests ---

    #[test]
    fn test_check_validity_valid() {
        let cert_time = Timestamp::new(1000, 0);
        let now = Timestamp::new(1100, 0);
        let policy = ValidityPolicy::new(3600, 5);
        let status = check_validity(&cert_time, &now, &policy);
        assert_eq!(status, ValidityStatus::Valid);
        assert!(status.is_acceptable());
    }

    #[test]
    fn test_check_validity_expired() {
        let cert_time = Timestamp::new(1000, 0);
        let now = Timestamp::new(1000 + 3601, 0); // 1 second past validity
        let policy = ValidityPolicy::new(3600, 5);
        let status = check_validity(&cert_time, &now, &policy);
        assert_eq!(status, ValidityStatus::Expired { seconds_past: 1 });
        assert!(!status.is_acceptable());
    }

    #[test]
    fn test_check_validity_future_within_skew() {
        let cert_time = Timestamp::new(1003, 0);
        let now = Timestamp::new(1000, 0);
        let policy = ValidityPolicy::new(3600, 5);
        let status = check_validity(&cert_time, &now, &policy);
        assert_eq!(status, ValidityStatus::ValidWithSkew);
        assert!(status.is_acceptable());
    }

    #[test]
    fn test_check_validity_future_beyond_skew() {
        let cert_time = Timestamp::new(1010, 0);
        let now = Timestamp::new(1000, 0);
        let policy = ValidityPolicy::new(3600, 5);
        let status = check_validity(&cert_time, &now, &policy);
        assert_eq!(status, ValidityStatus::FutureTimestamp { seconds_ahead: 10 });
        assert!(!status.is_acceptable());
    }

    #[test]
    fn test_check_validity_exactly_at_boundary() {
        let cert_time = Timestamp::new(1000, 0);
        let now = Timestamp::new(1000 + 3600, 0); // exactly at validity boundary
        let policy = ValidityPolicy::new(3600, 5);
        let status = check_validity(&cert_time, &now, &policy);
        assert_eq!(status, ValidityStatus::Valid);
    }

    #[test]
    fn test_validity_policy_default() {
        let policy = ValidityPolicy::default();
        assert_eq!(policy.validity_secs, DEFAULT_VALIDITY_SECS);
        assert_eq!(policy.skew_tolerance_secs, DEFAULT_SKEW_TOLERANCE_SECS);
    }

    // --- Skew-tolerant order verification ---

    #[test]
    fn test_verify_order_with_skew_valid() {
        let chain = vec![
            make_ts(1000, 0, 0),
            make_ts(1001, 0, 1),
        ];
        assert!(verify_timestamp_order_with_skew(&chain, 5));
    }

    #[test]
    fn test_verify_order_with_skew_slight_backward() {
        // Second timestamp is 2 seconds before first, but skew tolerance is 5
        let chain = vec![
            make_ts(1002, 0, 0),
            make_ts(1000, 0, 1),
        ];
        assert!(verify_timestamp_order_with_skew(&chain, 5));
    }

    #[test]
    fn test_verify_order_with_skew_too_far_backward() {
        // Second timestamp is 10 seconds before first, skew tolerance is 5
        let chain = vec![
            make_ts(1010, 0, 0),
            make_ts(1000, 0, 1),
        ];
        assert!(!verify_timestamp_order_with_skew(&chain, 5));
    }

    #[test]
    fn test_verify_order_with_skew_empty() {
        assert!(verify_timestamp_order_with_skew(&[], 5));
    }

    // --- Batch validity ---

    #[test]
    fn test_batch_check_validity() {
        let now = Timestamp::new(2000, 0);
        let policy = ValidityPolicy::new(3600, 5);
        let timestamps = vec![
            make_ts(1500, 0, 0), // valid (age = 500s)
            make_ts(100, 0, 1),  // expired (age = 1900s > 3600? no, 1900 < 3600, valid)
        ];
        let results = batch_check_validity(&timestamps, &now, &policy);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].0, 0);
        assert!(results[0].1.is_acceptable());
        assert_eq!(results[1].0, 1);
        assert!(results[1].1.is_acceptable());
    }

    #[test]
    fn test_batch_check_validity_with_expired() {
        let now = Timestamp::new(10000, 0);
        let policy = ValidityPolicy::new(100, 5);
        let timestamps = vec![
            make_ts(9950, 0, 0), // age 50 < 100, valid
            make_ts(9000, 0, 1), // age 1000 > 100, expired
        ];
        let results = batch_check_validity(&timestamps, &now, &policy);
        assert!(results[0].1.is_acceptable());
        assert!(!results[1].1.is_acceptable());
    }

    // --- ISO 8601 string parsing tests ---

    #[test]
    fn test_parse_timestamp_epoch_basic() {
        let t1 = parse_timestamp_epoch("2026-03-27T12:00:00Z");
        let t2 = parse_timestamp_epoch("2026-03-27T12:05:00Z");
        assert!(t1.is_some());
        assert!(t2.is_some());
        assert!(t2.unwrap() > t1.unwrap(), "later timestamp should have larger epoch");
    }

    #[test]
    fn test_parse_timestamp_epoch_invalid() {
        assert!(parse_timestamp_epoch("not-a-timestamp").is_none());
        assert!(parse_timestamp_epoch("").is_none());
    }

    #[test]
    fn test_cumulative_month_days_january() {
        assert_eq!(cumulative_month_days(1), 0);
    }

    #[test]
    fn test_cumulative_month_days_december() {
        assert_eq!(cumulative_month_days(12), 334);
    }

    #[test]
    fn test_cumulative_month_days_out_of_range() {
        assert_eq!(cumulative_month_days(0), 0);
        assert_eq!(cumulative_month_days(13), 0);
    }
}
