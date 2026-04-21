// trust-cache: Bloom filter pre-check for fast negative cache lookups.
//
// A Bloom filter is a space-efficient probabilistic data structure that tests
// whether an element is a member of a set. False positives are possible, but
// false negatives are not. This makes it ideal as a fast pre-check before
// expensive hash computations in the verification cache.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::f64;

/// Configuration for constructing a Bloom filter with target parameters.
#[derive(Debug, Clone, PartialEq)]
pub struct BloomConfig {
    /// Expected number of elements to insert.
    pub expected_elements: usize,
    /// Desired false positive rate (0.0..1.0).
    pub false_positive_rate: f64,
}

impl BloomConfig {
    /// Create a new configuration.
    ///
    /// # Panics
    ///
    /// Panics if `expected_elements` is 0 or `false_positive_rate` is not in (0.0, 1.0).
    #[must_use]
    pub fn new(expected_elements: usize, false_positive_rate: f64) -> Self {
        assert!(expected_elements > 0, "expected_elements must be > 0");
        assert!(
            false_positive_rate > 0.0 && false_positive_rate < 1.0,
            "false_positive_rate must be in (0.0, 1.0)"
        );
        Self { expected_elements, false_positive_rate }
    }

    /// Compute optimal bit array size for the given parameters.
    ///
    /// Formula: m = -(n * ln(p)) / (ln(2)^2)
    /// where n = expected elements, p = false positive rate.
    #[must_use]
    pub fn optimal_bit_count(&self) -> usize {
        let n = self.expected_elements as f64;
        let p = self.false_positive_rate;
        let m = -(n * p.ln()) / (f64::consts::LN_2 * f64::consts::LN_2);
        (m.ceil() as usize).max(1)
    }

    /// Compute optimal number of hash functions.
    ///
    /// Formula: k = (m/n) * ln(2)
    /// where m = bit count, n = expected elements.
    #[must_use]
    pub fn optimal_hash_count(&self) -> usize {
        let m = self.optimal_bit_count() as f64;
        let n = self.expected_elements as f64;
        let k = (m / n) * f64::consts::LN_2;
        (k.ceil() as usize).max(1)
    }

    /// Build a `BloomFilter` from this configuration.
    #[must_use]
    pub fn build(&self) -> BloomFilter {
        let bit_count = self.optimal_bit_count();
        let hash_count = self.optimal_hash_count();
        BloomFilter {
            bits: vec![false; bit_count],
            hash_count,
            inserted: 0,
            stats: BloomStats::default(),
        }
    }
}

/// Statistics for Bloom filter usage.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct BloomStats {
    /// Total number of `contains` queries.
    pub queries: u64,
    /// Number of queries that returned `true` (may include false positives).
    pub positive_results: u64,
    /// Number of queries that returned `false` (guaranteed true negatives).
    pub negative_results: u64,
}

impl BloomStats {
    /// Observed positive rate (positives / total queries).
    ///
    /// Returns 0.0 if no queries have been made.
    #[must_use]
    pub fn observed_positive_rate(&self) -> f64 {
        if self.queries == 0 {
            return 0.0;
        }
        self.positive_results as f64 / self.queries as f64
    }
}

/// A Bloom filter for fast set membership pre-checks.
///
/// Uses double hashing (h1 + i*h2) to simulate multiple independent hash
/// functions from two base hashes derived via FNV-1a with different seeds.
#[derive(Debug, Clone)]
pub struct BloomFilter {
    bits: Vec<bool>,
    hash_count: usize,
    inserted: usize,
    stats: BloomStats,
}

impl BloomFilter {
    /// Create a Bloom filter with explicit parameters.
    ///
    /// Prefer `BloomConfig::build()` for automatic optimal parameter selection.
    #[must_use]
    pub fn with_params(bit_count: usize, hash_count: usize) -> Self {
        assert!(bit_count > 0, "bit_count must be > 0");
        assert!(hash_count > 0, "hash_count must be > 0");
        Self {
            bits: vec![false; bit_count],
            hash_count,
            inserted: 0,
            stats: BloomStats::default(),
        }
    }

    /// Insert an element into the filter.
    pub fn insert(&mut self, item: &str) {
        let (h1, h2) = Self::double_hash(item);
        let len = self.bits.len();
        for i in 0..self.hash_count {
            let idx = Self::combined_hash(h1, h2, i, len);
            self.bits[idx] = true;
        }
        self.inserted += 1;
    }

    /// Check if an element might be in the set.
    ///
    /// Returns `false` if the element is definitely not in the set (true negative).
    /// Returns `true` if the element might be in the set (may be a false positive).
    pub fn contains(&mut self, item: &str) -> bool {
        let (h1, h2) = Self::double_hash(item);
        let len = self.bits.len();
        let result = (0..self.hash_count)
            .all(|i| self.bits[Self::combined_hash(h1, h2, i, len)]);
        self.stats.queries += 1;
        if result {
            self.stats.positive_results += 1;
        } else {
            self.stats.negative_results += 1;
        }
        result
    }

    /// Check membership without updating statistics.
    #[must_use]
    pub fn contains_quiet(&self, item: &str) -> bool {
        let (h1, h2) = Self::double_hash(item);
        let len = self.bits.len();
        (0..self.hash_count).all(|i| self.bits[Self::combined_hash(h1, h2, i, len)])
    }

    /// Estimate the current false positive rate given the number of inserted elements.
    ///
    /// Formula: (1 - e^(-kn/m))^k
    /// where k = hash count, n = inserted, m = bit count.
    #[must_use]
    pub fn estimated_false_positive_rate(&self) -> f64 {
        if self.bits.is_empty() || self.inserted == 0 {
            return 0.0;
        }
        let k = self.hash_count as f64;
        let n = self.inserted as f64;
        let m = self.bits.len() as f64;
        (1.0 - (-k * n / m).exp()).powf(k)
    }

    /// Merge another Bloom filter into this one (bitwise OR).
    ///
    /// Both filters must have the same bit count and hash count.
    ///
    /// # Panics
    ///
    /// Panics if the filters have different parameters.
    pub fn merge(&mut self, other: &BloomFilter) {
        assert_eq!(
            self.bits.len(),
            other.bits.len(),
            "cannot merge filters with different bit counts"
        );
        assert_eq!(
            self.hash_count, other.hash_count,
            "cannot merge filters with different hash counts"
        );
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a = *a || *b;
        }
        self.inserted += other.inserted;
    }

    /// Number of elements inserted.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inserted
    }

    /// Whether the filter is empty (no elements inserted).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inserted == 0
    }

    /// Size of the bit array.
    #[must_use]
    pub fn bit_count(&self) -> usize {
        self.bits.len()
    }

    /// Number of hash functions used.
    #[must_use]
    pub fn hash_count(&self) -> usize {
        self.hash_count
    }

    /// Current usage statistics.
    #[must_use]
    pub fn stats(&self) -> &BloomStats {
        &self.stats
    }

    /// Reset statistics counters.
    pub fn reset_stats(&mut self) {
        self.stats = BloomStats::default();
    }

    /// Clear the filter, removing all elements.
    pub fn clear(&mut self) {
        self.bits.fill(false);
        self.inserted = 0;
        self.stats = BloomStats::default();
    }

    /// Fraction of bits that are set.
    #[must_use]
    pub fn fill_ratio(&self) -> f64 {
        if self.bits.is_empty() {
            return 0.0;
        }
        let set_bits = self.bits.iter().filter(|&&b| b).count();
        set_bits as f64 / self.bits.len() as f64
    }

    // -- internal hashing ---------------------------------------------------

    /// FNV-1a hash with a given seed offset.
    fn fnv1a(data: &[u8], seed: u64) -> u64 {
        let mut hash: u64 = 0xcbf29ce484222325_u64.wrapping_add(seed);
        for &byte in data {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }

    /// Produce two independent hashes for double hashing.
    fn double_hash(item: &str) -> (u64, u64) {
        let bytes = item.as_bytes();
        let h1 = Self::fnv1a(bytes, 0);
        let h2 = Self::fnv1a(bytes, 0x517cc1b727220a95);
        (h1, h2)
    }

    /// Combine two hashes for the i-th hash function: (h1 + i*h2) % len.
    fn combined_hash(h1: u64, h2: u64, i: usize, len: usize) -> usize {
        (h1.wrapping_add((i as u64).wrapping_mul(h2)) % len as u64) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // BloomConfig tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_config_optimal_params_reasonable() {
        let cfg = BloomConfig::new(1000, 0.01);
        let bits = cfg.optimal_bit_count();
        let hashes = cfg.optimal_hash_count();
        // For n=1000, p=0.01: m ~ 9585, k ~ 7
        assert!(bits > 5000 && bits < 15000, "bits={bits} out of expected range");
        assert!((5..=10).contains(&hashes), "hashes={hashes} out of expected range");
    }

    #[test]
    fn test_bloom_config_build_creates_filter() {
        let cfg = BloomConfig::new(100, 0.05);
        let filter = cfg.build();
        assert!(filter.is_empty());
        assert_eq!(filter.len(), 0);
        assert!(filter.bit_count() > 0);
        assert!(filter.hash_count() > 0);
    }

    #[test]
    #[should_panic(expected = "expected_elements must be > 0")]
    fn test_bloom_config_zero_elements_panics() {
        let _ = BloomConfig::new(0, 0.01);
    }

    #[test]
    #[should_panic(expected = "false_positive_rate must be in (0.0, 1.0)")]
    fn test_bloom_config_invalid_fpr_panics() {
        let _ = BloomConfig::new(100, 1.0);
    }

    // -----------------------------------------------------------------------
    // Insert and contains tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_insert_then_contains() {
        let mut bf = BloomConfig::new(100, 0.01).build();
        bf.insert("foo::bar");
        bf.insert("baz::qux");

        assert!(bf.contains("foo::bar"), "inserted element must be found");
        assert!(bf.contains("baz::qux"), "inserted element must be found");
        assert_eq!(bf.len(), 2);
    }

    #[test]
    fn test_bloom_no_false_negatives() {
        // Insert many elements and verify all are found -- Bloom filters
        // guarantee no false negatives.
        let mut bf = BloomConfig::new(500, 0.01).build();
        let items: Vec<String> = (0..200).map(|i| format!("fn_{i}")).collect();
        for item in &items {
            bf.insert(item);
        }
        for item in &items {
            assert!(bf.contains(item), "false negative for {item}");
        }
    }

    #[test]
    fn test_bloom_likely_negative_for_absent() {
        let mut bf = BloomConfig::new(100, 0.001).build();
        bf.insert("present_item");

        // Test several absent items -- with 0.1% FPR, most should be negative
        let absent = ["absent_1", "absent_2", "absent_3", "absent_4", "absent_5"];
        let negatives = absent.iter().filter(|item| !bf.contains(item)).count();
        assert!(negatives >= 4, "expected most absent items to return false, got {negatives}/5");
    }

    #[test]
    fn test_bloom_empty_filter_contains_nothing() {
        let mut bf = BloomConfig::new(100, 0.01).build();
        assert!(!bf.contains("anything"));
        assert!(!bf.contains(""));
        assert!(bf.is_empty());
    }

    // -----------------------------------------------------------------------
    // Statistics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_stats_tracking() {
        let mut bf = BloomConfig::new(100, 0.01).build();
        bf.insert("a");
        bf.contains("a"); // positive
        bf.contains("b"); // likely negative

        let stats = bf.stats();
        assert_eq!(stats.queries, 2);
        assert_eq!(stats.positive_results + stats.negative_results, 2);
    }

    #[test]
    fn test_bloom_stats_observed_rate_no_queries() {
        let stats = BloomStats::default();
        assert_eq!(stats.observed_positive_rate(), 0.0);
    }

    // -----------------------------------------------------------------------
    // Merge tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_merge_combines_elements() {
        let mut bf1 = BloomFilter::with_params(1000, 5);
        let mut bf2 = BloomFilter::with_params(1000, 5);

        bf1.insert("alpha");
        bf2.insert("beta");

        bf1.merge(&bf2);

        assert!(bf1.contains("alpha"), "original element must survive merge");
        assert!(bf1.contains("beta"), "merged element must be found");
        assert_eq!(bf1.len(), 2);
    }

    #[test]
    #[should_panic(expected = "cannot merge filters with different bit counts")]
    fn test_bloom_merge_incompatible_panics() {
        let mut bf1 = BloomFilter::with_params(100, 3);
        let bf2 = BloomFilter::with_params(200, 3);
        bf1.merge(&bf2);
    }

    // -----------------------------------------------------------------------
    // False positive rate estimation
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_estimated_fpr_increases_with_inserts() {
        let mut bf = BloomConfig::new(1000, 0.01).build();
        let fpr_empty = bf.estimated_false_positive_rate();
        assert_eq!(fpr_empty, 0.0, "empty filter should have 0 FPR");

        for i in 0..100 {
            bf.insert(&format!("item_{i}"));
        }
        let fpr_100 = bf.estimated_false_positive_rate();

        for i in 100..500 {
            bf.insert(&format!("item_{i}"));
        }
        let fpr_500 = bf.estimated_false_positive_rate();

        assert!(fpr_500 > fpr_100, "FPR should increase: {fpr_100} vs {fpr_500}");
    }

    // -----------------------------------------------------------------------
    // Clear and fill ratio
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_clear_resets() {
        let mut bf = BloomConfig::new(100, 0.01).build();
        bf.insert("something");
        bf.contains("something");
        assert!(!bf.is_empty());

        bf.clear();
        assert!(bf.is_empty());
        assert_eq!(bf.len(), 0);
        assert_eq!(bf.stats().queries, 0);
        assert!(!bf.contains_quiet("something"), "cleared filter should not contain anything");
    }

    #[test]
    fn test_bloom_fill_ratio() {
        let mut bf = BloomFilter::with_params(100, 3);
        assert_eq!(bf.fill_ratio(), 0.0);

        bf.insert("x");
        let ratio = bf.fill_ratio();
        assert!(ratio > 0.0 && ratio <= 1.0, "fill ratio should be in (0, 1], got {ratio}");
    }

    // -----------------------------------------------------------------------
    // contains_quiet does not affect stats
    // -----------------------------------------------------------------------

    #[test]
    fn test_bloom_contains_quiet_no_stats() {
        let mut bf = BloomConfig::new(100, 0.01).build();
        bf.insert("item");
        let _ = bf.contains_quiet("item");
        let _ = bf.contains_quiet("other");
        assert_eq!(bf.stats().queries, 0, "contains_quiet must not update stats");
    }
}
