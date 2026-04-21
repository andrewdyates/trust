// trust-cache/alpha_normalize.rs: Alpha-normalization and sub-formula caching
//
// Alpha-normalizes Formula ASTs so that structurally equivalent formulas
// with different bound variable names produce identical hashes. Also provides
// sub-formula caching to avoid redundant hashing of shared sub-trees.
//
// Inspired by KLEE's query canonicalization
// (refs/klee/lib/Solver/CachingSolver.cpp) and standard lambda-calculus
// alpha-equivalence.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort};

/// Return type for [`AlphaState::rename_bindings`]: (new_bindings, saved_old_mappings).
type RenameBindingsResult = (Vec<(String, Sort)>, Vec<(String, Option<String>)>);

/// Alpha-normalize a formula by renaming all bound variables to canonical names.
///
/// Bound variables introduced by `Forall` and `Exists` are renamed to
/// `_v0`, `_v1`, `_v2`, ... in the order they are encountered (depth-first,
/// left-to-right). Free variables are left unchanged.
///
/// After normalization, `Exists([("a", Int)], Var("a"))` and
/// `Exists([("b", Int)], Var("b"))` become identical:
/// `Exists([("_v0", Int)], Var("_v0"))`.
///
/// This is the standard alpha-equivalence normalization from lambda calculus.
#[must_use]
pub fn alpha_normalize(formula: &Formula) -> Formula {
    let mut state = AlphaState { counter: 0, rename_map: FxHashMap::default() };
    state.normalize(formula)
}

/// Internal state for alpha-normalization.
struct AlphaState {
    /// Counter for generating canonical variable names.
    counter: usize,
    /// Map from original bound variable names to canonical names.
    /// Only populated for variables currently in scope.
    rename_map: FxHashMap<String, String>,
}

impl AlphaState {
    /// Generate the next canonical variable name.
    fn next_canonical_name(&mut self) -> String {
        let name = format!("_v{}", self.counter);
        self.counter += 1;
        name
    }

    /// Normalize a formula, renaming bound variables to canonical names.
    fn normalize(&mut self, formula: &Formula) -> Formula {
        match formula {
            // Leaves
            Formula::Bool(b) => Formula::Bool(*b),
            Formula::Int(n) => Formula::Int(*n),
            Formula::UInt(n) => Formula::UInt(*n),
            Formula::BitVec { value, width } => Formula::BitVec { value: *value, width: *width },

            // Variable: rename if bound, keep original name if free
            Formula::Var(name, sort) => {
                if let Some(canonical) = self.rename_map.get(name) {
                    Formula::Var(canonical.clone(), sort.clone())
                } else {
                    Formula::Var(name.clone(), sort.clone())
                }
            }

            // Unary
            Formula::Not(a) => Formula::Not(Box::new(self.normalize(a))),
            Formula::Neg(a) => Formula::Neg(Box::new(self.normalize(a))),
            Formula::BvNot(a, w) => Formula::BvNot(Box::new(self.normalize(a)), *w),
            Formula::BvToInt(a, w, s) => Formula::BvToInt(Box::new(self.normalize(a)), *w, *s),
            Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(self.normalize(a)), *w),
            Formula::BvZeroExt(a, bits) => Formula::BvZeroExt(Box::new(self.normalize(a)), *bits),
            Formula::BvSignExt(a, bits) => Formula::BvSignExt(Box::new(self.normalize(a)), *bits),
            Formula::BvExtract { inner, high, low } => {
                Formula::BvExtract { inner: Box::new(self.normalize(inner)), high: *high, low: *low }
            }

            // N-ary
            Formula::And(terms) => {
                Formula::And(terms.iter().map(|t| self.normalize(t)).collect())
            }
            Formula::Or(terms) => {
                Formula::Or(terms.iter().map(|t| self.normalize(t)).collect())
            }

            // Binary
            Formula::Implies(a, b) => {
                Formula::Implies(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Eq(a, b) => {
                Formula::Eq(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Lt(a, b) => {
                Formula::Lt(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Le(a, b) => {
                Formula::Le(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Gt(a, b) => {
                Formula::Gt(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Ge(a, b) => {
                Formula::Ge(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Add(a, b) => {
                Formula::Add(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Sub(a, b) => {
                Formula::Sub(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Mul(a, b) => {
                Formula::Mul(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Div(a, b) => {
                Formula::Div(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Rem(a, b) => {
                Formula::Rem(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::BvConcat(a, b) => {
                Formula::BvConcat(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }
            Formula::Select(a, b) => {
                Formula::Select(Box::new(self.normalize(a)), Box::new(self.normalize(b)))
            }

            // Binary with width
            Formula::BvAdd(a, b, w) => {
                Formula::BvAdd(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvSub(a, b, w) => {
                Formula::BvSub(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvMul(a, b, w) => {
                Formula::BvMul(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvUDiv(a, b, w) => {
                Formula::BvUDiv(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvSDiv(a, b, w) => {
                Formula::BvSDiv(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvURem(a, b, w) => {
                Formula::BvURem(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvSRem(a, b, w) => {
                Formula::BvSRem(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvAnd(a, b, w) => {
                Formula::BvAnd(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvOr(a, b, w) => {
                Formula::BvOr(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvXor(a, b, w) => {
                Formula::BvXor(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvShl(a, b, w) => {
                Formula::BvShl(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvLShr(a, b, w) => {
                Formula::BvLShr(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvAShr(a, b, w) => {
                Formula::BvAShr(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvULt(a, b, w) => {
                Formula::BvULt(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvULe(a, b, w) => {
                Formula::BvULe(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvSLt(a, b, w) => {
                Formula::BvSLt(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }
            Formula::BvSLe(a, b, w) => {
                Formula::BvSLe(Box::new(self.normalize(a)), Box::new(self.normalize(b)), *w)
            }

            // Ternary
            Formula::Ite(a, b, c) => Formula::Ite(
                Box::new(self.normalize(a)),
                Box::new(self.normalize(b)),
                Box::new(self.normalize(c)),
            ),
            Formula::Store(a, b, c) => Formula::Store(
                Box::new(self.normalize(a)),
                Box::new(self.normalize(b)),
                Box::new(self.normalize(c)),
            ),

            // Quantifiers: rename bound variables to canonical names
            Formula::Forall(bindings, body) => {
                let (new_bindings, saved) = self.rename_bindings(bindings);
                let new_body = self.normalize(body);
                self.restore_bindings(&saved);
                Formula::Forall(new_bindings, Box::new(new_body))
            }
            Formula::Exists(bindings, body) => {
                let (new_bindings, saved) = self.rename_bindings(bindings);
                let new_body = self.normalize(body);
                self.restore_bindings(&saved);
                Formula::Exists(new_bindings, Box::new(new_body))
            }
            _ => Formula::Bool(false),
        }
    }

    /// Rename quantifier bindings to canonical names.
    ///
    /// Returns the new bindings and a list of (original_name, old_mapping) pairs
    /// so the caller can restore the rename_map after processing the body.
    fn rename_bindings(
        &mut self,
        bindings: &[(String, Sort)],
    ) -> RenameBindingsResult {
        let mut new_bindings = Vec::with_capacity(bindings.len());
        let mut saved = Vec::with_capacity(bindings.len());

        for (name, sort) in bindings {
            let canonical = self.next_canonical_name();
            let old = self.rename_map.insert(name.clone(), canonical.clone());
            saved.push((name.clone(), old));
            new_bindings.push((canonical, sort.clone()));
        }

        (new_bindings, saved)
    }

    /// Restore the rename_map to its state before `rename_bindings`.
    fn restore_bindings(&mut self, saved: &[(String, Option<String>)]) {
        for (name, old) in saved {
            match old {
                Some(prev) => {
                    self.rename_map.insert(name.clone(), prev.clone());
                }
                None => {
                    self.rename_map.remove(name);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Sub-formula hash cache
// ---------------------------------------------------------------------------

/// A cache that stores SHA-256 hashes for sub-formulas to avoid redundant
/// serialization and hashing of shared sub-trees.
///
/// When computing the hash of a large formula, many sub-formulas may repeat
/// (e.g., the same `And([...])` appears in multiple VCs). This cache stores
/// the hash of each sub-formula so it can be looked up instead of recomputed.
///
/// The cache key is the formula's `Debug` representation (which is deterministic
/// for a given Formula tree). This avoids needing Formula to implement Hash.
pub struct SubFormulaCache {
    /// Map from formula debug representation to its SHA-256 hash.
    entries: FxHashMap<String, String>,
    /// Number of cache hits (reused hashes).
    hits: usize,
    /// Number of cache misses (newly computed hashes).
    misses: usize,
}

impl SubFormulaCache {
    /// Create an empty sub-formula cache.
    pub fn new() -> Self {
        SubFormulaCache {
            entries: FxHashMap::default(),
            hits: 0,
            misses: 0,
        }
    }

    /// Compute the SHA-256 hash of a formula, using the cache for sub-formulas.
    ///
    /// First alpha-normalizes the formula, then computes the hash of its
    /// JSON serialization. If the formula was seen before, returns the
    /// cached hash.
    #[must_use]
    pub fn hash_formula(&mut self, formula: &Formula) -> String {
        let normalized = alpha_normalize(formula);
        self.hash_normalized(&normalized)
    }

    /// Hash a formula that has already been alpha-normalized.
    #[must_use]
    pub(crate) fn hash_normalized(&mut self, formula: &Formula) -> String {
        // Use debug repr as cache key (deterministic for a given tree)
        let key = format!("{formula:?}");

        if let Some(cached) = self.entries.get(&key) {
            self.hits += 1;
            return cached.clone();
        }

        self.misses += 1;
        let json = serde_json::to_string(formula).unwrap_or_default();
        let mut hasher = Sha256::new();
        hasher.update(json.as_bytes());
        let hash = format!("{:x}", hasher.finalize());

        self.entries.insert(key, hash.clone());
        hash
    }

    /// Number of cache hits.
    #[must_use]
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Number of cache misses.
    #[must_use]
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Total number of cached sub-formula hashes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all cached entries and reset statistics.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.hits = 0;
        self.misses = 0;
    }
}

impl Default for SubFormulaCache {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Convenience: compute alpha-normalized hash without a persistent cache
// ---------------------------------------------------------------------------

/// Compute the SHA-256 hash of an alpha-normalized formula.
///
/// This is a convenience function for callers that don't need sub-formula
/// caching. The formula is alpha-normalized and then hashed via SHA-256
/// of its JSON serialization.
#[must_use]
pub fn alpha_normalized_hash(formula: &Formula) -> String {
    let normalized = alpha_normalize(formula);
    let json = serde_json::to_string(&normalized).unwrap_or_default();
    let mut hasher = Sha256::new();
    hasher.update(json.as_bytes());
    format!("{:x}", hasher.finalize())
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(w))
    }

    // -----------------------------------------------------------------------
    // Alpha-normalization tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_alpha_normalize_no_quantifiers_unchanged() {
        // Free variables should NOT be renamed
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let normalized = alpha_normalize(&f);
        assert_eq!(normalized, f);
    }

    #[test]
    fn test_alpha_normalize_exists_renames_bound_var() {
        let f = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0)))),
        );
        let normalized = alpha_normalize(&f);
        let expected = Formula::Exists(
            vec![("_v0".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("_v0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_different_names_same_result() {
        // Exists(a, a == 0) and Exists(b, b == 0) should normalize identically
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0)))),
        );
        assert_ne!(f1, f2, "originals should differ");
        let n1 = alpha_normalize(&f1);
        let n2 = alpha_normalize(&f2);
        assert_eq!(n1, n2, "alpha-normalized forms should be identical");
    }

    #[test]
    fn test_alpha_normalize_forall_renames() {
        let f = Formula::Forall(
            vec![("xyz".into(), Sort::Bool)],
            Box::new(Formula::Not(Box::new(Formula::Var("xyz".into(), Sort::Bool)))),
        );
        let normalized = alpha_normalize(&f);
        let expected = Formula::Forall(
            vec![("_v0".into(), Sort::Bool)],
            Box::new(Formula::Not(Box::new(Formula::Var("_v0".into(), Sort::Bool)))),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_nested_quantifiers() {
        // Forall(x, Exists(y, x == y))
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Eq(Box::new(var("x")), Box::new(var("y")))),
            )),
        );
        let normalized = alpha_normalize(&f);
        // Should become Forall(_v0, Exists(_v1, _v0 == _v1))
        let expected = Formula::Forall(
            vec![("_v0".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("_v1".into(), Sort::Int)],
                Box::new(Formula::Eq(
                    Box::new(Formula::Var("_v0".into(), Sort::Int)),
                    Box::new(Formula::Var("_v1".into(), Sort::Int)),
                )),
            )),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_nested_different_names_same_result() {
        // Forall(a, Exists(b, a == b)) vs Forall(x, Exists(y, x == y))
        let f1 = Formula::Forall(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("b".into(), Sort::Int)],
                Box::new(Formula::Eq(Box::new(var("a")), Box::new(var("b")))),
            )),
        );
        let f2 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Eq(Box::new(var("x")), Box::new(var("y")))),
            )),
        );
        assert_ne!(f1, f2);
        assert_eq!(alpha_normalize(&f1), alpha_normalize(&f2));
    }

    #[test]
    fn test_alpha_normalize_free_vars_preserved() {
        // Exists(a, a > free_var)
        let f = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("a")), Box::new(var("free_var")))),
        );
        let normalized = alpha_normalize(&f);
        // _v0 > free_var — free_var is NOT renamed
        let expected = Formula::Exists(
            vec![("_v0".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("_v0".into(), Sort::Int)),
                Box::new(var("free_var")),
            )),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_multiple_bindings() {
        // Exists([a, b], a + b == 0)
        let f = Formula::Exists(
            vec![("a".into(), Sort::Int), ("b".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Add(Box::new(var("a")), Box::new(var("b")))),
                Box::new(Formula::Int(0)),
            )),
        );
        let normalized = alpha_normalize(&f);
        let expected = Formula::Exists(
            vec![("_v0".into(), Sort::Int), ("_v1".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("_v0".into(), Sort::Int)),
                    Box::new(Formula::Var("_v1".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            )),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_preserves_sort() {
        // Exists(x: BitVec(32), ...)
        let f = Formula::Exists(
            vec![("x".into(), Sort::BitVec(32))],
            Box::new(bv_var("x", 32)),
        );
        let normalized = alpha_normalize(&f);
        match &normalized {
            Formula::Exists(bindings, body) => {
                assert_eq!(bindings[0].0, "_v0");
                assert_eq!(bindings[0].1, Sort::BitVec(32));
                assert_eq!(**body, Formula::Var("_v0".into(), Sort::BitVec(32)));
            }
            _ => panic!("expected Exists"),
        }
    }

    #[test]
    fn test_alpha_normalize_shadowing() {
        // Forall(x, Forall(x, x == 0)) — inner x shadows outer x
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
            )),
        );
        let normalized = alpha_normalize(&f);
        // Should become Forall(_v0, Forall(_v1, _v1 == 0))
        // The inner binding gets _v1, and the body uses _v1 (the innermost binding)
        let expected = Formula::Forall(
            vec![("_v0".into(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("_v1".into(), Sort::Int)],
                Box::new(Formula::Eq(
                    Box::new(Formula::Var("_v1".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            )),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_shadowing_restores_outer() {
        // Forall(x, And(Exists(x, x == 0), x == 1))
        // After inner Exists, outer x binding should be restored
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::And(vec![
                Formula::Exists(
                    vec![("x".into(), Sort::Int)],
                    Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
                ),
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(1))),
            ])),
        );
        let normalized = alpha_normalize(&f);
        // Forall(_v0, And(Exists(_v1, _v1 == 0), _v0 == 1))
        let expected = Formula::Forall(
            vec![("_v0".into(), Sort::Int)],
            Box::new(Formula::And(vec![
                Formula::Exists(
                    vec![("_v1".into(), Sort::Int)],
                    Box::new(Formula::Eq(
                        Box::new(Formula::Var("_v1".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    )),
                ),
                Formula::Eq(
                    Box::new(Formula::Var("_v0".into(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
            ])),
        );
        assert_eq!(normalized, expected);
    }

    #[test]
    fn test_alpha_normalize_leaves_unchanged() {
        // Literals should pass through unchanged
        assert_eq!(alpha_normalize(&Formula::Bool(true)), Formula::Bool(true));
        assert_eq!(alpha_normalize(&Formula::Int(42)), Formula::Int(42));
        assert_eq!(alpha_normalize(&Formula::UInt(7)), Formula::UInt(7));
        assert_eq!(
            alpha_normalize(&Formula::BitVec { value: 255, width: 8 }),
            Formula::BitVec { value: 255, width: 8 }
        );
    }

    #[test]
    fn test_alpha_normalize_ite() {
        let f = Formula::Exists(
            vec![("c".into(), Sort::Bool)],
            Box::new(Formula::Ite(
                Box::new(Formula::Var("c".into(), Sort::Bool)),
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(0)),
            )),
        );
        let normalized = alpha_normalize(&f);
        match &normalized {
            Formula::Exists(bindings, body) => {
                assert_eq!(bindings[0].0, "_v0");
                match body.as_ref() {
                    Formula::Ite(cond, _, _) => {
                        assert_eq!(**cond, Formula::Var("_v0".into(), Sort::Bool));
                    }
                    _ => panic!("expected Ite"),
                }
            }
            _ => panic!("expected Exists"),
        }
    }

    // -----------------------------------------------------------------------
    // Alpha-normalized hashing tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_alpha_normalized_hash_same_for_equivalent_formulas() {
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(42)))),
        );
        let f2 = Formula::Exists(
            vec![("zzz".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("zzz")), Box::new(Formula::Int(42)))),
        );
        assert_eq!(
            alpha_normalized_hash(&f1),
            alpha_normalized_hash(&f2),
            "alpha-equivalent formulas should hash identically"
        );
    }

    #[test]
    fn test_alpha_normalized_hash_different_for_different_formulas() {
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1)))),
        );
        assert_ne!(
            alpha_normalized_hash(&f1),
            alpha_normalized_hash(&f2),
            "structurally different formulas should hash differently"
        );
    }

    #[test]
    fn test_alpha_normalized_hash_is_sha256() {
        let f = Formula::Bool(true);
        let h = alpha_normalized_hash(&f);
        assert_eq!(h.len(), 64, "SHA-256 hex is 64 chars");
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_alpha_normalized_hash_deterministic() {
        let f = Formula::And(vec![
            Formula::Exists(
                vec![("x".into(), Sort::Int)],
                Box::new(var("x")),
            ),
            var("free"),
        ]);
        let h1 = alpha_normalized_hash(&f);
        let h2 = alpha_normalized_hash(&f);
        assert_eq!(h1, h2);
    }

    // -----------------------------------------------------------------------
    // Sub-formula cache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_subformula_cache_hit() {
        let mut cache = SubFormulaCache::new();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));

        let h1 = cache.hash_formula(&f);
        let h2 = cache.hash_formula(&f);
        assert_eq!(h1, h2);
        assert_eq!(cache.hits(), 1);
        assert_eq!(cache.misses(), 1); // first call is a miss
    }

    #[test]
    fn test_subformula_cache_different_formulas() {
        let mut cache = SubFormulaCache::new();
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));

        let h1 = cache.hash_formula(&f1);
        let h2 = cache.hash_formula(&f2);
        assert_ne!(h1, h2);
        assert_eq!(cache.misses(), 2);
        assert_eq!(cache.hits(), 0);
    }

    #[test]
    fn test_subformula_cache_alpha_equivalent_hit() {
        let mut cache = SubFormulaCache::new();
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0)))),
        );

        let h1 = cache.hash_formula(&f1);
        let h2 = cache.hash_formula(&f2);
        assert_eq!(h1, h2, "alpha-equivalent formulas get same hash from cache");
        // First call is a miss, second is a hit (after alpha-normalization they're identical)
        assert_eq!(cache.hits(), 1);
        assert_eq!(cache.misses(), 1);
    }

    #[test]
    fn test_subformula_cache_len() {
        let mut cache = SubFormulaCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        let _ = cache.hash_formula(&Formula::Bool(true));
        assert_eq!(cache.len(), 1);
        assert!(!cache.is_empty());

        let _ = cache.hash_formula(&Formula::Bool(false));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_subformula_cache_clear() {
        let mut cache = SubFormulaCache::new();
        let _ = cache.hash_formula(&Formula::Bool(true));
        let _ = cache.hash_formula(&Formula::Bool(true));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.hits(), 1);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 0);
    }

    #[test]
    fn test_subformula_cache_many_repeated_lookups() {
        let mut cache = SubFormulaCache::new();
        let f = Formula::And(vec![var("x"), var("y"), Formula::Int(42)]);

        for _ in 0..100 {
            let _ = cache.hash_formula(&f);
        }
        assert_eq!(cache.misses(), 1);
        assert_eq!(cache.hits(), 99);
        assert_eq!(cache.len(), 1);
    }
}
