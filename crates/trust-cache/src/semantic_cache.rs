// trust-cache/semantic_cache.rs: Semantic counterexample caching
//
// Matches counterexamples by structural formula similarity rather than exact
// match. Enables reuse of counterexamples across similar functions and versions
// by alpha-renaming variables and comparing normalized formula structure.
//
// Inspired by KLEE's CexCachingSolver with added semantic matching.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use sha2::{Digest, Sha256};
use trust_types::{Counterexample, Formula, Sort, VerificationCondition, VerificationResult};

/// A normalized formula with variables alpha-renamed to canonical positions.
///
/// Two formulas that differ only in variable names will produce the same
/// `NormalizedFormula`, enabling structural comparison across functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizedFormula {
    /// The formula with all variables renamed to positional names (v0, v1, ...).
    pub formula: Formula,
    /// Mapping from original variable names to canonical names.
    pub var_map: Vec<(String, String)>,
}

/// A fingerprint of a normalized formula for fast HashMap lookup.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SemanticKey {
    /// SHA-256 hex digest of the canonical serde_json serialization.
    pub fingerprint: String,
}

/// Cached verification result with its semantic key.
#[derive(Debug, Clone)]
pub struct CachedResult {
    /// The original verification condition's function name.
    pub source_function: String,
    /// The verification result (typically Failed with counterexample).
    pub result: VerificationResult,
    /// Similarity score at time of insertion (1.0 for exact structural match).
    pub similarity: f64,
}

/// Semantic cache: stores and retrieves counterexamples by structural formula shape.
///
/// Unlike exact-match caching, this allows reuse when variable names differ
/// but the formula structure is identical or sufficiently similar.
pub struct SemanticCache {
    /// Exact structural matches (alpha-renamed equality).
    exact: FxHashMap<SemanticKey, CachedResult>,
    /// All entries for approximate matching, stored with their normalized forms.
    entries: Vec<(NormalizedFormula, CachedResult)>,
    hits: usize,
    misses: usize,
}

impl SemanticCache {
    /// Create an empty semantic cache.
    pub fn new() -> Self {
        SemanticCache {
            exact: FxHashMap::default(),
            entries: Vec::new(),
            hits: 0,
            misses: 0,
        }
    }

    /// Insert a verification result keyed by the VC's formula.
    pub fn insert(&mut self, vc: &VerificationCondition, result: VerificationResult) {
        let normalized = normalize_formula(&vc.formula);
        let key = semantic_key(&normalized);
        let cached = CachedResult {
            source_function: vc.function.clone(),
            result,
            similarity: 1.0,
        };
        self.exact.insert(key, cached.clone());
        self.entries.push((normalized, cached));
    }

    /// Look up by exact structural match (alpha-renamed equality).
    ///
    /// This is O(1) via the HashMap and is tried first.
    pub fn lookup_exact(&mut self, vc: &VerificationCondition) -> Option<&CachedResult> {
        let normalized = normalize_formula(&vc.formula);
        let key = semantic_key(&normalized);
        match self.exact.get(&key) {
            Some(result) => {
                self.hits += 1;
                Some(result)
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Look up by structural similarity, returning the best match above threshold.
    ///
    /// Scans all entries and returns the one with the highest similarity score
    /// that exceeds `threshold`. Falls back to exact match first.
    #[must_use]
    pub fn lookup_similar(
        &mut self,
        vc: &VerificationCondition,
        threshold: f64,
    ) -> Option<CachedResult> {
        let normalized = normalize_formula(&vc.formula);
        let key = semantic_key(&normalized);

        // Try exact match first (O(1))
        if let Some(result) = self.exact.get(&key) {
            self.hits += 1;
            return Some(result.clone());
        }

        // Scan for approximate match
        let mut best_score = 0.0_f64;
        let mut best_idx = None;

        for (i, (entry_norm, _)) in self.entries.iter().enumerate() {
            let score = similarity_score(&normalized, entry_norm);
            if score > best_score && score >= threshold {
                best_score = score;
                best_idx = Some(i);
            }
        }

        match best_idx {
            Some(idx) => {
                self.hits += 1;
                let (_, cached) = &self.entries[idx];
                Some(CachedResult {
                    source_function: cached.source_function.clone(),
                    result: cached.result.clone(),
                    similarity: best_score,
                })
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Number of cached entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
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

    /// Clear all entries and reset statistics.
    pub fn clear(&mut self) {
        self.exact.clear();
        self.entries.clear();
        self.hits = 0;
        self.misses = 0;
    }
}

impl Default for SemanticCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Normalize a formula by alpha-renaming all variables to positional canonical names.
///
/// Variables are renamed in order of first appearance during a depth-first traversal:
/// the first variable seen becomes `v0`, the second `v1`, etc. Sort information is
/// preserved. This makes structurally identical formulas with different variable names
/// compare as equal.
#[must_use]
pub(crate) fn normalize_formula(formula: &Formula) -> NormalizedFormula {
    let mut renamer = AlphaRenamer::new();
    let normalized = renamer.rename(formula);
    NormalizedFormula {
        formula: normalized,
        var_map: renamer.mapping,
    }
}

/// Compute a semantic key (SHA-256 fingerprint) for a normalized formula.
#[must_use]
pub(crate) fn semantic_key(normalized: &NormalizedFormula) -> SemanticKey {
    let json = serde_json::to_string(&normalized.formula).unwrap_or_default();
    let mut hasher = Sha256::new();
    hasher.update(json.as_bytes());
    SemanticKey {
        fingerprint: format!("{:x}", hasher.finalize()),
    }
}

/// Compute a structural similarity score between two normalized formulas.
///
/// Returns a value in `[0.0, 1.0]` where 1.0 means identical structure.
/// The score is based on the ratio of matching AST nodes to total AST nodes.
#[must_use]
pub fn similarity_score(a: &NormalizedFormula, b: &NormalizedFormula) -> f64 {
    if a.formula == b.formula {
        return 1.0;
    }

    let size_a = formula_size(&a.formula);
    let size_b = formula_size(&b.formula);
    if size_a == 0 && size_b == 0 {
        return 1.0;
    }

    let common = common_nodes(&a.formula, &b.formula);
    let max_size = size_a.max(size_b);
    if max_size == 0 {
        return 0.0;
    }

    common as f64 / max_size as f64
}

/// Count the number of AST nodes in a formula.
fn formula_size(f: &Formula) -> usize {
    match f {
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } | Formula::Var(_, _) => 1,

        Formula::Not(inner) | Formula::Neg(inner) | Formula::BvNot(inner, _) => {
            1 + formula_size(inner)
        }

        Formula::And(children) | Formula::Or(children) => {
            1 + children.iter().map(formula_size).sum::<usize>()
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
        | Formula::Rem(a, b)
        | Formula::Select(a, b)
        | Formula::BvConcat(a, b) => 1 + formula_size(a) + formula_size(b),

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
        | Formula::BvSLe(a, b, _) => 1 + formula_size(a) + formula_size(b),

        Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => 1 + formula_size(inner),

        Formula::BvExtract { inner, .. } => 1 + formula_size(inner),

        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            1 + formula_size(c) + formula_size(t) + formula_size(e)
        }

        Formula::Forall(_, body) | Formula::Exists(_, body) => 1 + formula_size(body),
        _ => 0,
    }
}

/// Count the number of structurally matching nodes between two formulas.
fn common_nodes(a: &Formula, b: &Formula) -> usize {
    match (a, b) {
        // Leaf nodes: match if identical
        (Formula::Bool(x), Formula::Bool(y)) if x == y => 1,
        (Formula::Int(x), Formula::Int(y)) if x == y => 1,
        (Formula::BitVec { value: v1, width: w1 }, Formula::BitVec { value: v2, width: w2 })
            if v1 == v2 && w1 == w2 =>
        {
            1
        }
        // Variables: match if sort is the same (names already canonical after normalization)
        (Formula::Var(n1, s1), Formula::Var(n2, s2)) if n1 == n2 && s1 == s2 => 1,

        // Unary operators: 1 for matching constructor + recurse
        (Formula::Not(a), Formula::Not(b)) | (Formula::Neg(a), Formula::Neg(b)) => {
            1 + common_nodes(a, b)
        }
        (Formula::BvNot(a, w1), Formula::BvNot(b, w2)) if w1 == w2 => 1 + common_nodes(a, b),

        // N-ary: match constructor + pairwise children
        (Formula::And(ca), Formula::And(cb)) | (Formula::Or(ca), Formula::Or(cb)) => {
            1 + ca.iter().zip(cb.iter()).map(|(x, y)| common_nodes(x, y)).sum::<usize>()
        }

        // Binary operators
        (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
        | (Formula::Eq(a1, a2), Formula::Eq(b1, b2))
        | (Formula::Lt(a1, a2), Formula::Lt(b1, b2))
        | (Formula::Le(a1, a2), Formula::Le(b1, b2))
        | (Formula::Gt(a1, a2), Formula::Gt(b1, b2))
        | (Formula::Ge(a1, a2), Formula::Ge(b1, b2))
        | (Formula::Add(a1, a2), Formula::Add(b1, b2))
        | (Formula::Sub(a1, a2), Formula::Sub(b1, b2))
        | (Formula::Mul(a1, a2), Formula::Mul(b1, b2))
        | (Formula::Div(a1, a2), Formula::Div(b1, b2))
        | (Formula::Rem(a1, a2), Formula::Rem(b1, b2))
        | (Formula::Select(a1, a2), Formula::Select(b1, b2))
        | (Formula::BvConcat(a1, a2), Formula::BvConcat(b1, b2)) => {
            1 + common_nodes(a1, b1) + common_nodes(a2, b2)
        }

        // Bitvector binary with width match
        (Formula::BvAdd(a1, a2, w1), Formula::BvAdd(b1, b2, w2))
        | (Formula::BvSub(a1, a2, w1), Formula::BvSub(b1, b2, w2))
        | (Formula::BvMul(a1, a2, w1), Formula::BvMul(b1, b2, w2))
        | (Formula::BvUDiv(a1, a2, w1), Formula::BvUDiv(b1, b2, w2))
        | (Formula::BvSDiv(a1, a2, w1), Formula::BvSDiv(b1, b2, w2))
        | (Formula::BvURem(a1, a2, w1), Formula::BvURem(b1, b2, w2))
        | (Formula::BvSRem(a1, a2, w1), Formula::BvSRem(b1, b2, w2))
        | (Formula::BvAnd(a1, a2, w1), Formula::BvAnd(b1, b2, w2))
        | (Formula::BvOr(a1, a2, w1), Formula::BvOr(b1, b2, w2))
        | (Formula::BvXor(a1, a2, w1), Formula::BvXor(b1, b2, w2))
        | (Formula::BvShl(a1, a2, w1), Formula::BvShl(b1, b2, w2))
        | (Formula::BvLShr(a1, a2, w1), Formula::BvLShr(b1, b2, w2))
        | (Formula::BvAShr(a1, a2, w1), Formula::BvAShr(b1, b2, w2))
        | (Formula::BvULt(a1, a2, w1), Formula::BvULt(b1, b2, w2))
        | (Formula::BvULe(a1, a2, w1), Formula::BvULe(b1, b2, w2))
        | (Formula::BvSLt(a1, a2, w1), Formula::BvSLt(b1, b2, w2))
        | (Formula::BvSLe(a1, a2, w1), Formula::BvSLe(b1, b2, w2))
            if w1 == w2 =>
        {
            1 + common_nodes(a1, b1) + common_nodes(a2, b2)
        }

        // Ternary
        (Formula::Ite(c1, t1, e1), Formula::Ite(c2, t2, e2))
        | (Formula::Store(c1, t1, e1), Formula::Store(c2, t2, e2)) => {
            1 + common_nodes(c1, c2) + common_nodes(t1, t2) + common_nodes(e1, e2)
        }

        // Quantifiers: match if same arity and sorts
        (Formula::Forall(vars1, body1), Formula::Forall(vars2, body2))
        | (Formula::Exists(vars1, body1), Formula::Exists(vars2, body2))
            if vars1.len() == vars2.len()
                && vars1
                    .iter()
                    .zip(vars2.iter())
                    .all(|((_, s1), (_, s2))| s1 == s2) =>
        {
            1 + common_nodes(body1, body2)
        }

        // No structural match
        _ => 0,
    }
}

/// Alpha-renamer: renames variables to canonical positional names.
struct AlphaRenamer {
    next_id: usize,
    rename_map: FxHashMap<String, String>,
    /// Ordered mapping: (original_name, canonical_name).
    mapping: Vec<(String, String)>,
}

impl AlphaRenamer {
    fn new() -> Self {
        AlphaRenamer {
            next_id: 0,
            rename_map: FxHashMap::default(),
            mapping: Vec::new(),
        }
    }

    fn canonical_name(&mut self, original: &str) -> String {
        if let Some(name) = self.rename_map.get(original) {
            return name.clone();
        }
        let name = format!("v{}", self.next_id);
        self.next_id += 1;
        self.rename_map.insert(original.to_string(), name.clone());
        self.mapping.push((original.to_string(), name.clone()));
        name
    }

    fn rename(&mut self, formula: &Formula) -> Formula {
        match formula {
            Formula::Bool(b) => Formula::Bool(*b),
            Formula::Int(n) => Formula::Int(*n),
            Formula::UInt(n) => Formula::UInt(*n),
            Formula::BitVec { value, width } => Formula::BitVec { value: *value, width: *width },

            Formula::Var(name, sort) => {
                let canonical = self.canonical_name(name);
                Formula::Var(canonical, sort.clone())
            }

            Formula::Not(inner) => Formula::Not(Box::new(self.rename(inner))),
            Formula::Neg(inner) => Formula::Neg(Box::new(self.rename(inner))),

            Formula::And(children) => {
                Formula::And(children.iter().map(|c| self.rename(c)).collect())
            }
            Formula::Or(children) => {
                Formula::Or(children.iter().map(|c| self.rename(c)).collect())
            }

            Formula::Implies(a, b) => {
                Formula::Implies(Box::new(self.rename(a)), Box::new(self.rename(b)))
            }
            Formula::Eq(a, b) => Formula::Eq(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Lt(a, b) => Formula::Lt(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Le(a, b) => Formula::Le(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Gt(a, b) => Formula::Gt(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Ge(a, b) => Formula::Ge(Box::new(self.rename(a)), Box::new(self.rename(b))),

            Formula::Add(a, b) => Formula::Add(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Sub(a, b) => Formula::Sub(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Mul(a, b) => Formula::Mul(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Div(a, b) => Formula::Div(Box::new(self.rename(a)), Box::new(self.rename(b))),
            Formula::Rem(a, b) => Formula::Rem(Box::new(self.rename(a)), Box::new(self.rename(b))),

            Formula::BvAdd(a, b, w) => {
                Formula::BvAdd(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvSub(a, b, w) => {
                Formula::BvSub(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvMul(a, b, w) => {
                Formula::BvMul(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvUDiv(a, b, w) => {
                Formula::BvUDiv(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvSDiv(a, b, w) => {
                Formula::BvSDiv(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvURem(a, b, w) => {
                Formula::BvURem(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvSRem(a, b, w) => {
                Formula::BvSRem(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvAnd(a, b, w) => {
                Formula::BvAnd(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvOr(a, b, w) => {
                Formula::BvOr(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvXor(a, b, w) => {
                Formula::BvXor(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvNot(inner, w) => Formula::BvNot(Box::new(self.rename(inner)), *w),
            Formula::BvShl(a, b, w) => {
                Formula::BvShl(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvLShr(a, b, w) => {
                Formula::BvLShr(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvAShr(a, b, w) => {
                Formula::BvAShr(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvULt(a, b, w) => {
                Formula::BvULt(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvULe(a, b, w) => {
                Formula::BvULe(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvSLt(a, b, w) => {
                Formula::BvSLt(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }
            Formula::BvSLe(a, b, w) => {
                Formula::BvSLe(Box::new(self.rename(a)), Box::new(self.rename(b)), *w)
            }

            Formula::BvToInt(inner, w, signed) => {
                Formula::BvToInt(Box::new(self.rename(inner)), *w, *signed)
            }
            Formula::IntToBv(inner, w) => Formula::IntToBv(Box::new(self.rename(inner)), *w),
            Formula::BvExtract { inner, high, low } => {
                Formula::BvExtract { inner: Box::new(self.rename(inner)), high: *high, low: *low }
            }
            Formula::BvConcat(a, b) => {
                Formula::BvConcat(Box::new(self.rename(a)), Box::new(self.rename(b)))
            }
            Formula::BvZeroExt(inner, w) => Formula::BvZeroExt(Box::new(self.rename(inner)), *w),
            Formula::BvSignExt(inner, w) => Formula::BvSignExt(Box::new(self.rename(inner)), *w),

            Formula::Ite(c, t, e) => Formula::Ite(
                Box::new(self.rename(c)),
                Box::new(self.rename(t)),
                Box::new(self.rename(e)),
            ),

            Formula::Select(arr, idx) => {
                Formula::Select(Box::new(self.rename(arr)), Box::new(self.rename(idx)))
            }
            Formula::Store(arr, idx, val) => Formula::Store(
                Box::new(self.rename(arr)),
                Box::new(self.rename(idx)),
                Box::new(self.rename(val)),
            ),

            Formula::Forall(vars, body) => {
                let new_vars: Vec<(String, Sort)> = vars
                    .iter()
                    .map(|(name, sort)| (self.canonical_name(name), sort.clone()))
                    .collect();
                Formula::Forall(new_vars, Box::new(self.rename(body)))
            }
            Formula::Exists(vars, body) => {
                let new_vars: Vec<(String, Sort)> = vars
                    .iter()
                    .map(|(name, sort)| (self.canonical_name(name), sort.clone()))
                    .collect();
                Formula::Exists(new_vars, Box::new(self.rename(body)))
            }
            _ => Formula::Bool(false),
        }
    }
}

/// Normalize a verification condition's formula and return both the key and
/// the normalized form (for use in similarity lookups).
///
/// This is a convenience wrapper combining `normalize_formula` and `semantic_key`.
#[must_use]
pub(crate) fn normalize_vc(vc: &VerificationCondition) -> (SemanticKey, NormalizedFormula) {
    let normalized = normalize_formula(&vc.formula);
    let key = semantic_key(&normalized);
    (key, normalized)
}

/// Look up a cached counterexample for a VC by semantic key.
///
/// Returns the counterexample if the cache contains a `Failed` result with
/// a counterexample for a structurally equivalent formula.
#[must_use]
pub(crate) fn lookup_semantic(
    cache: &mut SemanticCache,
    vc: &VerificationCondition,
) -> Option<Counterexample> {
    let result = cache.lookup_exact(vc)?;
    match &result.result {
        VerificationResult::Failed { counterexample: Some(cex), .. } => Some(cex.clone()),
        _ => None,
    }
}

/// Store a counterexample in the semantic cache keyed by the VC's formula.
///
/// Wraps the counterexample in a `VerificationResult::Failed` and inserts it.
pub(crate) fn store_counterexample(
    cache: &mut SemanticCache,
    vc: &VerificationCondition,
    counterexample: Counterexample,
) {
    let result = VerificationResult::Failed {
        solver: "cached".to_string(),
        time_ms: 0,
        counterexample: Some(counterexample),
    };
    cache.insert(vc, result);
}

#[cfg(test)]
mod tests {
    use trust_types::{Counterexample, CounterexampleValue, ProofStrength, SourceSpan, VcKind};

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn make_vc(function: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: function.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn failed_result(cex_var: &str, val: i128) -> VerificationResult {
        VerificationResult::Failed {
            solver: "test".to_string(),
            time_ms: 10,
            counterexample: Some(Counterexample::new(vec![(
                cex_var.to_string(),
                CounterexampleValue::Int(val),
            )])),
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "test".to_string(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    // -----------------------------------------------------------------------
    // Alpha-renaming / normalization tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_normalize_renames_variables_canonically() {
        // x > 0 AND y < 10  ->  v0 > 0 AND v1 < 10
        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let norm = normalize_formula(&f);

        let expected = Formula::And(vec![
            Formula::Gt(Box::new(var("v0")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("v1")), Box::new(Formula::Int(10))),
        ]);
        assert_eq!(norm.formula, expected);
        assert_eq!(norm.var_map.len(), 2);
        assert_eq!(norm.var_map[0], ("x".to_string(), "v0".to_string()));
        assert_eq!(norm.var_map[1], ("y".to_string(), "v1".to_string()));
    }

    #[test]
    fn test_normalize_same_structure_different_names_equal() {
        // f(a, b) = a > 0 AND b < 10
        let f1 = Formula::And(vec![
            Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("b")), Box::new(Formula::Int(10))),
        ]);
        // f(x, y) = x > 0 AND y < 10
        let f2 = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);

        let n1 = normalize_formula(&f1);
        let n2 = normalize_formula(&f2);
        assert_eq!(n1.formula, n2.formula, "same structure with different names should normalize equally");
    }

    #[test]
    fn test_normalize_different_structure_not_equal() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let n1 = normalize_formula(&f1);
        let n2 = normalize_formula(&f2);
        assert_ne!(n1.formula, n2.formula);
    }

    #[test]
    fn test_normalize_preserves_literals() {
        let f = Formula::Bool(true);
        let norm = normalize_formula(&f);
        assert_eq!(norm.formula, Formula::Bool(true));
        assert!(norm.var_map.is_empty());
    }

    #[test]
    fn test_normalize_repeated_variable_same_canonical() {
        // x > 0 AND x < 10  ->  v0 > 0 AND v0 < 10
        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(10))),
        ]);
        let norm = normalize_formula(&f);
        let expected = Formula::And(vec![
            Formula::Gt(Box::new(var("v0")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("v0")), Box::new(Formula::Int(10))),
        ]);
        assert_eq!(norm.formula, expected);
        assert_eq!(norm.var_map.len(), 1, "repeated variable should map once");
    }

    #[test]
    fn test_normalize_quantifier_variables() {
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("i")), Box::new(Formula::Int(0)))),
        );
        let norm = normalize_formula(&f);
        // Quantifier variable "i" and body variable "i" both map to v0
        match &norm.formula {
            Formula::Forall(vars, _) => {
                assert_eq!(vars[0].0, "v0");
            }
            _ => panic!("expected Forall"),
        }
    }

    // -----------------------------------------------------------------------
    // Semantic key tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_semantic_key_equal_for_alpha_equivalent() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(5)));
        let f2 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(5)));
        let k1 = semantic_key(&normalize_formula(&f1));
        let k2 = semantic_key(&normalize_formula(&f2));
        assert_eq!(k1, k2, "alpha-equivalent formulas should have same key");
    }

    #[test]
    fn test_semantic_key_different_for_different_structure() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(5)));
        let f2 = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(5)));
        let k1 = semantic_key(&normalize_formula(&f1));
        let k2 = semantic_key(&normalize_formula(&f2));
        assert_ne!(k1, k2);
    }

    #[test]
    fn test_semantic_key_is_sha256_hex() {
        let f = Formula::Bool(true);
        let key = semantic_key(&normalize_formula(&f));
        assert_eq!(key.fingerprint.len(), 64);
        assert!(key.fingerprint.chars().all(|c| c.is_ascii_hexdigit()));
    }

    // -----------------------------------------------------------------------
    // Similarity score tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_similarity_identical_is_one() {
        let f = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let n = normalize_formula(&f);
        assert!((similarity_score(&n, &n) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_similarity_completely_different_is_low() {
        let f1 = Formula::Bool(true);
        let f2 = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(42))),
        ]);
        let n1 = normalize_formula(&f1);
        let n2 = normalize_formula(&f2);
        let score = similarity_score(&n1, &n2);
        assert!(score < 0.3, "very different formulas should score low: {score}");
    }

    #[test]
    fn test_similarity_same_shape_different_literal() {
        // x > 0 vs x > 5 -- same structure, different constant
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(5)));
        let n1 = normalize_formula(&f1);
        let n2 = normalize_formula(&f2);
        let score = similarity_score(&n1, &n2);
        // 3 nodes total (Gt, Var, Int); Gt and Var match = 2/3
        assert!(score > 0.5, "partial match should be moderate: {score}");
    }

    #[test]
    fn test_similarity_symmetric() {
        let f1 = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]);
        let f2 = Formula::And(vec![
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]);
        let n1 = normalize_formula(&f1);
        let n2 = normalize_formula(&f2);
        let s1 = similarity_score(&n1, &n2);
        let s2 = similarity_score(&n2, &n1);
        assert!((s1 - s2).abs() < f64::EPSILON, "similarity should be symmetric");
    }

    // -----------------------------------------------------------------------
    // SemanticCache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_insert_and_exact_lookup() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        let result = failed_result("x", 0);
        cache.insert(&vc, result);

        let hit = cache.lookup_exact(&vc);
        assert!(hit.is_some());
        assert_eq!(hit.unwrap().source_function, "foo");
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn test_cache_alpha_equivalent_exact_hit() {
        let mut cache = SemanticCache::new();
        // Insert with variable name "a"
        let vc1 = make_vc("func_a", Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))));
        cache.insert(&vc1, failed_result("a", 0));

        // Lookup with variable name "b" -- same structure
        let vc2 = make_vc("func_b", Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0))));
        let hit = cache.lookup_exact(&vc2);
        assert!(hit.is_some(), "alpha-equivalent formula should hit");
        assert_eq!(hit.unwrap().source_function, "func_a");
    }

    #[test]
    fn test_cache_exact_miss() {
        let mut cache = SemanticCache::new();
        let vc1 = make_vc("foo", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        cache.insert(&vc1, proved_result());

        let vc2 = make_vc("bar", Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(0))));
        let hit = cache.lookup_exact(&vc2);
        assert!(hit.is_none());
        assert_eq!(cache.misses(), 1);
    }

    #[test]
    fn test_cache_similar_lookup_above_threshold() {
        let mut cache = SemanticCache::new();

        // Insert: x > 0 AND y < 10
        let vc1 = make_vc(
            "foo",
            Formula::And(vec![
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
            ]),
        );
        cache.insert(&vc1, failed_result("x", -1));

        // Lookup: a > 0 AND b < 10 (same structure, different names) -- exact hit
        let vc2 = make_vc(
            "bar",
            Formula::And(vec![
                Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("b")), Box::new(Formula::Int(10))),
            ]),
        );
        let result = cache.lookup_similar(&vc2, 0.8);
        assert!(result.is_some());
        assert!((result.unwrap().similarity - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cache_similar_lookup_below_threshold() {
        let mut cache = SemanticCache::new();
        let vc1 = make_vc("foo", Formula::Bool(true));
        cache.insert(&vc1, proved_result());

        // Very different formula
        let vc2 = make_vc(
            "bar",
            Formula::And(vec![
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
                Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(42))),
            ]),
        );
        let result = cache.lookup_similar(&vc2, 0.9);
        assert!(result.is_none(), "very different formula should not match at 0.9 threshold");
    }

    #[test]
    fn test_cache_len_and_empty() {
        let mut cache = SemanticCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        let vc = make_vc("foo", Formula::Bool(true));
        cache.insert(&vc, proved_result());
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Bool(true));
        cache.insert(&vc, proved_result());
        cache.lookup_exact(&vc);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 0);
    }

    #[test]
    fn test_cache_multiple_entries_best_match() {
        let mut cache = SemanticCache::new();

        // Insert a simple formula
        let vc1 = make_vc("simple", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        cache.insert(&vc1, failed_result("x", -1));

        // Insert a compound formula
        let vc2 = make_vc(
            "compound",
            Formula::And(vec![
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(100))),
            ]),
        );
        cache.insert(&vc2, failed_result("x", -5));

        // Lookup a similar compound formula -- should match compound entry
        let vc3 = make_vc(
            "query",
            Formula::And(vec![
                Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("b")), Box::new(Formula::Int(100))),
            ]),
        );
        let result = cache.lookup_similar(&vc3, 0.5);
        assert!(result.is_some());
        // Should be exact match via alpha-equivalence
        assert_eq!(result.unwrap().source_function, "compound");
    }

    // -----------------------------------------------------------------------
    // normalize_vc tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_normalize_vc_returns_key_and_formula() {
        let vc = make_vc("foo", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        let (key, norm) = normalize_vc(&vc);
        assert_eq!(key.fingerprint.len(), 64);
        assert!(!norm.var_map.is_empty());
    }

    #[test]
    fn test_normalize_vc_alpha_equivalence() {
        let vc1 = make_vc("foo", Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(5))));
        let vc2 = make_vc("bar", Formula::Gt(Box::new(var("z")), Box::new(Formula::Int(5))));
        let (k1, _) = normalize_vc(&vc1);
        let (k2, _) = normalize_vc(&vc2);
        assert_eq!(k1, k2, "alpha-equivalent VCs should produce same key");
    }

    #[test]
    fn test_normalize_vc_different_structure() {
        let vc1 = make_vc("foo", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        let vc2 = make_vc("foo", Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(0))));
        let (k1, _) = normalize_vc(&vc1);
        let (k2, _) = normalize_vc(&vc2);
        assert_ne!(k1, k2);
    }

    // -----------------------------------------------------------------------
    // lookup_semantic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lookup_semantic_returns_counterexample() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        cache.insert(&vc, failed_result("x", -5));

        let cex = lookup_semantic(&mut cache, &vc);
        assert!(cex.is_some());
        let cex = cex.unwrap();
        assert_eq!(cex.assignments.len(), 1);
        assert_eq!(cex.assignments[0].0, "x");
    }

    #[test]
    fn test_lookup_semantic_returns_none_for_proved() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Bool(true));
        cache.insert(&vc, proved_result());

        let cex = lookup_semantic(&mut cache, &vc);
        assert!(cex.is_none(), "proved results should not return counterexample");
    }

    #[test]
    fn test_lookup_semantic_returns_none_for_miss() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Bool(true));

        let cex = lookup_semantic(&mut cache, &vc);
        assert!(cex.is_none());
    }

    #[test]
    fn test_lookup_semantic_cross_function_alpha() {
        let mut cache = SemanticCache::new();
        // Store counterexample for func_a with variable "a"
        let vc1 = make_vc("func_a", Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))));
        cache.insert(&vc1, failed_result("a", -10));

        // Lookup with func_b using variable "b" -- same structure
        let vc2 = make_vc("func_b", Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0))));
        let cex = lookup_semantic(&mut cache, &vc2);
        assert!(cex.is_some(), "alpha-equivalent formula should yield cached cex");
    }

    // -----------------------------------------------------------------------
    // store_counterexample tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_counterexample_roundtrip() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))));
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(-1)),
        ]);

        store_counterexample(&mut cache, &vc, cex);
        assert_eq!(cache.len(), 1);

        let retrieved = lookup_semantic(&mut cache, &vc);
        assert!(retrieved.is_some());
        let retrieved = retrieved.unwrap();
        assert_eq!(retrieved.assignments.len(), 1);
        assert_eq!(retrieved.assignments[0].0, "x");
    }

    #[test]
    fn test_store_counterexample_multi_var() {
        let mut cache = SemanticCache::new();
        let vc = make_vc(
            "bar",
            Formula::And(vec![
                Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("b")), Box::new(Formula::Int(10))),
            ]),
        );
        let cex = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Int(-1)),
            ("b".to_string(), CounterexampleValue::Int(20)),
        ]);

        store_counterexample(&mut cache, &vc, cex);

        let retrieved = lookup_semantic(&mut cache, &vc);
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().assignments.len(), 2);
    }

    #[test]
    fn test_store_counterexample_overwrites() {
        let mut cache = SemanticCache::new();
        let vc = make_vc("foo", Formula::Bool(false));
        let cex1 = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(1)),
        ]);
        let cex2 = Counterexample::new(vec![
            ("y".to_string(), CounterexampleValue::Int(2)),
        ]);

        store_counterexample(&mut cache, &vc, cex1);
        store_counterexample(&mut cache, &vc, cex2);

        // The exact lookup hits the last-inserted for this key
        let retrieved = lookup_semantic(&mut cache, &vc);
        assert!(retrieved.is_some());
    }
}
