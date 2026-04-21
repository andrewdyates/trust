// trust-router/classifier.rs: VC query classification for intelligent solver selection
//
// tRust: Analyzes Formula structure to extract features (variable count, theory
// usage, nesting depth, quantifiers) and classify queries into categories that
// predict which solver backend will perform best. Maintains a performance
// database tracking (QueryClass, solver) -> solve time for adaptive routing.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::sync::Mutex;

use trust_types::{Formula, Sort, VcKind, VerificationCondition};

/// tRust: SMT theory tags detected in a formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TheoryTag {
    /// Linear integer arithmetic (QF_LIA).
    Lia,
    /// Linear real arithmetic (QF_LRA).
    Lra,
    /// Nonlinear integer arithmetic (QF_NIA).
    Nlia,
    /// Bitvector theory (QF_BV).
    Bv,
    /// Array theory (QF_AX).
    Arrays,
    /// Uninterpreted functions (QF_UF).
    Uf,
    /// Pure boolean / propositional.
    Bool,
}

/// tRust: Structural features extracted from a VC formula.
///
/// Used by the classifier to determine which solver family is likely to
/// perform best on this query.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Default)]
pub struct QueryFeatures {
    /// Number of distinct variable names.
    pub num_variables: usize,
    /// Number of clauses (top-level conjuncts in CNF-like structure).
    pub num_clauses: usize,
    /// Whether the formula contains quantifiers (forall/exists).
    pub has_quantifiers: bool,
    /// Whether the formula uses array select/store operations.
    pub has_arrays: bool,
    /// Whether the formula uses bitvector operations.
    pub has_bitvectors: bool,
    /// Maximum nesting depth of the formula AST.
    pub nesting_depth: usize,
    /// Set of SMT theory tags detected.
    pub theory_tags: Vec<TheoryTag>,
    /// Total number of AST nodes (formula size).
    pub node_count: usize,
}


/// tRust: High-level query classification for solver dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum QueryClass {
    /// Small linear arithmetic, no quantifiers -- fast for any SMT solver.
    EasyLinear,
    /// Contains multiplication/division of variables -- needs NIA support.
    HardNonlinear,
    /// Contains forall/exists quantifiers -- needs quantifier instantiation.
    Quantified,
    /// Primarily bitvector operations -- needs BV solver.
    BitVector,
    /// Uses array select/store -- needs array theory support.
    ArrayTheory,
    /// Multiple theories combined -- needs theory combination.
    Mixed,
    /// tRust: #178 Ownership/borrow/lifetime properties -- certus preferred.
    Ownership,
}

impl QueryClass {
    /// Human-readable label for diagnostics.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            QueryClass::EasyLinear => "easy-linear",
            QueryClass::HardNonlinear => "hard-nonlinear",
            QueryClass::Quantified => "quantified",
            QueryClass::BitVector => "bitvector",
            QueryClass::ArrayTheory => "array-theory",
            QueryClass::Mixed => "mixed",
            QueryClass::Ownership => "ownership",
        }
    }
}

/// tRust: Solver affinity -- preferred solver ordering for a query class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverAffinity {
    /// Query class this affinity applies to.
    pub class: QueryClass,
    /// Ordered list of preferred solver names (best first).
    pub preferred_solvers: Vec<String>,
}

/// tRust: A solver recommendation with confidence score.
#[derive(Debug, Clone, PartialEq)]
pub struct SolverRecommendation {
    /// Solver name.
    pub solver: String,
    /// Confidence in [0.0, 1.0] that this solver is optimal for the query.
    pub confidence: f64,
}

/// tRust: Historical performance record for a (class, solver) pair.
#[derive(Debug, Clone)]
#[derive(Default)]
pub(crate) struct PerformanceRecord {
    /// Total number of queries solved.
    pub(crate) count: u64,
    /// Sum of solve times in milliseconds.
    pub(crate) total_time_ms: u64,
    /// Number of timeouts.
    pub(crate) timeouts: u64,
    /// Number of successful solves (Proved or Failed with result).
    pub(crate) successes: u64,
}


impl PerformanceRecord {
    /// Average solve time in ms, or u64::MAX if no data.
    #[must_use]
    pub(crate) fn avg_time_ms(&self) -> u64 {
        if self.count == 0 { u64::MAX } else { self.total_time_ms / self.count }
    }

    /// Success rate in [0.0, 1.0], or 0.0 if no data.
    #[must_use]
    pub(crate) fn success_rate(&self) -> f64 {
        if self.count == 0 { 0.0 } else { self.successes as f64 / self.count as f64 }
    }
}

/// tRust: Performance database tracking solve time by (QueryClass, solver) pairs.
///
/// Thread-safe via internal Mutex. Records are accumulated over the lifetime
/// of the router and used to adapt solver selection over time.
pub struct PerformanceDatabase {
    records: Mutex<FxHashMap<(QueryClass, String), PerformanceRecord>>,
}

impl PerformanceDatabase {
    /// Create an empty performance database.
    #[must_use]
    pub fn new() -> Self {
        Self { records: Mutex::new(FxHashMap::default()) }
    }

    /// Record a solve attempt.
    pub fn record(
        &self,
        class: QueryClass,
        solver: &str,
        time_ms: u64,
        success: bool,
        timeout: bool,
    ) {
        let mut records =
            self.records.lock().unwrap_or_else(|e| e.into_inner());
        let entry = records.entry((class, solver.to_string())).or_default();
        entry.count += 1;
        entry.total_time_ms += time_ms;
        if success {
            entry.successes += 1;
        }
        if timeout {
            entry.timeouts += 1;
        }
    }

    /// Get historical performance for a (class, solver) pair.
    #[must_use]
    pub fn get(&self, class: QueryClass, solver: &str) -> Option<(u64, f64)> {
        let records =
            self.records.lock().unwrap_or_else(|e| e.into_inner());
        records.get(&(class, solver.to_string())).map(|r| (r.avg_time_ms(), r.success_rate()))
    }

    /// Return solvers ranked by historical performance for a given class.
    ///
    /// Returns `(solver_name, avg_time_ms, success_rate)` sorted by success
    /// rate descending, then avg time ascending.
    #[must_use]
    pub fn ranked_solvers(&self, class: QueryClass) -> Vec<(String, u64, f64)> {
        let records =
            self.records.lock().unwrap_or_else(|e| e.into_inner());
        let mut entries: Vec<(String, u64, f64)> = records
            .iter()
            .filter(|((c, _), _)| *c == class)
            .map(|((_, solver), rec)| (solver.clone(), rec.avg_time_ms(), rec.success_rate()))
            .collect();
        // Sort by success rate desc, then avg time asc.
        entries.sort_by(|a, b| {
            b.2.partial_cmp(&a.2)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then(a.1.cmp(&b.1))
        });
        entries
    }

    /// Number of records in the database.
    #[must_use]
    pub fn len(&self) -> usize {
        self.records.lock().unwrap_or_else(|e| e.into_inner()).len()
    }

    /// Whether the database has no records.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for PerformanceDatabase {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Feature extraction
// ---------------------------------------------------------------------------

/// tRust: Extract structural features from a formula.
///
/// Walks the formula AST once, counting variables, detecting theories,
/// measuring nesting depth, etc.
#[must_use]
pub fn extract_features(formula: &Formula) -> QueryFeatures {
    let mut vars = FxHashMap::default();
    let mut features = QueryFeatures::default();
    walk_formula(formula, 0, &mut vars, &mut features);
    features.num_variables = vars.len();
    // Count top-level clauses (And children, or 1 if not And).
    features.num_clauses = count_clauses(formula);
    // Deduplicate theory tags.
    features.theory_tags.sort_by_key(|t| *t as u8);
    features.theory_tags.dedup();
    features
}

/// Recursively walk the formula, collecting features.
fn walk_formula(
    formula: &Formula,
    depth: usize,
    vars: &mut FxHashMap<String, Sort>,
    features: &mut QueryFeatures,
) {
    features.node_count += 1;
    if depth > features.nesting_depth {
        features.nesting_depth = depth;
    }

    match formula {
        Formula::Bool(_) => {
            if !features.theory_tags.contains(&TheoryTag::Bool) {
                features.theory_tags.push(TheoryTag::Bool);
            }
        }
        Formula::Int(_) | Formula::UInt(_) => {
            if !features.theory_tags.contains(&TheoryTag::Lia) {
                features.theory_tags.push(TheoryTag::Lia);
            }
        }
        Formula::BitVec { .. } => {
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
        }
        Formula::Var(name, sort) => {
            vars.insert(name.clone(), sort.clone());
            match sort {
                Sort::BitVec(_) => {
                    features.has_bitvectors = true;
                    if !features.theory_tags.contains(&TheoryTag::Bv) {
                        features.theory_tags.push(TheoryTag::Bv);
                    }
                }
                Sort::Array(_, _) => {
                    features.has_arrays = true;
                    if !features.theory_tags.contains(&TheoryTag::Arrays) {
                        features.theory_tags.push(TheoryTag::Arrays);
                    }
                }
                Sort::Int => {
                    if !features.theory_tags.contains(&TheoryTag::Lia) {
                        features.theory_tags.push(TheoryTag::Lia);
                    }
                }
                Sort::Bool => {
                    if !features.theory_tags.contains(&TheoryTag::Bool) {
                        features.theory_tags.push(TheoryTag::Bool);
                    }
                }
                // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
                _ => {}
            }
        }

        // Unary connectives
        Formula::Not(inner) | Formula::Neg(inner) => {
            walk_formula(inner, depth + 1, vars, features);
        }

        // Binary connectives and arithmetic
        Formula::And(children) => {
            for child in children {
                walk_formula(child, depth + 1, vars, features);
            }
        }
        Formula::Or(children) => {
            for child in children {
                walk_formula(child, depth + 1, vars, features);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b) => {
            walk_formula(a, depth + 1, vars, features);
            walk_formula(b, depth + 1, vars, features);
        }

        // Multiplication/division -- signals nonlinear arithmetic.
        Formula::Mul(a, b) | Formula::Div(a, b) | Formula::Rem(a, b) => {
            // Check if both operands contain variables (nonlinear).
            if contains_var(a) && contains_var(b)
                && !features.theory_tags.contains(&TheoryTag::Nlia) {
                    features.theory_tags.push(TheoryTag::Nlia);
                }
            walk_formula(a, depth + 1, vars, features);
            walk_formula(b, depth + 1, vars, features);
        }

        // Bitvector operations
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
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
            walk_formula(a, depth + 1, vars, features);
            walk_formula(b, depth + 1, vars, features);
        }

        Formula::BvNot(inner, _) => {
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
            walk_formula(inner, depth + 1, vars, features);
        }

        // Bitvector conversions
        Formula::BvToInt(inner, _, _) | Formula::IntToBv(inner, _) => {
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
            walk_formula(inner, depth + 1, vars, features);
        }

        Formula::BvExtract { inner, .. } => {
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
            walk_formula(inner, depth + 1, vars, features);
        }

        Formula::BvConcat(a, b) => {
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
            walk_formula(a, depth + 1, vars, features);
            walk_formula(b, depth + 1, vars, features);
        }

        Formula::BvZeroExt(inner, _) | Formula::BvSignExt(inner, _) => {
            features.has_bitvectors = true;
            if !features.theory_tags.contains(&TheoryTag::Bv) {
                features.theory_tags.push(TheoryTag::Bv);
            }
            walk_formula(inner, depth + 1, vars, features);
        }

        // Conditional
        Formula::Ite(cond, then, els) => {
            walk_formula(cond, depth + 1, vars, features);
            walk_formula(then, depth + 1, vars, features);
            walk_formula(els, depth + 1, vars, features);
        }

        // Quantifiers
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            features.has_quantifiers = true;
            for (name, sort) in bindings {
                vars.insert(name.clone(), sort.clone());
            }
            walk_formula(body, depth + 1, vars, features);
        }

        // Arrays
        Formula::Select(arr, idx) => {
            features.has_arrays = true;
            if !features.theory_tags.contains(&TheoryTag::Arrays) {
                features.theory_tags.push(TheoryTag::Arrays);
            }
            walk_formula(arr, depth + 1, vars, features);
            walk_formula(idx, depth + 1, vars, features);
        }
        Formula::Store(arr, idx, val) => {
            features.has_arrays = true;
            if !features.theory_tags.contains(&TheoryTag::Arrays) {
                features.theory_tags.push(TheoryTag::Arrays);
            }
            walk_formula(arr, depth + 1, vars, features);
            walk_formula(idx, depth + 1, vars, features);
            walk_formula(val, depth + 1, vars, features);
        }
        _ => {} // Unknown Formula variant — no features to collect
    }
}

/// Check if a formula subtree contains any variable reference.
///
/// Uses `Formula::visit()` to walk the AST instead of a manual match.
fn contains_var(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |node| {
        if let Formula::Var(_, _) = node {
            found = true;
        }
    });
    found
}

/// Count top-level clauses (And children at root level).
fn count_clauses(formula: &Formula) -> usize {
    match formula {
        Formula::And(children) => children.len(),
        _ => 1,
    }
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

/// tRust: Classify a set of query features into a `QueryClass`.
#[must_use]
pub fn classify(features: &QueryFeatures) -> QueryClass {
    // Priority: quantifiers > arrays > bitvectors > nonlinear > mixed > easy.
    if features.has_quantifiers {
        return QueryClass::Quantified;
    }
    if features.has_arrays && features.has_bitvectors {
        return QueryClass::Mixed;
    }
    if features.has_arrays {
        return QueryClass::ArrayTheory;
    }
    if features.has_bitvectors {
        return QueryClass::BitVector;
    }
    if features.theory_tags.contains(&TheoryTag::Nlia) {
        return QueryClass::HardNonlinear;
    }
    // Multiple non-trivial theories = mixed.
    let non_bool_theories: usize =
        features.theory_tags.iter().filter(|t| !matches!(t, TheoryTag::Bool)).count();
    if non_bool_theories > 1 {
        return QueryClass::Mixed;
    }
    QueryClass::EasyLinear
}

/// tRust: Classify a VC's formula directly.
///
/// #178: Ownership-class VCs (tagged with `[memory:region]` prefix) are
/// classified as `Ownership` regardless of their formula structure, since
/// they need certus-specific axiom encoding.
#[must_use]
pub fn classify_vc(vc: &VerificationCondition) -> QueryClass {
    // tRust: #178 Ownership VCs get their own class for certus affinity.
    if let VcKind::Assertion { message } = &vc.kind
        && message.starts_with("[memory:region]") {
            return QueryClass::Ownership;
        }
    // tRust #546: Typed ownership VcKinds route directly to certus.
    if matches!(
        vc.kind,
        VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation
    ) {
        return QueryClass::Ownership;
    }
    let features = extract_features(&vc.formula);
    classify(&features)
}

// ---------------------------------------------------------------------------
// Solver affinity
// ---------------------------------------------------------------------------

/// tRust: Default solver affinity table.
///
/// Returns the preferred solver ordering for each query class based on
/// solver strengths. z4 is the primary SMT solver and handles most classes.
#[must_use]
pub fn default_affinity(class: QueryClass) -> SolverAffinity {
    let preferred = match class {
        QueryClass::EasyLinear => vec!["z4", "zani", "sunder"],
        QueryClass::HardNonlinear => vec!["z4", "sunder", "lean5"],
        QueryClass::Quantified => vec!["lean5", "z4"],
        QueryClass::BitVector => vec!["z4", "zani"],
        QueryClass::ArrayTheory => vec!["z4", "sunder"],
        QueryClass::Mixed => vec!["z4", "zani", "sunder"],
        // tRust: #178 Ownership VCs prefer certus (ownership-aware axioms).
        QueryClass::Ownership => vec!["certus", "z4", "sunder"],
    };
    SolverAffinity {
        class,
        preferred_solvers: preferred.into_iter().map(String::from).collect(),
    }
}

// ---------------------------------------------------------------------------
// Recommendation
// ---------------------------------------------------------------------------

/// tRust: Recommend solvers for a VC, combining static affinity with
/// historical performance data.
///
/// Returns a ranked list of solver recommendations. If the performance
/// database has data for the query class, it blends static affinity
/// (70% weight) with historical performance (30% weight).
#[must_use]
pub fn recommend_solver(
    vc: &VerificationCondition,
    perf_db: Option<&PerformanceDatabase>,
) -> Vec<SolverRecommendation> {
    let class = classify_vc(vc);
    let affinity = default_affinity(class);

    let mut recommendations: Vec<SolverRecommendation> = affinity
        .preferred_solvers
        .iter()
        .enumerate()
        .map(|(rank, solver)| {
            // Static confidence: 1st = 0.9, 2nd = 0.7, 3rd = 0.5, etc.
            let static_conf = (0.9 - rank as f64 * 0.2).max(0.1);

            let final_conf = if let Some(db) = perf_db {
                if let Some((_, success_rate)) = db.get(class, solver) {
                    // Blend: 70% static + 30% historical.
                    0.7 * static_conf + 0.3 * success_rate
                } else {
                    static_conf
                }
            } else {
                static_conf
            };

            SolverRecommendation { solver: solver.clone(), confidence: final_conf }
        })
        .collect();

    // If we have historical data, also include any solvers that performed
    // well but are not in the static affinity list.
    if let Some(db) = perf_db {
        let ranked = db.ranked_solvers(class);
        for (solver, _avg_time, success_rate) in ranked {
            if !recommendations.iter().any(|r| r.solver == solver) && success_rate > 0.5 {
                recommendations.push(SolverRecommendation {
                    solver,
                    confidence: 0.3 * success_rate,
                });
            }
        }
    }

    // Sort by confidence descending.
    recommendations.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal));
    recommendations
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    // -----------------------------------------------------------------------
    // Feature extraction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_features_bool_literal() {
        let f = extract_features(&Formula::Bool(true));
        assert_eq!(f.num_variables, 0);
        assert_eq!(f.node_count, 1);
        assert_eq!(f.nesting_depth, 0);
        assert!(!f.has_quantifiers);
        assert!(!f.has_arrays);
        assert!(!f.has_bitvectors);
    }

    #[test]
    fn test_extract_features_variable_counting() {
        let formula = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("y".into(), Sort::Int),
            Formula::Var("x".into(), Sort::Int), // duplicate
        ]);
        let f = extract_features(&formula);
        assert_eq!(f.num_variables, 2); // x and y
        assert_eq!(f.num_clauses, 3);
    }

    #[test]
    fn test_extract_features_bitvector_detection() {
        let formula = Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        );
        let f = extract_features(&formula);
        assert!(f.has_bitvectors);
        assert!(f.theory_tags.contains(&TheoryTag::Bv));
        assert_eq!(f.num_variables, 2);
    }

    #[test]
    fn test_extract_features_array_detection() {
        let formula = Formula::Select(
            Box::new(Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))),
            Box::new(Formula::Var("idx".into(), Sort::Int)),
        );
        let f = extract_features(&formula);
        assert!(f.has_arrays);
        assert!(f.theory_tags.contains(&TheoryTag::Arrays));
    }

    #[test]
    fn test_extract_features_quantifier_detection() {
        let formula = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let f = extract_features(&formula);
        assert!(f.has_quantifiers);
        assert_eq!(f.num_variables, 1);
    }

    #[test]
    fn test_extract_features_nonlinear_detection() {
        // x * y where both are variables => nonlinear
        let formula = Formula::Mul(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let f = extract_features(&formula);
        assert!(f.theory_tags.contains(&TheoryTag::Nlia));
    }

    #[test]
    fn test_extract_features_linear_mul_by_constant() {
        // x * 2 is still linear (constant on one side)
        let formula = Formula::Mul(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(2)),
        );
        let f = extract_features(&formula);
        assert!(!f.theory_tags.contains(&TheoryTag::Nlia));
    }

    #[test]
    fn test_extract_features_nesting_depth() {
        // Not(Not(Not(Bool(true)))) => depth 3
        let formula = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::Bool(true),
        ))))));
        let f = extract_features(&formula);
        assert_eq!(f.nesting_depth, 3);
    }

    #[test]
    fn test_extract_features_clause_count() {
        let formula = Formula::And(vec![
            Formula::Bool(true),
            Formula::Bool(false),
            Formula::Bool(true),
            Formula::Bool(false),
        ]);
        let f = extract_features(&formula);
        assert_eq!(f.num_clauses, 4);
    }

    #[test]
    fn test_extract_features_single_non_and_is_one_clause() {
        let f = extract_features(&Formula::Bool(true));
        assert_eq!(f.num_clauses, 1);
    }

    // -----------------------------------------------------------------------
    // Classification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_easy_linear() {
        let features = QueryFeatures {
            num_variables: 3,
            num_clauses: 5,
            has_quantifiers: false,
            has_arrays: false,
            has_bitvectors: false,
            nesting_depth: 2,
            theory_tags: vec![TheoryTag::Lia],
            node_count: 15,
        };
        assert_eq!(classify(&features), QueryClass::EasyLinear);
    }

    #[test]
    fn test_classify_quantified() {
        let features = QueryFeatures {
            has_quantifiers: true,
            theory_tags: vec![TheoryTag::Lia],
            ..Default::default()
        };
        assert_eq!(classify(&features), QueryClass::Quantified);
    }

    #[test]
    fn test_classify_bitvector() {
        let features = QueryFeatures {
            has_bitvectors: true,
            theory_tags: vec![TheoryTag::Bv],
            ..Default::default()
        };
        assert_eq!(classify(&features), QueryClass::BitVector);
    }

    #[test]
    fn test_classify_array() {
        let features = QueryFeatures {
            has_arrays: true,
            theory_tags: vec![TheoryTag::Arrays],
            ..Default::default()
        };
        assert_eq!(classify(&features), QueryClass::ArrayTheory);
    }

    #[test]
    fn test_classify_nonlinear() {
        let features = QueryFeatures {
            theory_tags: vec![TheoryTag::Nlia],
            ..Default::default()
        };
        assert_eq!(classify(&features), QueryClass::HardNonlinear);
    }

    #[test]
    fn test_classify_mixed_arrays_and_bv() {
        let features = QueryFeatures {
            has_arrays: true,
            has_bitvectors: true,
            theory_tags: vec![TheoryTag::Arrays, TheoryTag::Bv],
            ..Default::default()
        };
        assert_eq!(classify(&features), QueryClass::Mixed);
    }

    #[test]
    fn test_classify_vc_integration() {
        let vc = make_vc(Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        ));
        assert_eq!(classify_vc(&vc), QueryClass::BitVector);
    }

    // -----------------------------------------------------------------------
    // Affinity tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_affinity_easy_linear() {
        let aff = default_affinity(QueryClass::EasyLinear);
        assert_eq!(aff.class, QueryClass::EasyLinear);
        assert_eq!(aff.preferred_solvers[0], "z4");
    }

    #[test]
    fn test_default_affinity_bitvector() {
        let aff = default_affinity(QueryClass::BitVector);
        assert!(aff.preferred_solvers.contains(&"z4".to_string()));
        assert!(aff.preferred_solvers.contains(&"zani".to_string()));
    }

    // -----------------------------------------------------------------------
    // Performance database tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_perf_db_record_and_get() {
        let db = PerformanceDatabase::new();
        db.record(QueryClass::EasyLinear, "z4", 100, true, false);
        db.record(QueryClass::EasyLinear, "z4", 200, true, false);

        let (avg_time, success_rate) = db.get(QueryClass::EasyLinear, "z4").unwrap();
        assert_eq!(avg_time, 150);
        assert!((success_rate - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_perf_db_get_missing() {
        let db = PerformanceDatabase::new();
        assert!(db.get(QueryClass::EasyLinear, "z4").is_none());
    }

    #[test]
    fn test_perf_db_ranked_solvers() {
        let db = PerformanceDatabase::new();
        // z4: 2 successes out of 2 = 100%
        db.record(QueryClass::EasyLinear, "z4", 50, true, false);
        db.record(QueryClass::EasyLinear, "z4", 60, true, false);
        // zani: 1 success out of 2 = 50%
        db.record(QueryClass::EasyLinear, "zani", 100, true, false);
        db.record(QueryClass::EasyLinear, "zani", 500, false, true);

        let ranked = db.ranked_solvers(QueryClass::EasyLinear);
        assert_eq!(ranked.len(), 2);
        assert_eq!(ranked[0].0, "z4"); // higher success rate
        assert_eq!(ranked[1].0, "zani");
    }

    #[test]
    fn test_perf_db_len_and_is_empty() {
        let db = PerformanceDatabase::new();
        assert!(db.is_empty());
        assert_eq!(db.len(), 0);

        db.record(QueryClass::EasyLinear, "z4", 100, true, false);
        assert!(!db.is_empty());
        assert_eq!(db.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Recommendation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_recommend_solver_static_only() {
        let vc = make_vc(Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        ));
        let recs = recommend_solver(&vc, None);
        assert!(!recs.is_empty());
        // First recommendation should have highest confidence.
        assert!(recs[0].confidence >= recs.last().unwrap().confidence);
        assert_eq!(recs[0].solver, "z4");
    }

    #[test]
    fn test_recommend_solver_with_perf_data() {
        let vc = make_vc(Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        ));
        let db = PerformanceDatabase::new();
        // zani has perfect track record for EasyLinear
        db.record(QueryClass::EasyLinear, "zani", 10, true, false);
        db.record(QueryClass::EasyLinear, "zani", 15, true, false);
        // z4 has mediocre record
        db.record(QueryClass::EasyLinear, "z4", 500, true, false);
        db.record(QueryClass::EasyLinear, "z4", 1000, false, true);

        let recs = recommend_solver(&vc, Some(&db));
        assert!(!recs.is_empty());
        // With blending, z4 still has high static affinity but zani gets a boost.
        // Both should appear.
        let solver_names: Vec<&str> = recs.iter().map(|r| r.solver.as_str()).collect();
        assert!(solver_names.contains(&"z4"));
        assert!(solver_names.contains(&"zani"));
    }

    #[test]
    fn test_recommend_solver_bitvector_query() {
        let vc = make_vc(Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        ));
        let recs = recommend_solver(&vc, None);
        // BV queries should recommend z4 and zani.
        let solver_names: Vec<&str> = recs.iter().map(|r| r.solver.as_str()).collect();
        assert!(solver_names.contains(&"z4"));
        assert!(solver_names.contains(&"zani"));
    }

    #[test]
    fn test_recommend_solver_includes_historical_unknown_solver() {
        let vc = make_vc(Formula::Bool(true));
        let db = PerformanceDatabase::new();
        // A solver not in static affinity but with good track record.
        db.record(QueryClass::EasyLinear, "experimental", 10, true, false);
        db.record(QueryClass::EasyLinear, "experimental", 20, true, false);

        let recs = recommend_solver(&vc, Some(&db));
        let solver_names: Vec<&str> = recs.iter().map(|r| r.solver.as_str()).collect();
        assert!(solver_names.contains(&"experimental"));
    }

    #[test]
    fn test_query_class_label() {
        assert_eq!(QueryClass::EasyLinear.label(), "easy-linear");
        assert_eq!(QueryClass::HardNonlinear.label(), "hard-nonlinear");
        assert_eq!(QueryClass::Mixed.label(), "mixed");
    }
}
