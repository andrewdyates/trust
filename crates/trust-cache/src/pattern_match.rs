// trust-cache/pattern_match.rs: Formula pattern matching with wildcards
//
// Extracts generalized formula patterns from concrete formulas and matches
// new formulas against cached patterns. Enables counterexample reuse when
// formulas share the same shape but differ in specific subterms.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort};

/// A generalized formula pattern where some subterms are replaced by wildcards.
///
/// Wildcards match any subterm at that position, enabling structural matching
/// across formulas that share the same top-level shape but differ in constants
/// or specific subexpressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormulaPattern {
    /// Matches any formula subterm. Wildcards with the same id must match
    /// the same subterm within a single pattern match.
    Wildcard(WildcardId),

    /// Exact boolean literal.
    Bool(bool),
    /// Exact integer literal.
    Int(i128),
    /// Exact bitvector literal.
    BitVec { value: i128, width: u32 },

    /// Variable with a specific sort (name is a wildcard).
    AnyVar(Sort),

    /// Boolean negation.
    Not(Box<FormulaPattern>),
    /// Conjunction.
    And(Vec<FormulaPattern>),
    /// Disjunction.
    Or(Vec<FormulaPattern>),
    /// Implication.
    Implies(Box<FormulaPattern>, Box<FormulaPattern>),

    /// Equality comparison.
    Eq(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Less than.
    Lt(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Less than or equal.
    Le(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Greater than.
    Gt(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Greater than or equal.
    Ge(Box<FormulaPattern>, Box<FormulaPattern>),

    /// Addition.
    Add(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Subtraction.
    Sub(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Multiplication.
    Mul(Box<FormulaPattern>, Box<FormulaPattern>),
    /// Division.
    Div(Box<FormulaPattern>, Box<FormulaPattern>),

    /// Bitvector addition with width.
    BvAdd(Box<FormulaPattern>, Box<FormulaPattern>, u32),
    /// Bitvector subtraction with width.
    BvSub(Box<FormulaPattern>, Box<FormulaPattern>, u32),

    /// If-then-else.
    Ite(Box<FormulaPattern>, Box<FormulaPattern>, Box<FormulaPattern>),

    /// Quantifier pattern (forall/exists with arity and sorts).
    Forall(Vec<Sort>, Box<FormulaPattern>),
    /// Existential quantifier pattern.
    Exists(Vec<Sort>, Box<FormulaPattern>),
}

/// Identifier for wildcards within a pattern. Wildcards with the same id
/// must bind to the same subterm during matching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WildcardId(pub u32);

/// Controls how aggressively formulas are generalized into patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralizationLevel {
    /// Only replace variable names with AnyVar; keep all structure and literals.
    Variables,
    /// Replace variables and integer/bitvector literals with wildcards.
    Literals,
    /// Replace variables, literals, and leaf subexpressions with wildcards.
    Leaves,
}

/// Extract a pattern from a concrete formula.
///
/// The generalization level controls which parts become wildcards:
/// - `Variables`: variable names become `AnyVar`, structure preserved exactly.
/// - `Literals`: additionally, integer/bitvec constants become wildcards.
/// - `Leaves`: all leaf nodes (vars, literals) become wildcards.
#[must_use]
pub(crate) fn extract_pattern(formula: &Formula, level: GeneralizationLevel) -> FormulaPattern {
    let mut next_wildcard = 0u32;
    extract_inner(formula, level, &mut next_wildcard)
}

fn extract_inner(
    formula: &Formula,
    level: GeneralizationLevel,
    next_wc: &mut u32,
) -> FormulaPattern {
    match formula {
        Formula::Bool(b) => {
            if level == GeneralizationLevel::Leaves {
                let id = *next_wc;
                *next_wc += 1;
                FormulaPattern::Wildcard(WildcardId(id))
            } else {
                FormulaPattern::Bool(*b)
            }
        }

        Formula::Int(n) => match level {
            GeneralizationLevel::Variables => FormulaPattern::Int(*n),
            GeneralizationLevel::Literals | GeneralizationLevel::Leaves => {
                let id = *next_wc;
                *next_wc += 1;
                FormulaPattern::Wildcard(WildcardId(id))
            }
        },

        Formula::BitVec { value, width } => match level {
            GeneralizationLevel::Variables => FormulaPattern::BitVec { value: *value, width: *width },
            GeneralizationLevel::Literals | GeneralizationLevel::Leaves => {
                let id = *next_wc;
                *next_wc += 1;
                FormulaPattern::Wildcard(WildcardId(id))
            }
        },

        Formula::Var(_, sort) => match level {
            GeneralizationLevel::Variables | GeneralizationLevel::Literals => {
                FormulaPattern::AnyVar(sort.clone())
            }
            GeneralizationLevel::Leaves => {
                let id = *next_wc;
                *next_wc += 1;
                FormulaPattern::Wildcard(WildcardId(id))
            }
        },

        Formula::Not(inner) => {
            FormulaPattern::Not(Box::new(extract_inner(inner, level, next_wc)))
        }

        Formula::And(children) => FormulaPattern::And(
            children.iter().map(|c| extract_inner(c, level, next_wc)).collect(),
        ),

        Formula::Or(children) => FormulaPattern::Or(
            children.iter().map(|c| extract_inner(c, level, next_wc)).collect(),
        ),

        Formula::Implies(a, b) => FormulaPattern::Implies(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),

        Formula::Eq(a, b) => FormulaPattern::Eq(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Lt(a, b) => FormulaPattern::Lt(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Le(a, b) => FormulaPattern::Le(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Gt(a, b) => FormulaPattern::Gt(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Ge(a, b) => FormulaPattern::Ge(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),

        Formula::Add(a, b) => FormulaPattern::Add(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Sub(a, b) => FormulaPattern::Sub(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Mul(a, b) => FormulaPattern::Mul(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),
        Formula::Div(a, b) => FormulaPattern::Div(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
        ),

        Formula::BvAdd(a, b, w) => FormulaPattern::BvAdd(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
            *w,
        ),
        Formula::BvSub(a, b, w) => FormulaPattern::BvSub(
            Box::new(extract_inner(a, level, next_wc)),
            Box::new(extract_inner(b, level, next_wc)),
            *w,
        ),

        Formula::Ite(c, t, e) => FormulaPattern::Ite(
            Box::new(extract_inner(c, level, next_wc)),
            Box::new(extract_inner(t, level, next_wc)),
            Box::new(extract_inner(e, level, next_wc)),
        ),

        Formula::Forall(vars, body) => {
            let sorts: Vec<Sort> = vars.iter().map(|(_, s)| s.clone()).collect();
            FormulaPattern::Forall(sorts, Box::new(extract_inner(body, level, next_wc)))
        }

        Formula::Exists(vars, body) => {
            let sorts: Vec<Sort> = vars.iter().map(|(_, s)| s.clone()).collect();
            FormulaPattern::Exists(sorts, Box::new(extract_inner(body, level, next_wc)))
        }

        // For formula variants not explicitly handled, produce a wildcard
        _ => {
            let id = *next_wc;
            *next_wc += 1;
            FormulaPattern::Wildcard(WildcardId(id))
        }
    }
}

/// Check if a concrete formula matches a pattern.
///
/// Returns `true` if the formula's structure matches the pattern at every
/// non-wildcard position. Wildcards with the same `WildcardId` must bind
/// to structurally equal subterms.
#[must_use]
pub(crate) fn matches_pattern(formula: &Formula, pattern: &FormulaPattern) -> bool {
    let mut bindings: FxHashMap<WildcardId, &Formula> = FxHashMap::default();
    matches_inner(formula, pattern, &mut bindings)
}

fn matches_inner<'a>(
    formula: &'a Formula,
    pattern: &FormulaPattern,
    bindings: &mut FxHashMap<WildcardId, &'a Formula>,
) -> bool {
    match pattern {
        FormulaPattern::Wildcard(id) => {
            if let Some(bound) = bindings.get(id) {
                // Same wildcard id must bind to same subterm
                *bound == formula
            } else {
                bindings.insert(*id, formula);
                true
            }
        }

        FormulaPattern::Bool(b) => matches!(formula, Formula::Bool(fb) if fb == b),
        FormulaPattern::Int(n) => matches!(formula, Formula::Int(fn_) if fn_ == n),
        FormulaPattern::BitVec { value, width } => {
            matches!(formula, Formula::BitVec { value: v, width: w } if v == value && w == width)
        }

        FormulaPattern::AnyVar(sort) => {
            matches!(formula, Formula::Var(_, s) if s == sort)
        }

        FormulaPattern::Not(inner) => {
            if let Formula::Not(f_inner) = formula {
                matches_inner(f_inner, inner, bindings)
            } else {
                false
            }
        }

        FormulaPattern::And(p_children) => {
            if let Formula::And(f_children) = formula {
                p_children.len() == f_children.len()
                    && p_children
                        .iter()
                        .zip(f_children.iter())
                        .all(|(p, f)| matches_inner(f, p, bindings))
            } else {
                false
            }
        }

        FormulaPattern::Or(p_children) => {
            if let Formula::Or(f_children) = formula {
                p_children.len() == f_children.len()
                    && p_children
                        .iter()
                        .zip(f_children.iter())
                        .all(|(p, f)| matches_inner(f, p, bindings))
            } else {
                false
            }
        }

        FormulaPattern::Implies(pa, pb) => {
            if let Formula::Implies(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }

        FormulaPattern::Eq(pa, pb) => {
            if let Formula::Eq(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Lt(pa, pb) => {
            if let Formula::Lt(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Le(pa, pb) => {
            if let Formula::Le(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Gt(pa, pb) => {
            if let Formula::Gt(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Ge(pa, pb) => {
            if let Formula::Ge(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }

        FormulaPattern::Add(pa, pb) => {
            if let Formula::Add(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Sub(pa, pb) => {
            if let Formula::Sub(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Mul(pa, pb) => {
            if let Formula::Mul(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::Div(pa, pb) => {
            if let Formula::Div(fa, fb) = formula {
                matches_inner(fa, pa, bindings) && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }

        FormulaPattern::BvAdd(pa, pb, pw) => {
            if let Formula::BvAdd(fa, fb, fw) = formula {
                pw == fw
                    && matches_inner(fa, pa, bindings)
                    && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }
        FormulaPattern::BvSub(pa, pb, pw) => {
            if let Formula::BvSub(fa, fb, fw) = formula {
                pw == fw
                    && matches_inner(fa, pa, bindings)
                    && matches_inner(fb, pb, bindings)
            } else {
                false
            }
        }

        FormulaPattern::Ite(pc, pt, pe) => {
            if let Formula::Ite(fc, ft, fe) = formula {
                matches_inner(fc, pc, bindings)
                    && matches_inner(ft, pt, bindings)
                    && matches_inner(fe, pe, bindings)
            } else {
                false
            }
        }

        FormulaPattern::Forall(p_sorts, p_body) => {
            if let Formula::Forall(f_vars, f_body) = formula {
                p_sorts.len() == f_vars.len()
                    && p_sorts
                        .iter()
                        .zip(f_vars.iter())
                        .all(|(ps, (_, fs))| ps == fs)
                    && matches_inner(f_body, p_body, bindings)
            } else {
                false
            }
        }

        FormulaPattern::Exists(p_sorts, p_body) => {
            if let Formula::Exists(f_vars, f_body) = formula {
                p_sorts.len() == f_vars.len()
                    && p_sorts
                        .iter()
                        .zip(f_vars.iter())
                        .all(|(ps, (_, fs))| ps == fs)
                    && matches_inner(f_body, p_body, bindings)
            } else {
                false
            }
        }
    }
}

/// Compute a fingerprint hash for a pattern, for use as a cache key.
#[must_use]
pub(crate) fn pattern_fingerprint(pattern: &FormulaPattern) -> String {
    let canonical = pattern_to_string(pattern);
    let mut hasher = Sha256::new();
    hasher.update(canonical.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Convert a pattern to a canonical string representation for hashing.
fn pattern_to_string(pattern: &FormulaPattern) -> String {
    match pattern {
        FormulaPattern::Wildcard(WildcardId(id)) => format!("?{id}"),
        FormulaPattern::Bool(b) => format!("B({b})"),
        FormulaPattern::Int(n) => format!("I({n})"),
        FormulaPattern::BitVec { value, width } => format!("BV({value},{width})"),
        FormulaPattern::AnyVar(sort) => format!("V({sort:?})"),
        FormulaPattern::Not(inner) => format!("Not({})", pattern_to_string(inner)),
        FormulaPattern::And(children) => {
            let parts: Vec<String> = children.iter().map(pattern_to_string).collect();
            format!("And({})", parts.join(","))
        }
        FormulaPattern::Or(children) => {
            let parts: Vec<String> = children.iter().map(pattern_to_string).collect();
            format!("Or({})", parts.join(","))
        }
        FormulaPattern::Implies(a, b) => {
            format!("Imp({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Eq(a, b) => {
            format!("Eq({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Lt(a, b) => {
            format!("Lt({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Le(a, b) => {
            format!("Le({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Gt(a, b) => {
            format!("Gt({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Ge(a, b) => {
            format!("Ge({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Add(a, b) => {
            format!("Add({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Sub(a, b) => {
            format!("Sub({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Mul(a, b) => {
            format!("Mul({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Div(a, b) => {
            format!("Div({},{})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::BvAdd(a, b, w) => {
            format!("BvAdd({},{},{w})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::BvSub(a, b, w) => {
            format!("BvSub({},{},{w})", pattern_to_string(a), pattern_to_string(b))
        }
        FormulaPattern::Ite(c, t, e) => {
            format!(
                "Ite({},{},{})",
                pattern_to_string(c),
                pattern_to_string(t),
                pattern_to_string(e)
            )
        }
        FormulaPattern::Forall(sorts, body) => {
            format!("Forall({sorts:?},{})", pattern_to_string(body))
        }
        FormulaPattern::Exists(sorts, body) => {
            format!("Exists({sorts:?},{})", pattern_to_string(body))
        }
    }
}

/// Count the number of nodes in a pattern (for complexity metrics).
#[must_use]
pub(crate) fn pattern_size(pattern: &FormulaPattern) -> usize {
    match pattern {
        FormulaPattern::Wildcard(_)
        | FormulaPattern::Bool(_)
        | FormulaPattern::Int(_)
        | FormulaPattern::BitVec { .. }
        | FormulaPattern::AnyVar(_) => 1,

        FormulaPattern::Not(inner) => 1 + pattern_size(inner),

        FormulaPattern::And(children) | FormulaPattern::Or(children) => {
            1 + children.iter().map(pattern_size).sum::<usize>()
        }

        FormulaPattern::Implies(a, b)
        | FormulaPattern::Eq(a, b)
        | FormulaPattern::Lt(a, b)
        | FormulaPattern::Le(a, b)
        | FormulaPattern::Gt(a, b)
        | FormulaPattern::Ge(a, b)
        | FormulaPattern::Add(a, b)
        | FormulaPattern::Sub(a, b)
        | FormulaPattern::Mul(a, b)
        | FormulaPattern::Div(a, b)
        | FormulaPattern::BvAdd(a, b, _)
        | FormulaPattern::BvSub(a, b, _) => 1 + pattern_size(a) + pattern_size(b),

        FormulaPattern::Ite(c, t, e) => {
            1 + pattern_size(c) + pattern_size(t) + pattern_size(e)
        }

        FormulaPattern::Forall(_, body) | FormulaPattern::Exists(_, body) => {
            1 + pattern_size(body)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn bv_var(name: &str, width: u32) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(width))
    }

    // -----------------------------------------------------------------------
    // extract_pattern tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_variables_level_keeps_literals() {
        let f = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        assert_eq!(
            p,
            FormulaPattern::Gt(
                Box::new(FormulaPattern::AnyVar(Sort::Int)),
                Box::new(FormulaPattern::Int(0)),
            )
        );
    }

    #[test]
    fn test_extract_literals_level_wildcards_constants() {
        let f = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(42)));
        let p = extract_pattern(&f, GeneralizationLevel::Literals);
        match &p {
            FormulaPattern::Gt(left, right) => {
                assert!(matches!(left.as_ref(), FormulaPattern::AnyVar(Sort::Int)));
                assert!(matches!(right.as_ref(), FormulaPattern::Wildcard(_)));
            }
            _ => panic!("expected Gt pattern"),
        }
    }

    #[test]
    fn test_extract_leaves_level_all_wildcards() {
        let f = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let p = extract_pattern(&f, GeneralizationLevel::Leaves);
        match &p {
            FormulaPattern::Gt(left, right) => {
                assert!(matches!(left.as_ref(), FormulaPattern::Wildcard(_)));
                assert!(matches!(right.as_ref(), FormulaPattern::Wildcard(_)));
            }
            _ => panic!("expected Gt pattern"),
        }
    }

    #[test]
    fn test_extract_and_pattern() {
        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        match &p {
            FormulaPattern::And(children) => assert_eq!(children.len(), 2),
            _ => panic!("expected And pattern"),
        }
    }

    #[test]
    fn test_extract_bitvec_literal_variables_level() {
        let f = Formula::BitVec { value: 255, width: 8 };
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        assert_eq!(p, FormulaPattern::BitVec { value: 255, width: 8 });
    }

    #[test]
    fn test_extract_bitvec_literal_literals_level() {
        let f = Formula::BitVec { value: 255, width: 8 };
        let p = extract_pattern(&f, GeneralizationLevel::Literals);
        assert!(matches!(p, FormulaPattern::Wildcard(_)));
    }

    #[test]
    fn test_extract_bool_variables_level() {
        let f = Formula::Bool(true);
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        assert_eq!(p, FormulaPattern::Bool(true));
    }

    #[test]
    fn test_extract_bool_leaves_level() {
        let f = Formula::Bool(true);
        let p = extract_pattern(&f, GeneralizationLevel::Leaves);
        assert!(matches!(p, FormulaPattern::Wildcard(_)));
    }

    #[test]
    fn test_extract_not_pattern() {
        let f = Formula::Not(Box::new(var("x")));
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        match &p {
            FormulaPattern::Not(inner) => {
                assert!(matches!(inner.as_ref(), FormulaPattern::AnyVar(Sort::Int)));
            }
            _ => panic!("expected Not pattern"),
        }
    }

    #[test]
    fn test_extract_ite_pattern() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(var("x")),
            Box::new(var("y")),
        );
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        assert!(matches!(p, FormulaPattern::Ite(_, _, _)));
    }

    #[test]
    fn test_extract_forall_pattern() {
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("i")), Box::new(Formula::Int(0)))),
        );
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        match &p {
            FormulaPattern::Forall(sorts, _) => {
                assert_eq!(sorts, &[Sort::Int]);
            }
            _ => panic!("expected Forall pattern"),
        }
    }

    #[test]
    fn test_extract_bvadd_pattern() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        match &p {
            FormulaPattern::BvAdd(_, _, w) => assert_eq!(*w, 32),
            _ => panic!("expected BvAdd pattern"),
        }
    }

    // -----------------------------------------------------------------------
    // matches_pattern tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_matches_exact_bool() {
        let f = Formula::Bool(true);
        let p = FormulaPattern::Bool(true);
        assert!(matches_pattern(&f, &p));
        assert!(!matches_pattern(&Formula::Bool(false), &p));
    }

    #[test]
    fn test_matches_exact_int() {
        let f = Formula::Int(42);
        let p = FormulaPattern::Int(42);
        assert!(matches_pattern(&f, &p));
        assert!(!matches_pattern(&Formula::Int(99), &p));
    }

    #[test]
    fn test_matches_wildcard_any_formula() {
        let p = FormulaPattern::Wildcard(WildcardId(0));
        assert!(matches_pattern(&Formula::Bool(true), &p));
        assert!(matches_pattern(&Formula::Int(42), &p));
        assert!(matches_pattern(&var("x"), &p));
    }

    #[test]
    fn test_matches_wildcard_consistency() {
        // Same wildcard id must bind to same subterm
        let p = FormulaPattern::Eq(
            Box::new(FormulaPattern::Wildcard(WildcardId(0))),
            Box::new(FormulaPattern::Wildcard(WildcardId(0))),
        );
        // x == x should match (same subterm)
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(var("x")));
        assert!(matches_pattern(&f1, &p));

        // x == y should NOT match (different subterms)
        let f2 = Formula::Eq(Box::new(var("x")), Box::new(var("y")));
        assert!(!matches_pattern(&f2, &p));
    }

    #[test]
    fn test_matches_wildcard_different_ids_independent() {
        // Different wildcard ids can bind to different subterms
        let p = FormulaPattern::Eq(
            Box::new(FormulaPattern::Wildcard(WildcardId(0))),
            Box::new(FormulaPattern::Wildcard(WildcardId(1))),
        );
        let f = Formula::Eq(Box::new(var("x")), Box::new(var("y")));
        assert!(matches_pattern(&f, &p));
    }

    #[test]
    fn test_matches_any_var_sort_check() {
        let p = FormulaPattern::AnyVar(Sort::Int);
        assert!(matches_pattern(&var("x"), &p));
        assert!(matches_pattern(&var("anything"), &p));
        // Wrong sort should not match
        assert!(!matches_pattern(&bv_var("x", 32), &p));
    }

    #[test]
    fn test_matches_compound_pattern() {
        let p = FormulaPattern::And(vec![
            FormulaPattern::Gt(
                Box::new(FormulaPattern::AnyVar(Sort::Int)),
                Box::new(FormulaPattern::Int(0)),
            ),
            FormulaPattern::Lt(
                Box::new(FormulaPattern::AnyVar(Sort::Int)),
                Box::new(FormulaPattern::Int(10)),
            ),
        ]);

        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        assert!(matches_pattern(&f, &p));
    }

    #[test]
    fn test_matches_wrong_arity_and() {
        let p = FormulaPattern::And(vec![FormulaPattern::Bool(true)]);
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert!(!matches_pattern(&f, &p), "different arity should not match");
    }

    #[test]
    fn test_matches_wrong_constructor() {
        let p = FormulaPattern::Gt(
            Box::new(FormulaPattern::AnyVar(Sort::Int)),
            Box::new(FormulaPattern::Int(0)),
        );
        // Lt instead of Gt
        let f = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert!(!matches_pattern(&f, &p));
    }

    #[test]
    fn test_matches_bvadd_width_mismatch() {
        let p = FormulaPattern::BvAdd(
            Box::new(FormulaPattern::AnyVar(Sort::BitVec(32))),
            Box::new(FormulaPattern::AnyVar(Sort::BitVec(32))),
            32,
        );
        let f = Formula::BvAdd(Box::new(bv_var("a", 64)), Box::new(bv_var("b", 64)), 64);
        assert!(!matches_pattern(&f, &p), "width mismatch should not match");
    }

    #[test]
    fn test_matches_ite_pattern() {
        let p = FormulaPattern::Ite(
            Box::new(FormulaPattern::Wildcard(WildcardId(0))),
            Box::new(FormulaPattern::Wildcard(WildcardId(1))),
            Box::new(FormulaPattern::Wildcard(WildcardId(2))),
        );
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        assert!(matches_pattern(&f, &p));
    }

    #[test]
    fn test_matches_forall_sort_mismatch() {
        let p = FormulaPattern::Forall(
            vec![Sort::Int],
            Box::new(FormulaPattern::Wildcard(WildcardId(0))),
        );
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Bool)],
            Box::new(Formula::Bool(true)),
        );
        assert!(!matches_pattern(&f, &p), "sort mismatch in quantifier");
    }

    #[test]
    fn test_matches_forall_arity_mismatch() {
        let p = FormulaPattern::Forall(
            vec![Sort::Int, Sort::Int],
            Box::new(FormulaPattern::Wildcard(WildcardId(0))),
        );
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        );
        assert!(!matches_pattern(&f, &p), "arity mismatch in quantifier");
    }

    // -----------------------------------------------------------------------
    // Roundtrip: extract then match
    // -----------------------------------------------------------------------

    #[test]
    fn test_roundtrip_extract_then_match_variables() {
        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let p = extract_pattern(&f, GeneralizationLevel::Variables);
        assert!(matches_pattern(&f, &p), "formula should match its own extracted pattern");
    }

    #[test]
    fn test_roundtrip_extract_then_match_different_vars() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)));
        let p = extract_pattern(&f1, GeneralizationLevel::Variables);
        assert!(
            matches_pattern(&f2, &p),
            "different variable names should match with AnyVar"
        );
    }

    #[test]
    fn test_roundtrip_literals_level_matches_different_constants() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(99)));
        let p = extract_pattern(&f1, GeneralizationLevel::Literals);
        assert!(
            matches_pattern(&f2, &p),
            "literals-level pattern should match different constants"
        );
    }

    #[test]
    fn test_roundtrip_leaves_level_very_general() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Gt(Box::new(Formula::Int(100)), Box::new(var("z")));
        let p = extract_pattern(&f1, GeneralizationLevel::Leaves);
        assert!(
            matches_pattern(&f2, &p),
            "leaves-level pattern should match any Gt"
        );
    }

    // -----------------------------------------------------------------------
    // pattern_fingerprint tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fingerprint_deterministic() {
        let p = FormulaPattern::Gt(
            Box::new(FormulaPattern::AnyVar(Sort::Int)),
            Box::new(FormulaPattern::Int(0)),
        );
        let h1 = pattern_fingerprint(&p);
        let h2 = pattern_fingerprint(&p);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64);
    }

    #[test]
    fn test_fingerprint_different_patterns() {
        let p1 = FormulaPattern::Gt(
            Box::new(FormulaPattern::AnyVar(Sort::Int)),
            Box::new(FormulaPattern::Int(0)),
        );
        let p2 = FormulaPattern::Lt(
            Box::new(FormulaPattern::AnyVar(Sort::Int)),
            Box::new(FormulaPattern::Int(0)),
        );
        assert_ne!(pattern_fingerprint(&p1), pattern_fingerprint(&p2));
    }

    #[test]
    fn test_fingerprint_same_structure_same_hash() {
        // Two patterns with same structure should hash the same
        let p1 = FormulaPattern::And(vec![
            FormulaPattern::AnyVar(Sort::Int),
            FormulaPattern::Bool(true),
        ]);
        let p2 = FormulaPattern::And(vec![
            FormulaPattern::AnyVar(Sort::Int),
            FormulaPattern::Bool(true),
        ]);
        assert_eq!(pattern_fingerprint(&p1), pattern_fingerprint(&p2));
    }

    // -----------------------------------------------------------------------
    // pattern_size tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_pattern_size_leaf() {
        assert_eq!(pattern_size(&FormulaPattern::Bool(true)), 1);
        assert_eq!(pattern_size(&FormulaPattern::Int(42)), 1);
        assert_eq!(pattern_size(&FormulaPattern::AnyVar(Sort::Int)), 1);
        assert_eq!(pattern_size(&FormulaPattern::Wildcard(WildcardId(0))), 1);
    }

    #[test]
    fn test_pattern_size_compound() {
        let p = FormulaPattern::Gt(
            Box::new(FormulaPattern::AnyVar(Sort::Int)),
            Box::new(FormulaPattern::Int(0)),
        );
        assert_eq!(pattern_size(&p), 3);
    }

    #[test]
    fn test_pattern_size_and() {
        let p = FormulaPattern::And(vec![
            FormulaPattern::Bool(true),
            FormulaPattern::Bool(false),
        ]);
        assert_eq!(pattern_size(&p), 3);
    }
}
