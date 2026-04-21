// trust-vcgen/quantifier_elim.rs: Quantifier elimination for verification conditions
//
// Attempts to remove universal and existential quantifiers from VCs via
// Skolemization, universal instantiation, and heuristic term selection.
// When exact elimination is not possible, returns an approximation or failure.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{Formula, Sort};

/// Whether a quantifier is universal or existential.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifierKind {
    Forall,
    Exists,
}

/// A quantified formula with its kind, bound variables, and body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedFormula {
    pub kind: QuantifierKind,
    pub bound_vars: Vec<(String, Sort)>,
    pub body: Formula,
}

impl QuantifiedFormula {
    /// Construct from a top-level `Formula::Forall` or `Formula::Exists`.
    /// Returns `None` if the formula is not quantified.
    #[must_use]
    pub fn from_formula(formula: &Formula) -> Option<Self> {
        match formula {
            Formula::Forall(vars, body) => Some(Self {
                kind: QuantifierKind::Forall,
                bound_vars: vars.clone(),
                body: *body.clone(),
            }),
            Formula::Exists(vars, body) => Some(Self {
                kind: QuantifierKind::Exists,
                bound_vars: vars.clone(),
                body: *body.clone(),
            }),
            _ => None,
        }
    }

    /// Convert back to a `Formula`.
    #[must_use]
    pub fn to_formula(&self) -> Formula {
        match self.kind {
            QuantifierKind::Forall => {
                Formula::Forall(self.bound_vars.clone(), Box::new(self.body.clone()))
            }
            QuantifierKind::Exists => {
                Formula::Exists(self.bound_vars.clone(), Box::new(self.body.clone()))
            }
        }
    }
}

/// Result of attempting quantifier elimination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EliminationResult {
    /// Exact elimination: the result is logically equivalent.
    Eliminated(Formula),
    /// Approximate elimination: sound over-approximation for verification.
    Approximated(Formula),
    /// Could not eliminate the quantifier.
    Failed,
}

impl EliminationResult {
    /// Extract the formula if elimination succeeded (exact or approximate).
    #[must_use]
    pub fn formula(&self) -> Option<&Formula> {
        match self {
            Self::Eliminated(f) | Self::Approximated(f) => Some(f),
            Self::Failed => None,
        }
    }

    /// Returns `true` if exact elimination succeeded.
    #[must_use]
    pub fn is_eliminated(&self) -> bool {
        matches!(self, Self::Eliminated(_))
    }
}

// ---------------------------------------------------------------------------
// Core elimination entry point
// ---------------------------------------------------------------------------

/// Attempt to eliminate quantifiers from a formula.
///
/// Strategy:
/// 1. If the formula has no quantifiers, return it as-is.
/// 2. For existential quantifiers: Skolemize (replace bound vars with Skolem
///    function applications over free variables).
/// 3. For universal quantifiers: attempt heuristic instantiation, falling back
///    to `Failed` if no good terms can be found.
#[must_use]
pub fn eliminate_quantifier(formula: &Formula) -> EliminationResult {
    match formula {
        Formula::Exists(vars, body) => {
            let skolemized = skolemize_inner(vars, body, &free_vars(formula));
            EliminationResult::Eliminated(skolemized)
        }
        Formula::Forall(vars, body) => {
            let terms = heuristic_instantiation(vars, body);
            if terms.is_empty() {
                EliminationResult::Failed
            } else {
                let instantiated = instantiate_universal(vars, body, &terms);
                EliminationResult::Approximated(instantiated)
            }
        }
        // No top-level quantifier: already quantifier-free.
        other => EliminationResult::Eliminated(other.clone()),
    }
}

// ---------------------------------------------------------------------------
// Skolemization
// ---------------------------------------------------------------------------

/// Replace existentially-bound variables with Skolem function applications.
///
/// Given `exists x, y. P(x, y, z)` where `z` is free, produce
/// `P(skolem_x(z), skolem_y(z), z)`.
///
/// For verification, Skolemization is exact for existentials: the resulting
/// formula is equisatisfiable.
#[must_use]
pub fn skolemize(formula: &Formula) -> Formula {
    match formula {
        Formula::Exists(vars, body) => {
            let fv = free_vars(formula);
            skolemize_inner(vars, body, &fv)
        }
        other => other.clone(),
    }
}

/// Inner Skolemization: substitute each bound variable with a Skolem constant
/// (0 free vars) or Skolem function application (>0 free vars).
fn skolemize_inner(
    bound: &[(String, Sort)],
    body: &Formula,
    free: &FxHashMap<String, Sort>,
) -> Formula {
    let mut result = body.clone();
    for (name, sort) in bound {
        let skolem_name = if free.is_empty() {
            format!("skolem_{name}")
        } else {
            // Encode dependency on free variables in the name.
            let deps: Vec<&str> = free.keys().map(String::as_str).collect();
            format!("skolem_{name}_{}", deps.join("_"))
        };
        let replacement = Formula::Var(skolem_name, sort.clone());
        result = substitute(&result, name, &replacement);
    }
    result
}

// ---------------------------------------------------------------------------
// Universal instantiation
// ---------------------------------------------------------------------------

/// Substitute universally-bound variables with the given terms.
///
/// Given `forall x1, x2. P(x1, x2)` and terms `[t1, t2]`, produce
/// `P(t1, t2)`. If fewer terms than bound vars, only the first N are
/// substituted and remaining quantifiers are kept.
#[must_use]
pub fn instantiate_universal(
    bound: &[(String, Sort)],
    body: &Formula,
    terms: &[Formula],
) -> Formula {
    let mut result = body.clone();
    let mut remaining_vars = Vec::new();

    for (i, (name, sort)) in bound.iter().enumerate() {
        if let Some(term) = terms.get(i) {
            result = substitute(&result, name, term);
        } else {
            remaining_vars.push((name.clone(), sort.clone()));
        }
    }

    if remaining_vars.is_empty() {
        result
    } else {
        Formula::Forall(remaining_vars, Box::new(result))
    }
}

// ---------------------------------------------------------------------------
// Heuristic instantiation
// ---------------------------------------------------------------------------

/// Choose instantiation terms for universally-bound variables by inspecting
/// the body formula for useful patterns.
///
/// Heuristics (in priority order):
/// 1. Constants appearing in comparisons with the bound variable.
/// 2. Boundary values (0 for Int, `false` for Bool).
/// 3. Other free variables of matching sort.
#[must_use]
pub fn heuristic_instantiation(
    bound: &[(String, Sort)],
    body: &Formula,
) -> Vec<Formula> {
    let constants = collect_comparison_constants(body);
    let free = free_vars_in(body);

    bound
        .iter()
        .filter_map(|(name, sort)| {
            // Heuristic 1: constants from comparisons with this variable.
            if let Some(c) = constants.get(name) {
                return Some(c.clone());
            }
            // Heuristic 2: boundary values by sort.
            match sort {
                Sort::Int => Some(Formula::Int(0)),
                Sort::Bool => Some(Formula::Bool(true)),
                Sort::BitVec(w) => Some(Formula::BitVec { value: 0, width: *w }),
                // Heuristic 3: any free variable of matching sort.
                Sort::Array(..) => {
                    free.iter()
                        .find(|(n, s)| s == sort && n != name)
                        .map(|(n, s)| Formula::Var(n.clone(), s.clone()))
                }
                _ => Some(Formula::Bool(false)),
            }
        })
        .collect()
}

/// Scan comparisons (`Eq`, `Lt`, `Le`, `Gt`, `Ge`) for constants paired
/// with a variable name.
fn collect_comparison_constants(formula: &Formula) -> FxHashMap<String, Formula> {
    let mut result = FxHashMap::default();
    collect_comparison_constants_rec(formula, &mut result);
    result
}

fn collect_comparison_constants_rec(formula: &Formula, out: &mut FxHashMap<String, Formula>) {
    match formula {
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            if let Formula::Var(name, _) = lhs.as_ref()
                && is_constant(rhs) {
                    out.entry(name.clone()).or_insert_with(|| *rhs.clone());
                }
            if let Formula::Var(name, _) = rhs.as_ref()
                && is_constant(lhs) {
                    out.entry(name.clone()).or_insert_with(|| *lhs.clone());
                }
        }
        _ => {
            for child in formula.children() {
                collect_comparison_constants_rec(child, out);
            }
        }
    }
}

fn is_constant(f: &Formula) -> bool {
    matches!(f, Formula::Int(_) | Formula::UInt(_) | Formula::Bool(_) | Formula::BitVec { .. })
}

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Replace all occurrences of `Var(name, _)` in `formula` with `replacement`.
#[must_use]
pub fn substitute(formula: &Formula, name: &str, replacement: &Formula) -> Formula {
    match formula {
        Formula::Var(n, _) if n == name => replacement.clone(),
        // Do not descend into quantifiers that rebind the same name.
        Formula::Forall(vars, body) if vars.iter().any(|(n, _)| n == name) => formula.clone(),
        Formula::Exists(vars, body) if vars.iter().any(|(n, _)| n == name) => formula.clone(),
        Formula::Forall(vars, body) => {
            Formula::Forall(vars.clone(), Box::new(substitute(body, name, replacement)))
        }
        Formula::Exists(vars, body) => {
            Formula::Exists(vars.clone(), Box::new(substitute(body, name, replacement)))
        }
        other => {
            // Use map_children for all structural recursion.
            other.clone().map_children(&mut |child| substitute(&child, name, replacement))
        }
    }
}

// ---------------------------------------------------------------------------
// Free variable collection
// ---------------------------------------------------------------------------

/// Collect free variables (name -> sort) in a formula.
fn free_vars(formula: &Formula) -> FxHashMap<String, Sort> {
    let mut fv = FxHashMap::default();
    let mut bound: FxHashSet<String> = FxHashSet::default();
    free_vars_rec(formula, &mut bound, &mut fv);
    fv
}

/// Like `free_vars` but ignores quantifier scoping (just collects all `Var` nodes).
fn free_vars_in(formula: &Formula) -> Vec<(String, Sort)> {
    let mut result = Vec::new();
    let mut seen = FxHashSet::default();
    collect_all_vars(formula, &mut seen, &mut result);
    result
}

fn free_vars_rec(
    formula: &Formula,
    bound: &mut FxHashSet<String>,
    out: &mut FxHashMap<String, Sort>,
) {
    match formula {
        Formula::Var(name, sort) => {
            if !bound.contains(name) {
                out.entry(name.clone()).or_insert_with(|| sort.clone());
            }
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            for (n, _) in vars {
                bound.insert(n.clone());
            }
            free_vars_rec(body, bound, out);
            for (n, _) in vars {
                bound.remove(n);
            }
        }
        other => {
            for child in other.children() {
                free_vars_rec(child, bound, out);
            }
        }
    }
}

fn collect_all_vars(
    formula: &Formula,
    seen: &mut FxHashSet<String>,
    out: &mut Vec<(String, Sort)>,
) {
    match formula {
        Formula::Var(name, sort) => {
            if seen.insert(name.clone()) {
                out.push((name.clone(), sort.clone()));
            }
        }
        _ => {
            for child in formula.children() {
                collect_all_vars(child, seen, out);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Bool)
    }

    // ----- QuantifierKind -----

    #[test]
    fn test_quantifier_kind_equality() {
        assert_eq!(QuantifierKind::Forall, QuantifierKind::Forall);
        assert_ne!(QuantifierKind::Forall, QuantifierKind::Exists);
    }

    // ----- QuantifiedFormula -----

    #[test]
    fn test_quantified_formula_from_forall() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        let qf = QuantifiedFormula::from_formula(&f).unwrap();
        assert_eq!(qf.kind, QuantifierKind::Forall);
        assert_eq!(qf.bound_vars.len(), 1);
        assert_eq!(qf.bound_vars[0].0, "x");
    }

    #[test]
    fn test_quantified_formula_from_exists() {
        let f = Formula::Exists(
            vec![("y".into(), Sort::Bool)],
            Box::new(bool_var("y")),
        );
        let qf = QuantifiedFormula::from_formula(&f).unwrap();
        assert_eq!(qf.kind, QuantifierKind::Exists);
        assert_eq!(qf.bound_vars[0].1, Sort::Bool);
    }

    #[test]
    fn test_quantified_formula_from_non_quantified() {
        assert!(QuantifiedFormula::from_formula(&Formula::Bool(true)).is_none());
    }

    #[test]
    fn test_quantified_formula_roundtrip() {
        let original = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(42)))),
        );
        let qf = QuantifiedFormula::from_formula(&original).unwrap();
        assert_eq!(qf.to_formula(), original);
    }

    // ----- EliminationResult -----

    #[test]
    fn test_elimination_result_accessors() {
        let elim = EliminationResult::Eliminated(Formula::Bool(true));
        assert!(elim.is_eliminated());
        assert_eq!(elim.formula(), Some(&Formula::Bool(true)));

        let approx = EliminationResult::Approximated(Formula::Bool(false));
        assert!(!approx.is_eliminated());
        assert!(approx.formula().is_some());

        let failed = EliminationResult::Failed;
        assert!(failed.formula().is_none());
    }

    // ----- Skolemization -----

    #[test]
    fn test_skolemize_replaces_bound_var() {
        // exists x. x > 0  =>  skolem_x > 0
        let f = Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        let result = skolemize(&f);
        match &result {
            Formula::Gt(lhs, _) => {
                if let Formula::Var(name, sort) = lhs.as_ref() {
                    assert!(name.starts_with("skolem_x"), "got {name}");
                    assert_eq!(*sort, Sort::Int);
                } else {
                    panic!("expected Var, got {lhs:?}");
                }
            }
            other => panic!("expected Gt, got {other:?}"),
        }
    }

    #[test]
    fn test_skolemize_non_existential_is_identity() {
        let f = Formula::Bool(true);
        assert_eq!(skolemize(&f), f);
    }

    #[test]
    fn test_skolemize_with_free_vars_encodes_dependency() {
        // exists x. x > z  (z is free)
        let body = Formula::Gt(Box::new(int_var("x")), Box::new(int_var("z")));
        let f = Formula::Exists(vec![("x".into(), Sort::Int)], Box::new(body));
        let result = skolemize(&f);
        // The Skolem name should mention z.
        match &result {
            Formula::Gt(lhs, _) => {
                if let Formula::Var(name, _) = lhs.as_ref() {
                    assert!(name.contains("skolem_x"), "got {name}");
                    assert!(name.contains("z"), "Skolem should depend on free var z: {name}");
                } else {
                    panic!("expected Var");
                }
            }
            other => panic!("expected Gt, got {other:?}"),
        }
    }

    // ----- Universal instantiation -----

    #[test]
    fn test_instantiate_universal_single_var() {
        // forall x. x > 0  with x := 42  =>  42 > 0
        let bound = vec![("x".into(), Sort::Int)];
        let body = Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let result = instantiate_universal(&bound, &body, &[Formula::Int(42)]);
        assert_eq!(
            result,
            Formula::Gt(Box::new(Formula::Int(42)), Box::new(Formula::Int(0)))
        );
    }

    #[test]
    fn test_instantiate_universal_partial() {
        // forall x, y. x + y > 0  with only x := 1
        let bound = vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)];
        let body = Formula::Gt(
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(0)),
        );
        let result = instantiate_universal(&bound, &body, &[Formula::Int(1)]);
        // Should still have forall y
        match &result {
            Formula::Forall(vars, _) => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "y");
            }
            other => panic!("expected remaining Forall, got {other:?}"),
        }
    }

    // ----- Heuristic instantiation -----

    #[test]
    fn test_heuristic_instantiation_from_comparison() {
        // forall x. x > 5 => P(x)
        let bound = vec![("x".into(), Sort::Int)];
        let body = Formula::Implies(
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(5)))),
            Box::new(Formula::Bool(true)),
        );
        let terms = heuristic_instantiation(&bound, &body);
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0], Formula::Int(5));
    }

    #[test]
    fn test_heuristic_instantiation_fallback_to_zero() {
        // forall x. P(x) where body has no comparisons with constants
        let bound = vec![("x".into(), Sort::Int)];
        let body = Formula::Bool(true);
        let terms = heuristic_instantiation(&bound, &body);
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0], Formula::Int(0));
    }

    #[test]
    fn test_heuristic_instantiation_bool_fallback() {
        let bound = vec![("b".into(), Sort::Bool)];
        let body = Formula::Bool(true);
        let terms = heuristic_instantiation(&bound, &body);
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0], Formula::Bool(true));
    }

    // ----- eliminate_quantifier (integration) -----

    #[test]
    fn test_eliminate_quantifier_existential() {
        let f = Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(7)))),
        );
        let result = eliminate_quantifier(&f);
        assert!(result.is_eliminated());
        // The result should replace x with a Skolem constant.
        assert!(result.formula().is_some());
    }

    #[test]
    fn test_eliminate_quantifier_universal_with_hint() {
        // forall x. x == 10  =>  approximated with x := 10
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
        );
        let result = eliminate_quantifier(&f);
        match &result {
            EliminationResult::Approximated(formula) => {
                // Should be 10 == 10
                assert_eq!(
                    *formula,
                    Formula::Eq(Box::new(Formula::Int(10)), Box::new(Formula::Int(10)))
                );
            }
            other => panic!("expected Approximated, got {other:?}"),
        }
    }

    #[test]
    fn test_eliminate_quantifier_no_quantifier() {
        let f = Formula::Bool(false);
        let result = eliminate_quantifier(&f);
        assert!(result.is_eliminated());
        assert_eq!(result.formula(), Some(&Formula::Bool(false)));
    }

    // ----- Substitution edge cases -----

    #[test]
    fn test_substitute_respects_shadowing() {
        // forall x. (exists x. x > 0)  — inner x should NOT be substituted
        let inner = Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        let outer = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(inner.clone()),
        );
        // Substituting x in the outer formula should not change the inner.
        let result = substitute(&outer, "x", &Formula::Int(999));
        // The inner exists should be unchanged.
        match &result {
            Formula::Forall(_, body) => {
                assert_eq!(body.as_ref(), &inner);
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }
}
