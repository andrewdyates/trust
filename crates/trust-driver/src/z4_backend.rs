// trust-driver/z4_backend.rs (moved from trust-router): Z4 SMT solver backend
//
// NOTE: This is the canonical z4 integration for tRust. It will be migrated
// to a standalone trust-z4 crate as part of native compiler integration
// (issue #1, master plan epic 2). The trust-driver wrapper is deprecated,
// but this module is not — it is production code that will move.
//
// Encodes trust-types Formula into z4's native Rust API and checks SAT/UNSAT.
// Convention: we assert the negation of the property. UNSAT = property holds.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use num_bigint::BigInt;
use trust_router::VerificationBackend;
use trust_types::*;
use z4::api::{Logic, ModelValue, SolveResult, Sort as Z4Sort};
use z4::{BitVecSort, Solver};

pub(crate) struct Z4Backend;

impl Z4Backend {
    pub(crate) fn new() -> Self {
        Z4Backend
    }
}

impl Default for Z4Backend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for Z4Backend {
    fn name(&self) -> &str {
        "z4"
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // z4 handles all L0 safety properties
        matches!(vc.kind.proof_level(), ProofLevel::L0Safety | ProofLevel::L1Functional)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = std::time::Instant::now();

        // Choose logic based on formula content
        let logic = choose_logic(&vc.formula);
        let mut solver = match Solver::try_new(logic) {
            Ok(s) => s,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "z4".to_string(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: format!("solver creation failed: {e}"),
                };
            }
        };

        // Track declared variables for counterexample extraction
        let mut var_terms = FxHashMap::default();

        // Encode and assert the formula
        let term = match encode_formula(&mut solver, &vc.formula, &mut var_terms) {
            Ok(t) => t,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "z4".to_string(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: format!("encoding failed: {e}"),
                };
            }
        };

        if solver.try_assert_term(term).is_err() {
            return VerificationResult::Unknown {
                solver: "z4".to_string(),
                time_ms: start.elapsed().as_millis() as u64,
                reason: "assert failed".to_string(),
            };
        }

        // Check satisfiability
        let details = solver.check_sat_with_details();
        let elapsed = start.elapsed().as_millis() as u64;

        match details.accept_for_consumer() {
            Ok(SolveResult::Unsat(_)) => VerificationResult::Proved {
                solver: "z4".to_string(),
                time_ms: elapsed,
                strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
            Ok(SolveResult::Sat) => {
                let counterexample = extract_counterexample(&solver, &var_terms);
                VerificationResult::Failed {
                    solver: "z4".to_string(),
                    time_ms: elapsed,
                    counterexample: Some(counterexample),
                }
            }
            Ok(SolveResult::Unknown) | Err(_) => VerificationResult::Unknown {
                solver: "z4".to_string(),
                time_ms: elapsed,
                reason: details
                    .unknown_reason
                    .map(|r| format!("{r:?}"))
                    .unwrap_or_else(|| "unknown".to_string()),
            },
            _ => VerificationResult::Unknown {
                solver: "z4".to_string(),
                time_ms: elapsed,
                reason: "unexpected result".to_string(),
            },
        }
    }
}

/// Choose the appropriate SMT logic for a formula.
fn choose_logic(formula: &Formula) -> Logic {
    if has_bitvectors(formula) { Logic::QfBv } else { Logic::QfLia }
}

fn has_bitvectors(formula: &Formula) -> bool {
    match formula {
        Formula::BitVec { .. }
        | Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvNot(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..) => true,
        Formula::Var(_, Sort::BitVec(_)) => true,
        Formula::Not(inner) => has_bitvectors(inner),
        Formula::And(terms) | Formula::Or(terms) => terms.iter().any(has_bitvectors),
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
        | Formula::Rem(a, b) => has_bitvectors(a) || has_bitvectors(b),
        Formula::Ite(c, t, e) => has_bitvectors(c) || has_bitvectors(t) || has_bitvectors(e),
        Formula::Neg(inner) => has_bitvectors(inner),
        Formula::Forall(_, body) | Formula::Exists(_, body) => has_bitvectors(body),
        _ => false,
    }
}

type Z4Term = z4::api::Term;

/// Encode a trust-types Formula into z4 terms.
fn encode_formula(
    solver: &mut Solver,
    formula: &Formula,
    vars: &mut FxHashMap<String, Z4Term>,
) -> Result<Z4Term, String> {
    match formula {
        Formula::Bool(b) => Ok(solver.bool_const(*b)),
        Formula::Int(n) => {
            if *n >= i64::MIN as i128 && *n <= i64::MAX as i128 {
                Ok(solver.int_const(*n as i64))
            } else {
                Ok(solver.int_const_bigint(&BigInt::from(*n)))
            }
        }
        Formula::BitVec { value, width } => {
            if *value >= i64::MIN as i128 && *value <= i64::MAX as i128 {
                solver.try_bv_const(*value as i64, *width).map_err(|e| format!("bv_const: {e}"))
            } else {
                solver
                    .try_bv_const_bigint(&BigInt::from(*value), *width)
                    .map_err(|e| format!("bv_const_bigint: {e}"))
            }
        }
        Formula::Var(name, sort) => {
            if let Some(term) = vars.get(name) {
                Ok(*term)
            } else {
                let z4_sort = to_z4_sort(sort);
                let term = solver.declare_const(name, z4_sort);
                vars.insert(name.clone(), term);
                Ok(term)
            }
        }
        Formula::Not(inner) => {
            let t = encode_formula(solver, inner, vars)?;
            solver.try_not(t).map_err(|e| format!("not: {e}"))
        }
        Formula::And(terms) => {
            if terms.is_empty() {
                return Ok(solver.bool_const(true));
            }
            let encoded: Result<Vec<_>, _> =
                terms.iter().map(|t| encode_formula(solver, t, vars)).collect();
            let encoded = encoded?;
            solver.try_and_many(&encoded).map_err(|e| format!("and: {e}"))
        }
        Formula::Or(terms) => {
            if terms.is_empty() {
                return Ok(solver.bool_const(false));
            }
            let encoded: Result<Vec<_>, _> =
                terms.iter().map(|t| encode_formula(solver, t, vars)).collect();
            let encoded = encoded?;
            solver.try_or_many(&encoded).map_err(|e| format!("or: {e}"))
        }
        Formula::Implies(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_implies(l, r).map_err(|e| format!("implies: {e}"))
        }
        Formula::Eq(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_eq(l, r).map_err(|e| format!("eq: {e}"))
        }
        Formula::Lt(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_lt(l, r).map_err(|e| format!("lt: {e}"))
        }
        Formula::Le(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_le(l, r).map_err(|e| format!("le: {e}"))
        }
        Formula::Gt(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_gt(l, r).map_err(|e| format!("gt: {e}"))
        }
        Formula::Ge(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_ge(l, r).map_err(|e| format!("ge: {e}"))
        }
        Formula::Add(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_add(l, r).map_err(|e| format!("add: {e}"))
        }
        Formula::Sub(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_sub(l, r).map_err(|e| format!("sub: {e}"))
        }
        Formula::Mul(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_mul(l, r).map_err(|e| format!("mul: {e}"))
        }
        Formula::Div(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_div(l, r).map_err(|e| format!("div: {e}"))
        }
        // tRust #166: Remainder uses SMT `mod` (z4's try_modulo)
        Formula::Rem(a, b) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_modulo(l, r).map_err(|e| format!("rem/mod: {e}"))
        }
        Formula::Neg(inner) => {
            let t = encode_formula(solver, inner, vars)?;
            solver.try_neg(t).map_err(|e| format!("neg: {e}"))
        }
        Formula::Ite(cond, then, els) => {
            let c = encode_formula(solver, cond, vars)?;
            let t = encode_formula(solver, then, vars)?;
            let e = encode_formula(solver, els, vars)?;
            solver.try_ite(c, t, e).map_err(|e| format!("ite: {e}"))
        }
        // tRust #166: Array theory — select and store
        Formula::Select(arr, idx) => {
            let a = encode_formula(solver, arr, vars)?;
            let i = encode_formula(solver, idx, vars)?;
            solver.try_select(a, i).map_err(|e| format!("select: {e}"))
        }
        Formula::Store(arr, idx, val) => {
            let a = encode_formula(solver, arr, vars)?;
            let i = encode_formula(solver, idx, vars)?;
            let v = encode_formula(solver, val, vars)?;
            solver.try_store(a, i, v).map_err(|e| format!("store: {e}"))
        }
        // BV operations — pass through to z4's BV API
        Formula::BvAdd(a, b, w) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            let _ = w; // width is implicit in the terms
            solver.try_bvadd(l, r).map_err(|e| format!("bvadd: {e}"))
        }
        Formula::BvSub(a, b, _) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_bvsub(l, r).map_err(|e| format!("bvsub: {e}"))
        }
        Formula::BvMul(a, b, _) => {
            let l = encode_formula(solver, a, vars)?;
            let r = encode_formula(solver, b, vars)?;
            solver.try_bvmul(l, r).map_err(|e| format!("bvmul: {e}"))
        }
        // For remaining BV ops, return a placeholder — will be extended
        _ => Err(format!("unsupported formula variant: {formula:?}")),
    }
}

fn to_z4_sort(sort: &Sort) -> Z4Sort {
    match sort {
        Sort::Bool => Z4Sort::Bool,
        Sort::Int => Z4Sort::Int,
        Sort::BitVec(w) => Z4Sort::BitVec(BitVecSort::new(*w)),
        Sort::Array(idx, elem) => {
            Z4Sort::Array(Box::new(z4::ArraySort::new(to_z4_sort(idx), to_z4_sort(elem))))
        }
    }
}

/// Extract a counterexample from the solver's model.
fn extract_counterexample(solver: &Solver, var_terms: &FxHashMap<String, Z4Term>) -> Counterexample {
    let mut assignments = Vec::new();

    for (name, term) in var_terms {
        if let Some(model_val) = solver.value(*term) {
            let value = match model_val {
                ModelValue::Bool(b) => CounterexampleValue::Bool(b),
                ModelValue::Int(n) => {
                    if let Ok(v) = i128::try_from(&n) {
                        if v >= 0 {
                            CounterexampleValue::Uint(v as u128)
                        } else {
                            CounterexampleValue::Int(v)
                        }
                    } else {
                        CounterexampleValue::Int(0) // fallback for huge values
                    }
                }
                ModelValue::BitVec { value: n, .. } => {
                    if let Ok(v) = u128::try_from(&n) {
                        CounterexampleValue::Uint(v)
                    } else if let Ok(v) = i128::try_from(&n) {
                        CounterexampleValue::Int(v)
                    } else {
                        CounterexampleValue::Uint(0)
                    }
                }
                _ => continue,
            };
            assignments.push((name.clone(), value));
        }
    }

    // Sort by name for deterministic output
    assignments.sort_by(|a, b| a.0.cmp(&b.0));
    Counterexample::new(assignments)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_z4_proves_trivially_unsat() {
        // Formula: false (trivially UNSAT)
        let backend = Z4Backend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
        };
        let result = backend.verify(&vc);
        assert!(result.is_proved(), "false should be UNSAT → proved");
    }

    #[test]
    fn test_z4_finds_trivially_sat() {
        // Formula: true (trivially SAT)
        let backend = Z4Backend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
        };
        let result = backend.verify(&vc);
        assert!(result.is_failed(), "true should be SAT → failed");
    }

    #[test]
    fn test_z4_proves_division_safe() {
        // For midpoint: divisor is constant 2, which is never 0
        // Formula: 2 == 0 (should be UNSAT → proved safe)
        let backend = Z4Backend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "get_midpoint".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0))),
        };
        let result = backend.verify(&vc);
        assert!(result.is_proved(), "2 == 0 should be UNSAT → proved safe");
    }

    #[test]
    fn test_z4_detects_overflow() {
        // The midpoint overflow:
        // a, b: usize (0..2^64-1)
        // a + b can exceed 2^64-1
        // VC: exists a, b in [0, 2^64-1] such that a + b > 2^64-1
        //
        // Since z4 uses mathematical integers in QfLia, this is:
        // a >= 0 AND a <= MAX AND b >= 0 AND b <= MAX AND NOT(a + b >= 0 AND a + b <= MAX)
        let max_val = (1i128 << 64) - 1;
        let a = Formula::Var("a".into(), Sort::Int);
        let b = Formula::Var("b".into(), Sort::Int);
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));

        let formula = Formula::And(vec![
            // a in [0, MAX]
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a), Box::new(Formula::Int(max_val))),
            // b in [0, MAX]
            Formula::Le(Box::new(Formula::Int(0)), Box::new(b.clone())),
            Formula::Le(Box::new(b), Box::new(Formula::Int(max_val))),
            // NOT(sum in [0, MAX])
            Formula::Not(Box::new(Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(sum.clone())),
                Formula::Le(Box::new(sum), Box::new(Formula::Int(max_val))),
            ]))),
        ]);

        let backend = Z4Backend::new();
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "get_midpoint".to_string(),
            location: SourceSpan::default(),
            formula,
        };

        let result = backend.verify(&vc);
        assert!(result.is_failed(), "usize overflow should be SAT (violation found)");

        // Extract counterexample
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert!(!cex.assignments.is_empty(), "must provide counterexample values");
            // The counterexample should show values where a + b > MAX
            println!("Counterexample: {cex}");
        }
    }

    #[test]
    fn test_z4_variable_divzero() {
        // For div_by_var: b == 0 where b is unrestricted
        // Should be SAT (b can be 0)
        let backend = Z4Backend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "div_by_var".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        };
        let result = backend.verify(&vc);
        assert!(result.is_failed(), "unrestricted variable can be 0 → division possible");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert!(cex.assignments.iter().any(|(name, _)| name == "b"));
        }
    }
}
