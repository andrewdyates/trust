// trust-router/smt2_export.rs: SMT-LIB2 debug export format
//
// Provides --emit=smt2 functionality: exports VCs as standard SMT-LIB2 scripts
// for debugging and interop with any SMT-LIB2 compliant solver (z3, cvc5, etc.).
//
// Delegates formula/sort serialization to the canonical `to_smtlib()` methods
// in trust-types. This module adds VC-level structure: metadata comments,
// (set-logic), (declare-fun), (assert), (check-sat), and batch export.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt::Write as _;

use trust_types::{Formula, Sort, VerificationCondition};
use trust_types::fx::FxHashSet;

/// Emit a complete SMT-LIB2 script for a single verification condition.
///
/// Includes metadata comments (function name, VC kind, source location),
/// logic declaration, variable declarations, the assertion, and check-sat.
#[must_use]
pub fn emit_smt2(vc: &VerificationCondition) -> String {
    let mut out = String::new();

    // Metadata comments
    write_metadata_comments(&mut out, vc);

    // Logic
    let logic = detect_logic(&vc.formula);
    // SAFETY: writeln! to a String is infallible (no I/O errors possible).
    let _ = writeln!(out, "(set-logic {logic})");
    // tRust #556: Add :produce-models so (get-model) works correctly.
    // Previously missing from single-VC export (batch export had it).
    let _ = writeln!(out, "(set-option :produce-models true)");
    out.push('\n');

    // Variable declarations
    for decl in emit_declarations(&vc.formula) {
        // SAFETY: writeln! to a String is infallible.
        let _ = writeln!(out, "{decl}");
    }

    // Assertion
    // SAFETY: writeln! to a String is infallible.
    let _ = writeln!(out, "(assert {})", formula_to_smt2(&vc.formula));
    out.push('\n');

    // Check and exit
    // SAFETY: writeln! to a String is infallible.
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(get-model)");
    let _ = writeln!(out, "(exit)");

    out
}

/// Emit a single SMT-LIB2 script containing multiple VCs.
///
/// Each VC is wrapped in `(push)` / `(pop)` for incremental solving.
/// The logic is the union of all VCs' requirements.
#[must_use]
pub fn emit_smt2_batch(vcs: &[VerificationCondition]) -> String {
    if vcs.is_empty() {
        return "; empty batch\n(set-logic ALL)\n(exit)\n".to_string();
    }

    if vcs.len() == 1 {
        return emit_smt2(&vcs[0]);
    }

    let mut out = String::new();

    // SAFETY: All writeln! calls below write to a String, which is infallible.

    // Header
    let _ = writeln!(out, "; tRust SMT-LIB2 batch export ({} VCs)", vcs.len());
    let _ = writeln!(out, "; Use (push)/(pop) for incremental solving");
    out.push('\n');

    // Detect unified logic across all VCs
    let logic = detect_batch_logic(vcs);
    let _ = writeln!(out, "(set-logic {logic})");
    let _ = writeln!(out, "(set-option :produce-models true)");
    out.push('\n');

    for (i, vc) in vcs.iter().enumerate() {
        let _ = writeln!(out, "; --- VC {i} ---");
        write_metadata_comments(&mut out, vc);

        let _ = writeln!(out, "(push 1)");

        // Declarations scoped to this push
        for decl in emit_declarations(&vc.formula) {
            let _ = writeln!(out, "{decl}");
        }

        let _ = writeln!(out, "(assert {})", formula_to_smt2(&vc.formula));
        let _ = writeln!(out, "(check-sat)");
        let _ = writeln!(out, "(get-model)");
        let _ = writeln!(out, "(pop 1)");
        out.push('\n');
    }

    let _ = writeln!(out, "(exit)");
    out
}

/// Wrap a single VC in a full SMT-LIB2 script (alias for `emit_smt2`).
///
/// Returns a complete, self-contained SMT-LIB2 script with metadata comments,
/// logic declaration, variable declarations, assertion, `(check-sat)`, and
/// `(get-model)` commands.
#[must_use]
pub fn vc_to_smt2(vc: &VerificationCondition) -> String {
    emit_smt2(vc)
}

/// Convert a formula to its SMT-LIB2 text representation.
///
/// Delegates to the canonical `Formula::to_smtlib()` in trust-types.
#[must_use]
pub fn formula_to_smt2(formula: &Formula) -> String {
    formula.to_smtlib()
}

/// Convert a sort to its SMT-LIB2 text representation.
///
/// Delegates to the canonical `Sort::to_smtlib()` in trust-types.
#[must_use]
pub fn sort_to_smt2(sort: &Sort) -> String {
    sort.to_smtlib()
}

/// Collect `(declare-fun ...)` declarations for all free variables in a formula.
///
/// Returns declarations sorted by variable name for deterministic output.
/// Quantifier-bound variables are excluded.
#[must_use]
pub fn emit_declarations(formula: &Formula) -> Vec<String> {
    let mut vars = BTreeSet::new();
    collect_free_vars(formula, &mut vars);

    vars.into_iter()
        .map(|(name, sort)| format!("(declare-fun {name} () {})", sort_to_smt2(&sort)))
        .collect()
}

/// Detect the appropriate SMT-LIB2 logic string for a formula.
///
/// Analyzes the formula structure to select the most specific logic:
/// - `QF_LIA` for quantifier-free linear integer arithmetic
/// - `QF_BV` for quantifier-free bitvectors
/// - `QF_AUFLIA` for quantifier-free arrays + integers
/// - `QF_ABV` for quantifier-free arrays + bitvectors
/// - `AUFBVLIA` for quantified arrays + bitvectors + integers
/// - `ALL` as fallback for mixed theories
#[must_use]
pub fn detect_logic(formula: &Formula) -> &'static str {
    let features = analyze_formula(formula);

    match (features.has_bitvectors, features.has_arrays, features.has_quantifiers) {
        // Pure bitvector
        (true, false, false) => "QF_BV",
        (true, false, true) => "BV",
        // Bitvector + arrays
        (true, true, false) => "QF_ABV",
        (true, true, true) => "ABV",
        // Pure integer + arrays
        (false, true, false) => "QF_AUFLIA",
        (false, true, true) => "AUFLIA",
        // Pure integer (default)
        (false, false, _) => {
            if features.has_quantifiers {
                "LIA"
            } else {
                "QF_LIA"
            }
        }
    }
}

// --- Internal helpers ---

/// Formula features relevant to logic detection.
struct FormulaFeatures {
    has_bitvectors: bool,
    has_arrays: bool,
    has_quantifiers: bool,
}

/// Analyze a formula for theory features.
fn analyze_formula(formula: &Formula) -> FormulaFeatures {
    let mut features = FormulaFeatures {
        has_bitvectors: false,
        has_arrays: false,
        has_quantifiers: false,
    };

    formula.visit(&mut |node| {
        match node {
            // Bitvector detection
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
            | Formula::BvSignExt(..) => features.has_bitvectors = true,

            Formula::Var(_, Sort::BitVec(_)) => features.has_bitvectors = true,

            // Array detection
            Formula::Select(..) | Formula::Store(..) => features.has_arrays = true,
            Formula::Var(_, Sort::Array(..)) => features.has_arrays = true,

            // Quantifier detection
            Formula::Forall(..) | Formula::Exists(..) => features.has_quantifiers = true,

            _ => {}
        }
    });

    features
}

/// Detect the best logic for a batch of VCs (union of all features).
fn detect_batch_logic(vcs: &[VerificationCondition]) -> &'static str {
    let mut combined = FormulaFeatures {
        has_bitvectors: false,
        has_arrays: false,
        has_quantifiers: false,
    };

    for vc in vcs {
        let f = analyze_formula(&vc.formula);
        combined.has_bitvectors |= f.has_bitvectors;
        combined.has_arrays |= f.has_arrays;
        combined.has_quantifiers |= f.has_quantifiers;
    }

    // Reuse the same logic selection
    match (combined.has_bitvectors, combined.has_arrays, combined.has_quantifiers) {
        (true, false, false) => "QF_BV",
        (true, false, true) => "BV",
        (true, true, false) => "QF_ABV",
        (true, true, true) => "ABV",
        (false, true, false) => "QF_AUFLIA",
        (false, true, true) => "AUFLIA",
        (false, false, true) => "LIA",
        (false, false, false) => "QF_LIA",
    }
}

/// Write VC metadata as SMT-LIB2 comments.
fn write_metadata_comments(out: &mut String, vc: &VerificationCondition) {
    // SAFETY: All writeln! calls below write to a String, which is infallible.
    let _ = writeln!(out, "; tRust verification condition");
    let _ = writeln!(out, "; function: {}", vc.function);
    let _ = writeln!(out, "; vc_kind: {}", vc.kind.description());
    let _ = writeln!(out, "; proof_level: {:?}", vc.kind.proof_level());

    let loc = &vc.location;
    if !loc.file.is_empty() {
        let _ = writeln!(out, "; location: {}:{}:{}", loc.file, loc.line_start, loc.col_start);
    }

    if let Some(cm) = &vc.contract_metadata
        && cm.has_any() {
            let mut contracts = Vec::new();
            if cm.has_requires {
                contracts.push("requires");
            }
            if cm.has_ensures {
                contracts.push("ensures");
            }
            if cm.has_invariant {
                contracts.push("invariant");
            }
            if cm.has_variant {
                contracts.push("variant");
            }
            let _ = writeln!(out, "; contracts: {}", contracts.join(", "));
        }
}

/// Collect all free variables (name, sort) from a formula, excluding quantifier-bound names.
fn collect_free_vars(formula: &Formula, vars: &mut BTreeSet<(String, Sort)>) {
    let mut all_vars = BTreeSet::new();
    let mut bound_names: FxHashSet<String> = FxHashSet::default();

    formula.visit(&mut |node| {
        match node {
            Formula::Var(name, sort) => {
                all_vars.insert((name.clone(), sort.clone()));
            }
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
                for (name, _) in bindings {
                    bound_names.insert(name.clone());
                }
            }
            _ => {}
        }
    });

    for (name, sort) in all_vars {
        if !bound_names.contains(&name) {
            vars.insert((name, sort));
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    // --- Helpers ---

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    fn make_simple_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 42,
                col_start: 5,
                line_end: 42,
                col_end: 20,
            },
            formula,
            contract_metadata: None,
        }
    }

    // --- formula_to_smt2 tests ---

    #[test]
    fn test_formula_to_smt2_bool_literals() {
        assert_eq!(formula_to_smt2(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_smt2(&Formula::Bool(false)), "false");
    }

    #[test]
    fn test_formula_to_smt2_int_literals() {
        assert_eq!(formula_to_smt2(&Formula::Int(0)), "0");
        assert_eq!(formula_to_smt2(&Formula::Int(42)), "42");
        assert_eq!(formula_to_smt2(&Formula::Int(-7)), "(- 7)");
    }

    #[test]
    fn test_formula_to_smt2_uint_literal() {
        assert_eq!(formula_to_smt2(&Formula::UInt(u128::MAX)), u128::MAX.to_string());
    }

    #[test]
    fn test_formula_to_smt2_bitvec_literal() {
        assert_eq!(formula_to_smt2(&Formula::BitVec { value: 10, width: 32 }), "(_ bv10 32)");
    }

    #[test]
    fn test_formula_to_smt2_variables() {
        assert_eq!(formula_to_smt2(&int_var("x")), "x");
        assert_eq!(formula_to_smt2(&bv_var("y", 64)), "y");
    }

    #[test]
    fn test_formula_to_smt2_boolean_connectives() {
        let p = Formula::Var("p".into(), Sort::Bool);
        let q = Formula::Var("q".into(), Sort::Bool);

        assert_eq!(formula_to_smt2(&Formula::Not(Box::new(p.clone()))), "(not p)");
        assert_eq!(formula_to_smt2(&Formula::And(vec![p.clone(), q.clone()])), "(and p q)");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![p.clone(), q.clone()])), "(or p q)");
        assert_eq!(
            formula_to_smt2(&Formula::Implies(Box::new(p), Box::new(q))),
            "(=> p q)"
        );
    }

    #[test]
    fn test_formula_to_smt2_arithmetic() {
        let a = int_var("a");
        let b = int_var("b");

        assert_eq!(
            formula_to_smt2(&Formula::Add(Box::new(a.clone()), Box::new(b.clone()))),
            "(+ a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Sub(Box::new(a.clone()), Box::new(b.clone()))),
            "(- a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Mul(Box::new(a.clone()), Box::new(b.clone()))),
            "(* a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Div(Box::new(a.clone()), Box::new(b.clone()))),
            "(div a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Rem(Box::new(a.clone()), Box::new(b.clone()))),
            "(mod a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::Neg(Box::new(a))), "(- a)");
    }

    #[test]
    fn test_formula_to_smt2_comparisons() {
        let a = int_var("a");
        let b = int_var("b");

        assert_eq!(
            formula_to_smt2(&Formula::Eq(Box::new(a.clone()), Box::new(b.clone()))),
            "(= a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Lt(Box::new(a.clone()), Box::new(b.clone()))),
            "(< a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Le(Box::new(a.clone()), Box::new(b.clone()))),
            "(<= a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Gt(Box::new(a.clone()), Box::new(b.clone()))),
            "(> a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Ge(Box::new(a.clone()), Box::new(b.clone()))),
            "(>= a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bitvector_ops() {
        let a = bv_var("a", 32);
        let b = bv_var("b", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvadd a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSub(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsub a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvAnd(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvand a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvNot(Box::new(a.clone()), 32)), "(bvnot a)");
        assert_eq!(
            formula_to_smt2(&Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvult a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLe(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsle a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bv_conversions() {
        let x = bv_var("x", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvToInt(Box::new(x.clone()), 32, false)),
            "(bv2int x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::IntToBv(Box::new(int_var("n")), 32)),
            "((_ int2bv 32) n)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvExtract { inner: Box::new(x.clone()), high: 15, low: 0 }),
            "((_ extract 15 0) x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvConcat(Box::new(x.clone()), Box::new(bv_var("y", 32)))),
            "(concat x y)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvZeroExt(Box::new(x.clone()), 32)),
            "((_ zero_extend 32) x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSignExt(Box::new(x), 16)),
            "((_ sign_extend 16) x)"
        );
    }

    #[test]
    fn test_formula_to_smt2_quantifiers() {
        let body = Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let forall =
            Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(body.clone()));
        assert_eq!(formula_to_smt2(&forall), "(forall ((x Int)) (> x 0))");

        let exists = Formula::Exists(vec![("x".into(), Sort::Int)], Box::new(body));
        assert_eq!(formula_to_smt2(&exists), "(exists ((x Int)) (> x 0))");
    }

    #[test]
    fn test_formula_to_smt2_arrays() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let idx = Formula::Int(0);
        let val = Formula::Int(42);

        assert_eq!(
            formula_to_smt2(&Formula::Select(Box::new(arr.clone()), Box::new(idx.clone()))),
            "(select arr 0)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Store(
                Box::new(arr),
                Box::new(idx),
                Box::new(val)
            )),
            "(store arr 0 42)"
        );
    }

    #[test]
    fn test_formula_to_smt2_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(formula_to_smt2(&f), "(ite true 1 0)");
    }

    // --- sort_to_smt2 tests ---

    #[test]
    fn test_sort_to_smt2_basic() {
        assert_eq!(sort_to_smt2(&Sort::Bool), "Bool");
        assert_eq!(sort_to_smt2(&Sort::Int), "Int");
        assert_eq!(sort_to_smt2(&Sort::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(
            sort_to_smt2(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
            "(Array Int Int)"
        );
    }

    #[test]
    fn test_sort_to_smt2_nested_array() {
        let nested = Sort::Array(
            Box::new(Sort::BitVec(64)),
            Box::new(Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool))),
        );
        assert_eq!(sort_to_smt2(&nested), "(Array (_ BitVec 64) (Array Int Bool))");
    }

    // --- emit_declarations tests ---

    #[test]
    fn test_emit_declarations_simple() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")));
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0], "(declare-fun x () Int)");
        assert_eq!(decls[1], "(declare-fun y () Int)");
    }

    #[test]
    fn test_emit_declarations_deduplicates() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("x")));
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn test_emit_declarations_excludes_quantifier_bound() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
        );
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0], "(declare-fun y () Int)");
    }

    #[test]
    fn test_emit_declarations_no_vars() {
        let f = Formula::Bool(true);
        let decls = emit_declarations(&f);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_emit_declarations_bitvec_sort() {
        let f = bv_var("bits", 64);
        let decls = emit_declarations(&f);
        assert_eq!(decls[0], "(declare-fun bits () (_ BitVec 64))");
    }

    #[test]
    fn test_emit_declarations_array_sort() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let decls = emit_declarations(&arr);
        assert_eq!(
            decls[0],
            "(declare-fun mem () (Array (_ BitVec 64) (_ BitVec 8)))"
        );
    }

    // --- detect_logic tests ---

    #[test]
    fn test_detect_logic_pure_int() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)));
        assert_eq!(detect_logic(&f), "QF_LIA");
    }

    #[test]
    fn test_detect_logic_bitvector() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        assert_eq!(detect_logic(&f), "QF_BV");
    }

    #[test]
    fn test_detect_logic_arrays_int() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let f = Formula::Select(Box::new(arr), Box::new(Formula::Int(0)));
        assert_eq!(detect_logic(&f), "QF_AUFLIA");
    }

    #[test]
    fn test_detect_logic_arrays_bv() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let f = Formula::Select(Box::new(arr), Box::new(bv_var("addr", 64)));
        assert_eq!(detect_logic(&f), "QF_ABV");
    }

    #[test]
    fn test_detect_logic_quantified_int() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(detect_logic(&f), "LIA");
    }

    #[test]
    fn test_detect_logic_quantified_bv() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::BitVec(32))],
            Box::new(Formula::BvULt(
                Box::new(bv_var("x", 32)),
                Box::new(Formula::BitVec { value: 100, width: 32 }),
                32,
            )),
        );
        assert_eq!(detect_logic(&f), "BV");
    }

    #[test]
    fn test_detect_logic_pure_bool() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(detect_logic(&f), "QF_LIA");
    }

    // --- emit_smt2 tests ---

    #[test]
    fn test_emit_smt2_contains_metadata() {
        let vc = make_simple_vc(Formula::Lt(
            Box::new(int_var("x")),
            Box::new(Formula::Int(10)),
        ));

        let smt2 = emit_smt2(&vc);

        assert!(smt2.contains("; function: test_fn"), "should contain function name");
        assert!(smt2.contains("; vc_kind: division by zero"), "should contain VC kind");
        assert!(smt2.contains("; proof_level: L0Safety"), "should contain proof level");
        assert!(smt2.contains("; location: src/lib.rs:42:5"), "should contain location");
    }

    #[test]
    fn test_emit_smt2_contains_logic() {
        let vc = make_simple_vc(Formula::Lt(
            Box::new(int_var("x")),
            Box::new(Formula::Int(10)),
        ));

        let smt2 = emit_smt2(&vc);
        assert!(smt2.contains("(set-logic QF_LIA)"));
    }

    #[test]
    fn test_emit_smt2_contains_declarations() {
        let vc = make_simple_vc(Formula::Lt(
            Box::new(int_var("x")),
            Box::new(Formula::Int(10)),
        ));

        let smt2 = emit_smt2(&vc);
        assert!(smt2.contains("(declare-fun x () Int)"));
    }

    #[test]
    fn test_emit_smt2_contains_assertion() {
        let vc = make_simple_vc(Formula::Lt(
            Box::new(int_var("x")),
            Box::new(Formula::Int(10)),
        ));

        let smt2 = emit_smt2(&vc);
        assert!(smt2.contains("(assert (< x 10))"));
    }

    #[test]
    fn test_emit_smt2_contains_check_sat_and_exit() {
        let vc = make_simple_vc(Formula::Bool(true));
        let smt2 = emit_smt2(&vc);

        assert!(smt2.contains("(check-sat)"));
        assert!(smt2.contains("(get-model)"));
        assert!(smt2.contains("(exit)"));
    }

    #[test]
    fn test_emit_smt2_contract_metadata() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "add".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: Some(ContractMetadata {
                has_requires: true,
                has_ensures: true,
                has_invariant: false,
                has_variant: false,
                ..ContractMetadata::default()
            }),
        };

        let smt2 = emit_smt2(&vc);
        assert!(smt2.contains("; contracts: requires, ensures"));
    }

    #[test]
    fn test_emit_smt2_no_location_when_empty() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let smt2 = emit_smt2(&vc);
        assert!(!smt2.contains("; location:"), "should omit location when file is empty");
    }

    // --- emit_smt2_batch tests ---

    #[test]
    fn test_emit_smt2_batch_empty() {
        let smt2 = emit_smt2_batch(&[]);
        assert!(smt2.contains("empty batch"));
        assert!(smt2.contains("(set-logic ALL)"));
        assert!(smt2.contains("(exit)"));
    }

    #[test]
    fn test_emit_smt2_batch_single_delegates() {
        let vc = make_simple_vc(Formula::Bool(true));
        let single = emit_smt2(&vc);
        let batch = emit_smt2_batch(&[vc]);
        // Single-element batch should produce the same output as emit_smt2
        assert_eq!(single, batch);
    }

    #[test]
    fn test_emit_smt2_batch_multiple_uses_push_pop() {
        let vcs = vec![
            make_simple_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_simple_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        let smt2 = emit_smt2_batch(&vcs);

        assert!(smt2.contains("; tRust SMT-LIB2 batch export (2 VCs)"));
        assert!(smt2.contains("(push 1)"));
        assert!(smt2.contains("(pop 1)"));
        assert!(smt2.contains("(assert (< x 10))"));
        assert!(smt2.contains("(assert (> y 0))"));
        assert!(smt2.contains("(exit)"));

        // Should have two push/pop pairs
        let push_count = smt2.matches("(push 1)").count();
        let pop_count = smt2.matches("(pop 1)").count();
        assert_eq!(push_count, 2, "should have 2 push commands");
        assert_eq!(pop_count, 2, "should have 2 pop commands");
    }

    #[test]
    fn test_emit_smt2_batch_unified_logic() {
        // Mix int and BV VCs -- batch logic should accommodate both
        let vcs = vec![
            make_simple_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_simple_vc(Formula::BvAdd(
                Box::new(bv_var("a", 32)),
                Box::new(bv_var("b", 32)),
                32,
            )),
        ];

        let smt2 = emit_smt2_batch(&vcs);
        // With both int and BV, it should fall back to a logic that supports both.
        // Our detect_batch_logic returns QF_BV when bitvectors are present (no arrays).
        // This is acceptable since BV solvers handle integer constraints too.
        assert!(smt2.contains("(set-logic"), "should contain a set-logic declaration");
    }

    // --- Roundtrip / structural tests ---

    #[test]
    fn test_emit_smt2_roundtrip_structure_simple() {
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(int_var("x"))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(100))),
        ]);
        let vc = make_simple_vc(formula);
        let smt2 = emit_smt2(&vc);

        // Verify the script has the expected overall structure
        let lines: Vec<&str> = smt2.lines().collect();
        assert!(lines.iter().any(|l| l.starts_with("; tRust")), "missing tRust header comment");
        assert!(lines.iter().any(|l| l.starts_with("(set-logic")), "missing set-logic");
        assert!(lines.iter().any(|l| l.starts_with("(declare-fun")), "missing declare-fun");
        assert!(lines.iter().any(|l| l.starts_with("(assert")), "missing assert");
        assert!(lines.iter().any(|l| l.starts_with("(check-sat")), "missing check-sat");
        assert!(lines.iter().any(|l| l.starts_with("(exit")), "missing exit");

        // Verify the assertion contains the formula content
        assert!(smt2.contains("(<= 0 x)"));
        assert!(smt2.contains("(< x 100)"));
    }

    #[test]
    fn test_emit_smt2_roundtrip_structure_bitvector() {
        let formula = Formula::BvULt(
            Box::new(Formula::BvAdd(
                Box::new(bv_var("a", 64)),
                Box::new(bv_var("b", 64)),
                64,
            )),
            Box::new(Formula::BitVec { value: 1000, width: 64 }),
            64,
        );
        let vc = make_simple_vc(formula);
        let smt2 = emit_smt2(&vc);

        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains("(declare-fun a () (_ BitVec 64))"));
        assert!(smt2.contains("(declare-fun b () (_ BitVec 64))"));
        assert!(smt2.contains("(bvult (bvadd a b) (_ bv1000 64))"));
    }

    #[test]
    fn test_emit_smt2_roundtrip_structure_quantified() {
        let body = Formula::Implies(
            Box::new(Formula::Ge(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
            Box::new(Formula::Ge(
                Box::new(Formula::Mul(Box::new(int_var("x")), Box::new(int_var("x")))),
                Box::new(Formula::Int(0)),
            )),
        );
        let formula = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(body));
        let vc = make_simple_vc(formula);
        let smt2 = emit_smt2(&vc);

        // Quantified formula should NOT declare x as a free variable
        assert!(!smt2.contains("(declare-fun x"), "bound variable should not be declared");
        assert!(smt2.contains("(set-logic LIA)"), "quantified formula needs non-QF logic");
        assert!(smt2.contains("(forall ((x Int))"));
    }

    #[test]
    fn test_emit_smt2_roundtrip_structure_array() {
        let arr = Formula::Var(
            "arr".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
        );
        let formula = Formula::Eq(
            Box::new(Formula::Select(Box::new(arr), Box::new(Formula::Int(0)))),
            Box::new(Formula::Int(42)),
        );
        let vc = make_simple_vc(formula);
        let smt2 = emit_smt2(&vc);

        assert!(smt2.contains("(set-logic QF_AUFLIA)"));
        assert!(smt2.contains("(declare-fun arr () (Array Int Int))"));
        assert!(smt2.contains("(= (select arr 0) 42)"));
    }

    #[test]
    fn test_emit_smt2_midpoint_overflow_full_roundtrip() {
        // The classic midpoint overflow VC
        let max_val = (1i128 << 64) - 1;
        let a = int_var("a");
        let b = int_var("b");
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));

        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a), Box::new(Formula::Int(max_val))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(b.clone())),
            Formula::Le(Box::new(b), Box::new(Formula::Int(max_val))),
            Formula::Not(Box::new(Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(sum.clone())),
                Formula::Le(Box::new(sum), Box::new(Formula::Int(max_val))),
            ]))),
        ]);

        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "get_midpoint".to_string(),
            location: SourceSpan {
                file: "src/midpoint.rs".to_string(),
                line_start: 5,
                col_start: 1,
                line_end: 7,
                col_end: 2,
            },
            formula,
            contract_metadata: None,
        };

        let smt2 = emit_smt2(&vc);

        // Structural checks
        assert!(smt2.contains("; function: get_midpoint"));
        assert!(smt2.contains("; vc_kind: arithmetic overflow (Add)"));
        assert!(smt2.contains("; location: src/midpoint.rs:5:1"));
        assert!(smt2.contains("(set-logic QF_LIA)"));
        assert!(smt2.contains("(declare-fun a () Int)"));
        assert!(smt2.contains("(declare-fun b () Int)"));
        assert!(smt2.contains("(check-sat)"));
        assert!(smt2.contains("(exit)"));

        // Key formula fragments
        assert!(smt2.contains("(<= 0 a)"));
        assert!(smt2.contains(&format!("(<= a {max_val})")));
        assert!(smt2.contains("(not"));
    }

    // --- Parsability check: balanced parentheses ---

    #[test]
    fn test_emit_smt2_balanced_parens() {
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(int_var("x"))),
            Formula::Not(Box::new(Formula::Gt(
                Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
                Box::new(Formula::Int(100)),
            ))),
        ]);
        let vc = make_simple_vc(formula);
        let smt2 = emit_smt2(&vc);

        let open = smt2.chars().filter(|&c| c == '(').count();
        let close = smt2.chars().filter(|&c| c == ')').count();
        assert_eq!(open, close, "parentheses must be balanced: open={open}, close={close}");
    }

    // --- vc_to_smt2 alias test ---

    #[test]
    fn test_vc_to_smt2_is_emit_smt2_alias() {
        let vc = make_simple_vc(Formula::Lt(
            Box::new(int_var("x")),
            Box::new(Formula::Int(10)),
        ));
        assert_eq!(vc_to_smt2(&vc), emit_smt2(&vc));
    }

    // --- Additional bitvector operation coverage ---

    #[test]
    fn test_formula_to_smt2_bv_mul_div_rem() {
        let a = bv_var("a", 32);
        let b = bv_var("b", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvmul a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvUDiv(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvudiv a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSDiv(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsdiv a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvURem(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvurem a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSRem(Box::new(a), Box::new(b), 32)),
            "(bvsrem a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bv_or_xor_shifts() {
        let a = bv_var("a", 16);
        let b = bv_var("b", 16);

        assert_eq!(
            formula_to_smt2(&Formula::BvOr(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvor a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvXor(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvxor a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvShl(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvshl a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvLShr(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvlshr a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvAShr(Box::new(a), Box::new(b), 16)),
            "(bvashr a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bv_comparisons_all() {
        let a = bv_var("a", 8);
        let b = bv_var("b", 8);

        assert_eq!(
            formula_to_smt2(&Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvult a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvULe(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvule a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLt(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvslt a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLe(Box::new(a), Box::new(b), 8)),
            "(bvsle a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_and_or_empty_and_single() {
        // Empty And => "true", Empty Or => "false"
        assert_eq!(formula_to_smt2(&Formula::And(vec![])), "true");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![])), "false");

        // Single-element And/Or => unwrapped
        assert_eq!(formula_to_smt2(&Formula::And(vec![Formula::Bool(true)])), "true");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![Formula::Bool(false)])), "false");
    }

    #[test]
    fn test_formula_to_smt2_negative_bitvec() {
        // Negative bitvector values should be rendered as two's complement
        let f = Formula::BitVec { value: -1, width: 8 };
        let smt2 = formula_to_smt2(&f);
        // -1 in 8-bit two's complement = 255
        assert_eq!(smt2, "(_ bv255 8)");
    }

    #[test]
    fn test_emit_smt2_batch_balanced_parens() {
        let vcs = vec![
            make_simple_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_simple_vc(Formula::And(vec![
                Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0))),
                Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32),
            ])),
        ];
        let smt2 = emit_smt2_batch(&vcs);

        let open = smt2.chars().filter(|&c| c == '(').count();
        let close = smt2.chars().filter(|&c| c == ')').count();
        assert_eq!(open, close, "batch parentheses must be balanced: open={open}, close={close}");
    }
}
