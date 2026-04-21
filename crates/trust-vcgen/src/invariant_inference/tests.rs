// Tests for invariant inference module.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;
use crate::abstract_interp::AbstractDomain;
use crate::loop_analysis;

/// Build a counted loop: while i < n { sum += i; i += 1; }
fn sum_loop_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "sum_to_n".to_string(),
        def_path: "test::sum_to_n".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a search loop with array index access.
fn search_loop_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "linear_search".to_string(),
        def_path: "test::linear_search".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                    },
                    name: Some("arr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("target".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("len".into()) },
                LocalDecl { index: 4, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("elem".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Len(Place::local(1)),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(4)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Index(4)],
                            })),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a binary search loop.
fn binary_search_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "binary_search".to_string(),
        def_path: "test::binary_search".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                    },
                    name: Some("arr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("target".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("low".into()) },
                LocalDecl { index: 4, ty: Ty::usize(), name: Some("high".into()) },
                LocalDecl { index: 5, ty: Ty::usize(), name: Some("mid".into()) },
                LocalDecl { index: 6, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 7, ty: Ty::usize(), name: Some("len".into()) },
            ],
            blocks: vec![
                // bb0: len = arr.len(); low = 0; high = len; goto bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Len(Place::local(1)),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(7))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1 (header): cond = low < high; SwitchInt -> [1: bb2, else: bb3]
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(6)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb2 (body): mid = low / 2; low = mid + 1; goto bb1
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(5)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb3 (exit): return false
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn no_loop_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "identity".to_string(),
        def_path: "test::identity".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn annotated_loop_function() -> VerifiableFunction {
    let mut func = sum_loop_function();
    func.contracts.push(Contract {
        kind: ContractKind::Invariant,
        span: SourceSpan::default(),
        body: "i_le_n".to_string(),
    });
    func
}

// --- Tests ---

#[test]
fn test_no_loops_no_invariants() {
    let func = no_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    assert!(loops.is_empty());
}

#[test]
fn test_counter_loop_invariant_inferred() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    assert_eq!(loops.len(), 1);

    let candidates = infer_loop_invariants(&loops[0], &func);
    let counter = candidates
        .iter()
        .filter(|c| c.pattern == InvariantPattern::CounterLoop)
        .collect::<Vec<_>>();
    assert!(
        !counter.is_empty(),
        "should infer counter loop invariant for `i`"
    );
    assert!(counter[0].confidence >= 0.70);
    assert_eq!(counter[0].loop_header, BlockId(1));
}

#[test]
fn test_counter_loop_has_and_formula() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    // The counter for `i` should have init=0 and bound=n, so expression is And([0<=i, i<=n])
    let i_counter = candidates.iter().find(|c| {
        c.pattern == InvariantPattern::CounterLoop
            && matches!(&c.expression, Formula::And(_))
    });
    assert!(
        i_counter.is_some(),
        "should produce And(lower, upper) for counter with init and bound"
    );
}

#[test]
fn test_accumulator_invariant_inferred() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    let accum = candidates
        .iter()
        .filter(|c| c.pattern == InvariantPattern::Accumulator)
        .collect::<Vec<_>>();
    assert!(
        !accum.is_empty(),
        "should infer accumulator invariant for `sum`"
    );
    assert!(accum[0].confidence >= 0.70);
    // Expression should be sum >= 0
    assert!(matches!(
        &accum[0].expression,
        Formula::Ge(lhs, rhs)
            if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "sum")
            && matches!(rhs.as_ref(), Formula::Int(0))
    ));
}

#[test]
fn test_array_iteration_invariant_inferred() {
    let func = search_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    assert_eq!(loops.len(), 1);

    let candidates = infer_loop_invariants(&loops[0], &func);
    let arr_iter = candidates
        .iter()
        .filter(|c| c.pattern == InvariantPattern::ArrayIteration)
        .collect::<Vec<_>>();
    assert!(
        !arr_iter.is_empty(),
        "should infer array iteration invariant for `i < len`"
    );
    assert!(arr_iter[0].confidence >= 0.90);
}

#[test]
fn test_array_iteration_has_and_formula() {
    let func = search_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    let arr_iter = candidates
        .iter()
        .find(|c| c.pattern == InvariantPattern::ArrayIteration);
    assert!(arr_iter.is_some());
    // Should be And([0 <= i, i < len])
    assert!(matches!(&arr_iter.unwrap().expression, Formula::And(parts) if parts.len() == 2));
}

#[test]
fn test_binary_search_invariant_inferred() {
    let func = binary_search_function();
    let loops = loop_analysis::detect_loops(&func);
    assert_eq!(loops.len(), 1);

    let candidates = infer_loop_invariants(&loops[0], &func);
    let bsearch = candidates
        .iter()
        .filter(|c| c.pattern == InvariantPattern::BinarySearch)
        .collect::<Vec<_>>();
    assert!(
        !bsearch.is_empty(),
        "should infer binary search invariant `low <= high`"
    );
    assert!(bsearch[0].confidence >= 0.80);
}

#[test]
fn test_binary_search_formula_is_le() {
    let func = binary_search_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    let bsearch = candidates
        .iter()
        .find(|c| c.pattern == InvariantPattern::BinarySearch);
    assert!(bsearch.is_some());
    assert!(
        matches!(&bsearch.unwrap().expression, Formula::Le(_, _)),
        "binary search invariant should be Le(low, high)"
    );
}

#[test]
fn test_user_annotated_invariant() {
    let func = annotated_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    let user = candidates
        .iter()
        .filter(|c| c.pattern == InvariantPattern::UserAnnotated)
        .collect::<Vec<_>>();
    assert_eq!(user.len(), 1);
    assert_eq!(user[0].confidence, 1.0);
    assert!(matches!(
        &user[0].expression,
        Formula::Var(name, Sort::Bool) if name == "i_le_n"
    ));
}

#[test]
fn test_invariants_sorted_by_confidence() {
    let func = annotated_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    assert!(!candidates.is_empty());
    let confidences: Vec<f64> = candidates.iter().map(|c| c.confidence).collect();
    for window in confidences.windows(2) {
        assert!(
            window[0] >= window[1],
            "invariants should be sorted descending: {:?}",
            confidences
        );
    }
}

#[test]
fn test_inject_invariants_wraps_vcs() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    let mut vcs = crate::generate_vcs(&func);
    let original_count = vcs.len();
    crate::invariants::inject_invariants(&mut vcs, &convert_candidates(&candidates));

    assert_eq!(vcs.len(), original_count, "inject should not add VCs");
    if !vcs.is_empty() && !candidates.is_empty() {
        for vc in &vcs {
            assert!(
                matches!(&vc.formula, Formula::Implies(_, _)),
                "VCs should be wrapped with Implies after injection"
            );
        }
    }
}

#[test]
fn test_inject_empty_invariants_is_noop() {
    let mut vcs = vec![VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    }];
    crate::invariants::inject_invariants(&mut vcs, &[]);
    assert!(matches!(&vcs[0].formula, Formula::Bool(true)));
}

#[test]
fn test_multiple_patterns_combined() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let candidates = infer_loop_invariants(&loops[0], &func);

    let patterns: Vec<&InvariantPattern> = candidates.iter().map(|c| &c.pattern).collect();
    // Should have at least counter and accumulator
    assert!(
        patterns.contains(&&InvariantPattern::CounterLoop),
        "should have counter pattern"
    );
    assert!(
        patterns.contains(&&InvariantPattern::Accumulator),
        "should have accumulator pattern"
    );
}

#[test]
fn test_extract_index_accesses_with_index() {
    let rvalue = Rvalue::Use(Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Index(4)],
    }));
    let accesses = patterns::extract_index_accesses(&rvalue);
    assert_eq!(accesses.len(), 1);
    assert_eq!(accesses[0].0, 4);
    assert_eq!(accesses[0].1.local, 1);
}

#[test]
fn test_extract_index_accesses_no_index() {
    let rvalue = Rvalue::Use(Operand::Copy(Place::local(1)));
    let accesses = patterns::extract_index_accesses(&rvalue);
    assert!(accesses.is_empty());
}

#[test]
fn test_find_len_variable_found() {
    let func = search_loop_function();
    let result = patterns::find_len_variable(&func, &Place::local(1));
    assert_eq!(result.as_deref(), Some("len"));
}

#[test]
fn test_find_len_variable_not_found() {
    let func = sum_loop_function();
    let result = patterns::find_len_variable(&func, &Place::local(1));
    assert!(result.is_none());
}

/// Convert new-style InvariantCandidate to old-style for inject_invariants compatibility.
fn convert_candidates(
    candidates: &[InvariantCandidate],
) -> Vec<crate::invariants::InvariantCandidate> {
    candidates
        .iter()
        .map(|c| crate::invariants::InvariantCandidate {
            expression: c.expression.clone(),
            confidence: c.confidence,
            source: match &c.pattern {
                InvariantPattern::CounterLoop => crate::invariants::InvariantSource::CounterBounds,
                InvariantPattern::Accumulator => crate::invariants::InvariantSource::Monotonicity,
                InvariantPattern::ArrayIteration => {
                    crate::invariants::InvariantSource::InductionVariable
                }
                InvariantPattern::BinarySearch => {
                    crate::invariants::InvariantSource::CounterBounds
                }
                InvariantPattern::UserAnnotated => {
                    crate::invariants::InvariantSource::UserAnnotated
                }
            },
            loop_header: c.loop_header,
        })
        .collect()
}

// ── InvariantStatus & verify_invariant tests ───────────────────────────

#[test]
fn test_invariant_status_eq() {
    assert_eq!(InvariantStatus::Verified, InvariantStatus::Verified);
    assert_ne!(InvariantStatus::Verified, InvariantStatus::InitFailed);
    assert_ne!(InvariantStatus::ConsecutionFailed, InvariantStatus::Unknown);
}

#[test]
fn test_verify_invariant_counter_loop_verified() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    assert_eq!(loops.len(), 1);

    // i >= 0 should be verified: i starts at 0, incremented by 1.
    let candidate = InvariantCandidate {
        expression: Formula::Ge(
            Box::new(Formula::Var("i".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        confidence: 0.90,
        pattern: InvariantPattern::CounterLoop,
        loop_header: loops[0].header,
    };
    let status = verify_invariant(&candidate, &loops[0], &func);
    assert_eq!(status, InvariantStatus::Verified);
}

#[test]
fn test_verify_invariant_init_failed() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);

    // i >= 5 fails initiation since i starts at 0.
    let candidate = InvariantCandidate {
        expression: Formula::Ge(
            Box::new(Formula::Var("i".into(), Sort::Int)),
            Box::new(Formula::Int(5)),
        ),
        confidence: 0.50,
        pattern: InvariantPattern::CounterLoop,
        loop_header: loops[0].header,
    };
    let status = verify_invariant(&candidate, &loops[0], &func);
    assert_eq!(status, InvariantStatus::InitFailed);
}

#[test]
fn test_verify_invariant_sum_nonneg() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);

    // sum >= 0 should be verified: starts at 0, only added to.
    let candidate = InvariantCandidate {
        expression: Formula::Ge(
            Box::new(Formula::Var("sum".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        confidence: 0.80,
        pattern: InvariantPattern::Accumulator,
        loop_header: loops[0].header,
    };
    let status = verify_invariant(&candidate, &loops[0], &func);
    assert_eq!(status, InvariantStatus::Verified);
}

#[test]
fn test_verify_invariant_bool_true() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);

    let candidate = InvariantCandidate {
        expression: Formula::Bool(true),
        confidence: 1.0,
        pattern: InvariantPattern::UserAnnotated,
        loop_header: loops[0].header,
    };
    let status = verify_invariant(&candidate, &loops[0], &func);
    assert_eq!(status, InvariantStatus::Verified);
}

#[test]
fn test_verify_invariant_bool_false_init_fails() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);

    let candidate = InvariantCandidate {
        expression: Formula::Bool(false),
        confidence: 0.0,
        pattern: InvariantPattern::UserAnnotated,
        loop_header: loops[0].header,
    };
    let status = verify_invariant(&candidate, &loops[0], &func);
    assert_eq!(status, InvariantStatus::InitFailed);
}

// ── Counterexample-guided inference tests ──────────────────────────────

#[test]
fn test_infer_from_cex_nonneg() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let mut cex = Counterexample::new();
    cex.insert("i".into(), 3);
    cex.insert("sum".into(), 6);

    let candidates = infer_from_counterexample(&cex, &loops[0], &func);
    // Should find non-negativity for unsigned variables.
    let nonneg_i = candidates.iter().any(|c| {
        matches!(&c.expression,
            Formula::Ge(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i")
                && matches!(rhs.as_ref(), Formula::Int(0))
        )
    });
    assert!(nonneg_i, "should infer i >= 0 from CEX");
}

#[test]
fn test_infer_from_cex_ivar_bounds() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let mut cex = Counterexample::new();
    cex.insert("i".into(), 2);
    cex.insert("n".into(), 5);

    let candidates = infer_from_counterexample(&cex, &loops[0], &func);
    // Should find i <= n from induction var + CEX.
    let i_le_n = candidates.iter().any(|c| {
        matches!(&c.expression,
            Formula::Le(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i")
                && matches!(rhs.as_ref(), Formula::Var(name, _) if name == "n")
        )
    });
    assert!(i_le_n, "should infer i <= n from CEX and induction var bound");
}

#[test]
fn test_infer_from_cex_pairwise_ordering() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let mut cex = Counterexample::new();
    cex.insert("i".into(), 2);
    cex.insert("n".into(), 10);

    let candidates = infer_from_counterexample(&cex, &loops[0], &func);
    // Should find pairwise i <= n.
    let has_ordering = candidates.iter().any(|c| c.confidence <= 0.40);
    assert!(has_ordering, "should produce pairwise ordering candidates");
}

#[test]
fn test_infer_from_cex_empty_cex() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let cex = Counterexample::new();

    let candidates = infer_from_counterexample(&cex, &loops[0], &func);
    assert!(candidates.is_empty(), "empty CEX should produce no candidates");
}

#[test]
fn test_infer_from_cex_sorted_by_confidence() {
    let func = sum_loop_function();
    let loops = loop_analysis::detect_loops(&func);
    let mut cex = Counterexample::new();
    cex.insert("i".into(), 2);
    cex.insert("n".into(), 5);
    cex.insert("sum".into(), 3);

    let candidates = infer_from_counterexample(&cex, &loops[0], &func);
    let confidences: Vec<f64> = candidates.iter().map(|c| c.confidence).collect();
    for window in confidences.windows(2) {
        assert!(
            window[0] >= window[1],
            "CEX candidates should be sorted descending: {:?}",
            confidences
        );
    }
}

// ── Abstract interpretation bridge tests ───────────────────────────────

#[test]
fn test_infer_invariant_abstract_sum_loop() {
    let func = sum_loop_function();
    let candidates = infer_invariant_abstract(&func);
    // Sum loop has a loop header; should produce some abstract invariants.
    // At minimum, the fixpoint should discover that i starts at 0.
    let has_lower_bound = candidates.iter().any(|c| {
        matches!(&c.expression, Formula::Ge(_, rhs) if matches!(rhs.as_ref(), Formula::Int(0)))
    });
    assert!(
        has_lower_bound,
        "abstract interpretation should find lower bounds from fixpoint"
    );
}

#[test]
fn test_infer_invariant_abstract_no_loop() {
    let func = no_loop_function();
    let candidates = infer_invariant_abstract(&func);
    // No loops means no widen points, so no invariants.
    assert!(candidates.is_empty(), "no loops => no abstract invariants");
}

#[test]
fn test_infer_invariant_abstract_confidence() {
    let func = sum_loop_function();
    let candidates = infer_invariant_abstract(&func);
    for c in &candidates {
        assert!(
            (c.confidence - 0.70).abs() < 0.01,
            "abstract invariants should have 0.70 confidence, got {}",
            c.confidence
        );
    }
}

// ── DFS loop detection tests ───────────────────────────────────────────

#[test]
fn test_detect_loops_dfs_sum_loop() {
    let func = sum_loop_function();
    let loops = detect_loops_dfs(&func);
    assert_eq!(loops.len(), 1, "sum loop has exactly one loop via DFS");
    assert_eq!(loops[0].header, BlockId(1));
    assert_eq!(loops[0].latch, BlockId(2));
}

#[test]
fn test_detect_loops_dfs_no_loop() {
    let func = no_loop_function();
    let loops = detect_loops_dfs(&func);
    assert!(loops.is_empty(), "no loops in straight-line function via DFS");
}

#[test]
fn test_detect_loops_dfs_binary_search() {
    let func = binary_search_function();
    let loops = detect_loops_dfs(&func);
    assert_eq!(loops.len(), 1, "binary search has one loop via DFS");
    assert_eq!(loops[0].header, BlockId(1));
}

#[test]
fn test_detect_loops_dfs_exit_blocks() {
    let func = sum_loop_function();
    let loops = detect_loops_dfs(&func);
    assert!(
        loops[0].exit_blocks.contains(&BlockId(3)),
        "DFS loop detection should find bb3 as exit block"
    );
}

#[test]
fn test_detect_loops_dfs_body_contains_header_and_latch() {
    let func = sum_loop_function();
    let loops = detect_loops_dfs(&func);
    assert!(
        loops[0].body_blocks.contains(&BlockId(1)),
        "body should contain header"
    );
    assert!(
        loops[0].body_blocks.contains(&BlockId(2)),
        "body should contain latch"
    );
}

#[test]
fn test_detect_loops_dfs_finds_induction_vars() {
    let func = sum_loop_function();
    let loops = detect_loops_dfs(&func);
    let i_var = loops[0].induction_vars.iter().find(|v| v.name == "i");
    assert!(i_var.is_some(), "DFS loop detection should populate induction vars");
    assert_eq!(i_var.unwrap().step, 1);
}

// ── Octagon domain tests ───────────────────────────────────────────────

#[test]
fn test_octagon_top_has_no_constraints() {
    let oct = OctagonDomain::top();
    assert!(oct.constraints.is_empty());
    assert!(!oct.is_unreachable);
}

#[test]
fn test_octagon_bottom_is_unreachable() {
    let oct = OctagonDomain::bottom();
    assert!(oct.is_unreachable);
}

#[test]
fn test_octagon_add_constraint() {
    let mut oct = OctagonDomain::top();
    oct.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "y".into(),
        coeff_y: -1,
        constant: 5,
    });
    assert_eq!(oct.constraints.len(), 1);
    assert_eq!(oct.constraints[0].constant, 5);
}

#[test]
fn test_octagon_add_constraint_to_bottom_is_noop() {
    let mut oct = OctagonDomain::bottom();
    oct.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 10,
    });
    assert!(oct.constraints.is_empty());
    assert!(oct.is_unreachable);
}

#[test]
fn test_octagon_join_keeps_common_with_weaker_bound() {
    let mut a = OctagonDomain::top();
    a.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "y".into(),
        coeff_y: -1,
        constant: 3,
    });

    let mut b = OctagonDomain::top();
    b.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "y".into(),
        coeff_y: -1,
        constant: 7,
    });

    let joined = a.join(&b);
    assert_eq!(joined.constraints.len(), 1);
    assert_eq!(joined.constraints[0].constant, 7, "join should take max (weaker)");
}

#[test]
fn test_octagon_join_drops_non_common() {
    let mut a = OctagonDomain::top();
    a.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 10,
    });

    let b = OctagonDomain::top(); // No constraints.

    let joined = a.join(&b);
    assert!(joined.constraints.is_empty(), "constraint not in both should be dropped");
}

#[test]
fn test_octagon_join_bottom_identity() {
    let mut a = OctagonDomain::top();
    a.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 10,
    });
    let b = OctagonDomain::bottom();

    assert_eq!(a.join(&b), a);
    assert_eq!(b.join(&a), a);
}

#[test]
fn test_octagon_widen_drops_increasing() {
    let mut a = OctagonDomain::top();
    a.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 5,
    });

    let mut b = OctagonDomain::top();
    b.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 10, // Increased from 5.
    });

    let widened = a.widen(&b);
    // Bound increased: constraint should be dropped (widened to +inf).
    assert!(widened.constraints.is_empty(), "widening should drop increased bounds");
}

#[test]
fn test_octagon_widen_keeps_stable() {
    let mut a = OctagonDomain::top();
    a.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 10,
    });

    let mut b = OctagonDomain::top();
    b.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 5, // Decreased (stable).
    });

    let widened = a.widen(&b);
    assert_eq!(widened.constraints.len(), 1);
    assert_eq!(widened.constraints[0].constant, 10, "stable constraint should be kept");
}

#[test]
fn test_octagon_to_formulas_unary() {
    let mut oct = OctagonDomain::top();
    oct.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 42,
    });

    let formulas = oct.to_formulas();
    assert_eq!(formulas.len(), 1);
    // Should be: x <= 42
    assert!(matches!(&formulas[0], Formula::Le(lhs, rhs)
        if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "x")
        && matches!(rhs.as_ref(), Formula::Int(42))
    ));
}

#[test]
fn test_octagon_to_formulas_binary() {
    let mut oct = OctagonDomain::top();
    oct.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "y".into(),
        coeff_y: -1,
        constant: 5,
    });

    let formulas = oct.to_formulas();
    assert_eq!(formulas.len(), 1);
    // Should be: x + (-y) <= 5
    assert!(matches!(&formulas[0], Formula::Le(_, rhs) if matches!(rhs.as_ref(), Formula::Int(5))));
}

#[test]
fn test_octagon_to_formulas_bottom() {
    let oct = OctagonDomain::bottom();
    let formulas = oct.to_formulas();
    assert_eq!(formulas.len(), 1);
    assert!(matches!(&formulas[0], Formula::Bool(false)));
}

#[test]
fn test_octagon_satisfies() {
    let mut oct = OctagonDomain::top();
    oct.add_constraint(OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 5,
    });

    // x <= 10 is satisfied by having x <= 5 (tighter).
    assert!(oct.satisfies(&OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 10,
    }));

    // x <= 3 is NOT satisfied (we only know x <= 5).
    assert!(!oct.satisfies(&OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 3,
    }));
}

#[test]
fn test_octagon_satisfies_bottom_satisfies_everything() {
    let oct = OctagonDomain::bottom();
    assert!(oct.satisfies(&OctagonConstraint {
        var_x: "x".into(),
        coeff_x: 1,
        var_y: "".into(),
        coeff_y: 0,
        constant: 0,
    }));
}

// ── eval_formula_in_state tests ────────────────────────────────────────

#[test]
fn test_eval_formula_ge_true() {
    let mut state = crate::abstract_interp::IntervalDomain::top();
    state.set("x".into(), crate::abstract_interp::Interval::new(5, 10));
    let formula = Formula::Ge(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(3)),
    );
    assert!(verification::eval_formula_in_state(&formula, &state));
}

#[test]
fn test_eval_formula_ge_false() {
    let mut state = crate::abstract_interp::IntervalDomain::top();
    state.set("x".into(), crate::abstract_interp::Interval::new(0, 2));
    // x >= 5 but x is in [0, 2] — hi < 5, so false.
    let formula = Formula::Ge(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(5)),
    );
    assert!(!verification::eval_formula_in_state(&formula, &state));
}

#[test]
fn test_eval_formula_and() {
    let mut state = crate::abstract_interp::IntervalDomain::top();
    state.set("x".into(), crate::abstract_interp::Interval::new(0, 10));
    let formula = Formula::And(vec![
        Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(20)),
        ),
    ]);
    assert!(verification::eval_formula_in_state(&formula, &state));
}

#[test]
fn test_eval_formula_or() {
    let mut state = crate::abstract_interp::IntervalDomain::top();
    state.set("x".into(), crate::abstract_interp::Interval::new(0, 2));
    let formula = Formula::Or(vec![
        Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(100)),
        ),
        Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(5)),
        ),
    ]);
    assert!(verification::eval_formula_in_state(&formula, &state));
}
