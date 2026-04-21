// trust-vcgen/termination.rs: Termination checking via decreases clauses (#66)
//
// Extracts loop variants and recursive function decreases measures from MIR,
// then generates VcKind::NonTermination verification conditions. Termination
// is proved by showing the measure:
//   1. Is bounded below (non-negative).
//   2. Strictly decreases on each loop iteration or recursive call.
//
// Loop variant extraction:
//   - Detect back-edges in the CFG (target block ID <= source block ID).
//   - For each back-edge, find integer variables modified in the loop body
//     that could serve as the decreasing measure.
//   - If a #[trust_decreases] annotation exists, use its measure expression.
//
// Recursive decreases detection:
//   - Detect self-calls (Call terminator where func matches the function name).
//   - Generate VC that the decreases measure at the call site is strictly less
//     than the measure at function entry.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_types::fx::FxHashSet;

/// A detected loop in the MIR control flow graph.
#[derive(Debug, Clone)]
pub(crate) struct LoopInfo {
    /// Block ID of the loop header (target of the back-edge).
    pub(crate) header: BlockId,
    /// Block ID of the latch (source of the back-edge).
    pub(crate) latch: BlockId,
    /// Block IDs of all blocks in the loop body (between header and latch).
    pub(crate) body_blocks: Vec<BlockId>,
}

/// A detected recursive call site.
#[derive(Debug, Clone)]
pub(crate) struct RecursiveCallSite {
    /// Block containing the recursive call.
    pub(crate) block: BlockId,
    /// Arguments passed to the recursive call.
    pub(crate) args: Vec<Operand>,
    /// Source span of the call.
    pub(crate) span: SourceSpan,
}

/// Detect loops by finding back-edges in the CFG.
///
/// A back-edge is a CFG edge where the target block ID is less than or equal
/// to the source block ID. This is a simplified heuristic that works for MIR's
/// structured control flow where loop headers have lower block IDs than latches.
pub(crate) fn detect_loops(body: &VerifiableBody) -> Vec<LoopInfo> {
    let mut loops = Vec::new();

    for block in &body.blocks {
        let successors = block_successors(&block.terminator);
        for succ in successors {
            // Back-edge: successor has a lower or equal block ID
            if succ.0 <= block.id.0 {
                let header = succ;
                let latch = block.id;
                // Collect body blocks: all blocks between header and latch (inclusive)
                let body_blocks: Vec<BlockId> = body
                    .blocks
                    .iter()
                    .filter(|bb| bb.id.0 >= header.0 && bb.id.0 <= latch.0)
                    .map(|bb| bb.id)
                    .collect();

                loops.push(LoopInfo { header, latch, body_blocks });
            }
        }
    }

    loops
}

/// Detect recursive call sites (calls to the same function).
pub(crate) fn detect_recursive_calls(func: &VerifiableFunction) -> Vec<RecursiveCallSite> {
    let mut sites = Vec::new();

    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, span, .. } = &block.terminator {
            // Match self-calls by function name or def_path
            if callee == &func.name || callee == &func.def_path {
                sites.push(RecursiveCallSite {
                    block: block.id,
                    args: args.clone(),
                    span: span.clone(),
                });
            }
        }
    }

    sites
}

/// Find integer variables modified in a set of blocks.
///
/// Returns (local_index, variable_name) pairs for locals that are assigned
/// in the given blocks and have integer types.
pub(crate) fn modified_int_locals(
    func: &VerifiableFunction,
    blocks: &[BlockId],
) -> Vec<(usize, String)> {
    let mut modified = Vec::new();
    let block_set: FxHashSet<usize> = blocks.iter().map(|b| b.0).collect();

    for block in &func.body.blocks {
        if !block_set.contains(&block.id.0) {
            continue;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && let Some(decl) = func.body.locals.get(place.local)
                    && decl.ty.is_integer() && place.projections.is_empty() {
                        let name = decl
                            .name
                            .clone()
                            .unwrap_or_else(|| format!("_{}", place.local));
                        if !modified.iter().any(|(idx, _)| *idx == place.local) {
                            modified.push((place.local, name));
                        }
                    }
        }
    }

    modified
}

/// Extract decreases clauses from contract annotations.
pub(crate) fn extract_decreases_contracts(func: &VerifiableFunction) -> Vec<DecreasesClause> {
    func.contracts
        .iter()
        .filter(|c| matches!(c.kind, ContractKind::Decreases))
        .map(|c| DecreasesClause {
            measure: c.body.clone(),
            span: c.span.clone(),
            kind: DecreasesKind::Recursion,
        })
        .collect()
}

/// Generate termination verification conditions for a function.
///
/// Produces VcKind::NonTermination VCs for:
/// 1. Each detected loop without a provably decreasing variant.
/// 2. Each recursive call without a decreases clause.
pub(crate) fn check_termination(
    func: &VerifiableFunction,
    vcs: &mut Vec<VerificationCondition>,
) {
    let loops = detect_loops(&func.body);
    let recursive_calls = detect_recursive_calls(func);

    // Skip if no loops and no recursion — function trivially terminates
    if loops.is_empty() && recursive_calls.is_empty() {
        return;
    }

    let decreases_clauses = extract_decreases_contracts(func);

    // Generate VCs for loops
    for loop_info in &loops {
        let modified = modified_int_locals(func, &loop_info.body_blocks);

        // If there's an explicit decreases clause for this loop, use it
        let explicit_clause = decreases_clauses.iter().find(|dc| {
            matches!(dc.kind, DecreasesKind::LoopVariant { header_block }
                if header_block == loop_info.header.0)
        });

        let measure = if let Some(clause) = explicit_clause {
            clause.measure.clone()
        } else if let Some((_, name)) = modified.first() {
            // Heuristic: use the first modified integer variable as the candidate measure
            name.clone()
        } else {
            // No integer variable modified in the loop — likely non-terminating or
            // the measure is non-obvious
            "unknown".to_string()
        };

        // Locate the span from the loop header block
        let span = func
            .body
            .blocks
            .get(loop_info.header.0)
            .map(|bb| terminator_span(&bb.terminator))
            .unwrap_or_default();

        // VC: the measure must be >= 0 AND must decrease on each iteration.
        // We encode: exists state where measure_before <= measure_after OR measure < 0
        // i.e., the negation of the termination argument.
        let measure_var =
            Formula::Var(format!("{measure}_before"), Sort::Int);
        let measure_var_after =
            Formula::Var(format!("{measure}_after"), Sort::Int);

        // Non-termination formula: measure doesn't decrease OR goes negative
        let not_decreasing = Formula::Or(vec![
            // measure_after >= measure_before (didn't decrease)
            Formula::Ge(
                Box::new(measure_var_after),
                Box::new(measure_var.clone()),
            ),
            // measure_before < 0 (not bounded below)
            Formula::Lt(Box::new(measure_var), Box::new(Formula::Int(0))),
        ]);

        vcs.push(VerificationCondition {
            kind: VcKind::NonTermination {
                context: "loop".to_string(),
                measure: measure.clone(),
            },
            function: func.name.clone(),
            location: span,
            formula: not_decreasing,
            contract_metadata: None,
        });
    }

    // Generate VCs for recursive calls
    for call_site in &recursive_calls {
        let explicit_clause =
            decreases_clauses.iter().find(|dc| matches!(dc.kind, DecreasesKind::Recursion));

        let measure = if let Some(clause) = explicit_clause {
            clause.measure.clone()
        } else if func.body.arg_count > 0 {
            // Heuristic: use the first integer argument as the candidate measure
            let first_int_arg = func.body.locals[1..=func.body.arg_count]
                .iter()
                .find(|l| l.ty.is_integer());
            match first_int_arg {
                Some(decl) => decl
                    .name
                    .clone()
                    .unwrap_or_else(|| format!("_{}", decl.index)),
                None => "unknown".to_string(),
            }
        } else {
            "unknown".to_string()
        };

        // VC for recursion: the measure at call site must be strictly less than
        // the measure at function entry.
        let measure_entry = Formula::Var(format!("{measure}_entry"), Sort::Int);
        let measure_call = Formula::Var(format!("{measure}_call"), Sort::Int);

        // Non-termination formula: measure at call >= measure at entry OR entry < 0
        let not_decreasing = Formula::Or(vec![
            Formula::Ge(Box::new(measure_call), Box::new(measure_entry.clone())),
            Formula::Lt(Box::new(measure_entry), Box::new(Formula::Int(0))),
        ]);

        vcs.push(VerificationCondition {
            kind: VcKind::NonTermination {
                context: "recursion".to_string(),
                measure: measure.clone(),
            },
            function: func.name.clone(),
            location: call_site.span.clone(),
            formula: not_decreasing,
            contract_metadata: None,
        });
    }
}

/// Get all successor block IDs from a terminator.
fn block_successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<BlockId> = targets.iter().map(|(_, t)| *t).collect();
            succs.push(*otherwise);
            succs
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        _ => vec![],
    }
}

/// Extract a source span from a terminator, falling back to default.
fn terminator_span(term: &Terminator) -> SourceSpan {
    match term {
        Terminator::SwitchInt { span, .. }
        | Terminator::Call { span, .. }
        | Terminator::Assert { span, .. }
        | Terminator::Drop { span, .. } => span.clone(),
        _ => SourceSpan::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a function with a simple counted loop:
    /// ```
    /// fn countdown(mut n: u32) {
    ///     while n > 0 { n -= 1; }
    /// }
    /// ```
    /// MIR:
    ///   bb0: SwitchInt(n > 0) -> [1: bb1, otherwise: bb2]
    ///   bb1: n = n - 1; goto bb0   (back-edge to bb0)
    ///   bb2: return
    fn countdown_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "countdown".to_string(),
            def_path: "test::countdown".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            // cond = n > 0
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Gt,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(0, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan { file: "test.rs".into(), line_start: 2, col_start: 5, line_end: 2, col_end: 30 },
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            // n = n - 1
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Sub,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(1, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(0)), // back-edge
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with an infinite loop (no decreasing variable):
    /// ```
    /// fn spin() { loop {} }
    /// ```
    /// MIR:
    ///   bb0: goto bb0  (self-loop)
    fn infinite_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "spin".to_string(),
            def_path: "test::spin".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(0)), // self-loop
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a recursive function:
    /// ```
    /// fn factorial(n: u32) -> u32 {
    ///     if n == 0 { 1 } else { n * factorial(n - 1) }
    /// }
    /// ```
    fn recursive_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "factorial".to_string(),
            def_path: "test::factorial".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },      // return
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None },       // n == 0
                    LocalDecl { index: 3, ty: Ty::u32(), name: None },      // n - 1
                    LocalDecl { index: 4, ty: Ty::u32(), name: None },      // factorial(n-1)
                    LocalDecl { index: 5, ty: Ty::u32(), name: None },      // n * factorial(n-1)
                ],
                blocks: vec![
                    // bb0: check n == 0
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1: base case, return 1
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                    // bb2: recursive case
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            func: "factorial".to_string(),
                            args: vec![Operand::Copy(Place::local(3))],
                            dest: Place::local(4),
                            target: Some(BlockId(3)),
                            span: SourceSpan { file: "test.rs".into(), line_start: 3, col_start: 20, line_end: 3, col_end: 40 },
                            atomic: None,
                        },
                    },
                    // bb3: multiply and return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Mul,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Copy(Place::local(4)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                                span: SourceSpan::default(),
                            },
                        ],
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

    /// Build a function with an explicit decreases clause on recursion.
    fn recursive_with_decreases() -> VerifiableFunction {
        let mut func = recursive_function();
        func.contracts.push(Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "n".to_string(),
        });
        func
    }

    // --- Tests ---

    #[test]
    fn test_detect_loops_countdown() {
        let func = countdown_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1, "countdown has exactly one loop");
        assert_eq!(loops[0].header, BlockId(0));
        assert_eq!(loops[0].latch, BlockId(1));
        assert!(loops[0].body_blocks.contains(&BlockId(0)));
        assert!(loops[0].body_blocks.contains(&BlockId(1)));
    }

    #[test]
    fn test_detect_loops_infinite() {
        let func = infinite_loop_function();
        let loops = detect_loops(&func.body);
        assert_eq!(loops.len(), 1, "infinite loop has one back-edge");
        assert_eq!(loops[0].header, BlockId(0));
        assert_eq!(loops[0].latch, BlockId(0));
    }

    #[test]
    fn test_detect_loops_no_loops() {
        let func = recursive_function();
        let loops = detect_loops(&func.body);
        assert!(loops.is_empty(), "factorial has no loops");
    }

    #[test]
    fn test_detect_recursive_calls_factorial() {
        let func = recursive_function();
        let calls = detect_recursive_calls(&func);
        assert_eq!(calls.len(), 1, "factorial has one recursive call");
        assert_eq!(calls[0].block, BlockId(2));
    }

    #[test]
    fn test_detect_recursive_calls_non_recursive() {
        let func = countdown_function();
        let calls = detect_recursive_calls(&func);
        assert!(calls.is_empty(), "countdown is not recursive");
    }

    #[test]
    fn test_modified_int_locals_in_loop() {
        let func = countdown_function();
        let loops = detect_loops(&func.body);
        let modified = modified_int_locals(&func, &loops[0].body_blocks);
        assert!(modified.iter().any(|(_, name)| name == "n"), "n is modified in the loop");
    }

    #[test]
    fn test_check_termination_countdown_produces_vc() {
        let func = countdown_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "countdown loop produces 1 termination VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "loop" && measure == "n"
        ));
        assert_eq!(vcs[0].kind.proof_level(), ProofLevel::L1Functional);
    }

    #[test]
    fn test_check_termination_infinite_loop_produces_vc() {
        let func = infinite_loop_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "infinite loop produces 1 termination VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "loop" && measure == "unknown"
        ));
    }

    #[test]
    fn test_check_termination_recursive_produces_vc() {
        let func = recursive_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1, "factorial produces 1 recursion termination VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
    }

    #[test]
    fn test_check_termination_with_decreases_clause() {
        let func = recursive_with_decreases();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::NonTermination { context, measure }
                if context == "recursion" && measure == "n"
        ));
    }

    #[test]
    fn test_check_termination_no_loops_no_recursion() {
        // A simple function with no loops and no recursion should produce no VCs
        let func = VerifiableFunction {
            name: "simple".to_string(),
            def_path: "test::simple".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
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
        };
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert!(vcs.is_empty(), "simple function should produce no termination VCs");
    }

    #[test]
    fn test_non_termination_vc_has_no_runtime_fallback() {
        let kind = VcKind::NonTermination {
            context: "loop".to_string(),
            measure: "n".to_string(),
        };
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
    }

    #[test]
    fn test_non_termination_vc_description() {
        let kind = VcKind::NonTermination {
            context: "loop".to_string(),
            measure: "n".to_string(),
        };
        assert_eq!(
            kind.description(),
            "non-termination: loop measure `n` may not decrease"
        );
    }

    #[test]
    fn test_non_termination_formula_structure() {
        let func = countdown_function();
        let mut vcs = Vec::new();
        check_termination(&func, &mut vcs);
        assert_eq!(vcs.len(), 1);

        // The formula should be Or([Ge(after, before), Lt(before, 0)])
        match &vcs[0].formula {
            Formula::Or(clauses) => {
                assert_eq!(clauses.len(), 2, "non-termination formula is Or of 2 clauses");
                assert!(
                    matches!(&clauses[0], Formula::Ge(_, _)),
                    "first clause: measure_after >= measure_before"
                );
                assert!(
                    matches!(&clauses[1], Formula::Lt(_, _)),
                    "second clause: measure_before < 0"
                );
            }
            other => panic!("expected Or formula, got: {other:?}"),
        }
    }

    #[test]
    fn test_extract_decreases_contracts() {
        let func = recursive_with_decreases();
        let clauses = extract_decreases_contracts(&func);
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].measure, "n");
        assert!(matches!(clauses[0].kind, DecreasesKind::Recursion));
    }

    #[test]
    fn test_decreases_clause_serialization_roundtrip() {
        let clause = DecreasesClause {
            measure: "len - i".to_string(),
            span: SourceSpan::default(),
            kind: DecreasesKind::LoopVariant { header_block: 3 },
        };
        let json = serde_json::to_string(&clause).expect("serialize");
        let round: DecreasesClause = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.measure, "len - i");
        assert!(matches!(round.kind, DecreasesKind::LoopVariant { header_block: 3 }));
    }

    #[test]
    fn test_decreases_kind_equality() {
        assert_eq!(DecreasesKind::Recursion, DecreasesKind::Recursion);
        assert_eq!(
            DecreasesKind::LoopVariant { header_block: 0 },
            DecreasesKind::LoopVariant { header_block: 0 }
        );
        assert_ne!(
            DecreasesKind::LoopVariant { header_block: 0 },
            DecreasesKind::Recursion
        );
    }
}
