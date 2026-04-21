// trust-vcgen/invariants.rs: Automatic loop invariant inference (#70)

//
// Discovers candidate loop invariants from MIR patterns and injects them
// as assumptions into verification conditions. This strengthens the
// solver's ability to prove loop-containing functions without manual
// annotations.
//
// Techniques:
//   - Pattern-based: detect common loop idioms (counter bounds, monotonic
//     accumulators, index bounds) and generate candidate invariants.
//   - User-annotated: extract ContractKind::Invariant from function contracts.
//
// Each candidate has a confidence score [0.0, 1.0] indicating how likely
// the invariant is to be inductive.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::termination::{detect_loops, modified_int_locals, LoopInfo};
use trust_types::fx::FxHashMap;

/// How the invariant was discovered.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum InvariantSource {
    /// Loop counter bounded: `0 <= i && i <= len`
    CounterBounds,
    /// Monotonic accumulator: `acc >= 0` (or `acc >= initial`)
    Monotonicity,
    /// Induction variable tracks iteration count
    InductionVariable,
    /// User-provided `#[invariant(...)]` annotation
    UserAnnotated,
}

/// A candidate loop invariant with confidence score.
#[derive(Debug, Clone)]
pub(crate) struct InvariantCandidate {
    /// The invariant formula (holds at loop header on every iteration).
    pub(crate) expression: Formula,
    /// Confidence that this invariant is inductive [0.0, 1.0].
    pub(crate) confidence: f64,
    /// How the invariant was discovered.
    pub(crate) source: InvariantSource,
    /// Which loop header this invariant applies to.
    pub(crate) loop_header: BlockId,
}

/// Infer loop invariants for all loops in a function.
///
/// Applies pattern-based heuristics and extracts user annotations.
/// Returns candidates sorted by confidence (highest first).
#[must_use]
pub(crate) fn infer_loop_invariants(func: &VerifiableFunction) -> Vec<InvariantCandidate> {
    let loops = detect_loops(&func.body);
    if loops.is_empty() {
        return vec![];
    }

    let mut candidates = Vec::new();

    for loop_info in &loops {
        // User-annotated invariants (highest confidence)
        candidates.extend(extract_user_invariants(func, loop_info));

        // Pattern-based inference
        candidates.extend(infer_counter_bounds(func, loop_info));
        candidates.extend(infer_monotonic_accumulators(func, loop_info));
        candidates.extend(infer_index_bounds(func, loop_info));
    }

    // Sort by confidence descending
    candidates.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal));
    candidates
}

/// Inject discovered invariants into verification conditions as assumptions.
///
/// For each VC in a loop, wraps its formula with invariant implications:
///   `invariant_conjunction => original_formula`
///
/// This tells the solver: assuming the invariants hold, does the property hold?
pub(crate) fn inject_invariants(
    vcs: &mut [VerificationCondition],
    invariants: &[InvariantCandidate],
) {
    if invariants.is_empty() {
        return;
    }

    // Group invariants by loop header for efficient lookup
    let mut inv_by_header: FxHashMap<BlockId, Vec<&InvariantCandidate>> =
        FxHashMap::default();
    for inv in invariants {
        inv_by_header.entry(inv.loop_header).or_default().push(inv);
    }

    // For each VC, if it has any applicable invariants, strengthen with assumptions.
    // We apply all invariants as a conjunction of assumptions.
    if inv_by_header.is_empty() {
        return;
    }

    // Build a single conjunction of all invariants (they apply globally to the function)
    let all_invariant_formulas: Vec<Formula> = invariants
        .iter()
        .map(|inv| inv.expression.clone())
        .collect();

    if all_invariant_formulas.is_empty() {
        return;
    }

    let assumption = if all_invariant_formulas.len() == 1 {
        // SAFETY: len == 1 guarantees .next() returns Some.
        all_invariant_formulas.into_iter().next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
    } else {
        Formula::And(all_invariant_formulas)
    };

    for vc in vcs.iter_mut() {
        // Wrap: assumption => original_formula
        // If UNSAT under the assumption, the property holds given invariants
        vc.formula = Formula::Implies(
            Box::new(assumption.clone()),
            Box::new(vc.formula.clone()),
        );
    }
}

// --- Pattern matchers ---

/// Extract user-annotated invariants from `ContractKind::Invariant` contracts.
fn extract_user_invariants(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    func.contracts
        .iter()
        .filter(|c| matches!(c.kind, ContractKind::Invariant))
        .map(|c| InvariantCandidate {
            // Parse the invariant body as a variable reference.
            // For now, treat the body as a boolean variable that must hold.
            expression: Formula::Var(c.body.clone(), Sort::Bool),
            confidence: 1.0,
            source: InvariantSource::UserAnnotated,
            loop_header: loop_info.header,
        })
        .collect()
}

/// Detect loop counter bounds: `0 <= var && var <= upper_bound`.
///
/// Pattern: a loop modifies an integer variable `i` via Add or Sub with
/// constant 1, and the loop condition compares `i` against a bound.
/// Generates: `0 <= i && i <= bound` for unsigned counters.
fn infer_counter_bounds(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    let modified = modified_int_locals(func, &loop_info.body_blocks);
    let mut candidates = Vec::new();

    for (local_idx, var_name) in &modified {
        // Check if this variable is incremented or decremented by a constant
        let step_info = find_step_pattern(func, loop_info, *local_idx);
        if step_info.is_none() {
            continue;
        }

        let var = Formula::Var(var_name.clone(), Sort::Int);

        // Look for a comparison bound in the loop header's terminator
        if let Some(bound) = find_loop_bound(func, loop_info, *local_idx) {
            // Counter bounds: 0 <= var && var <= bound
            let lower = Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(var.clone()),
            );
            let upper = Formula::Le(
                Box::new(var),
                Box::new(bound),
            );
            let invariant = Formula::And(vec![lower, upper]);

            candidates.push(InvariantCandidate {
                expression: invariant,
                confidence: 0.85,
                source: InvariantSource::CounterBounds,
                loop_header: loop_info.header,
            });
        } else {
            // No explicit bound found, but we know the variable changes.
            // For unsigned types, at least `var >= 0` holds.
            if let Some(decl) = func.body.locals.get(*local_idx)
                && !decl.ty.is_signed() && decl.ty.is_integer() {
                    let lower = Formula::Ge(
                        Box::new(Formula::Var(var_name.clone(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    );
                    candidates.push(InvariantCandidate {
                        expression: lower,
                        confidence: 0.95,
                        source: InvariantSource::CounterBounds,
                        loop_header: loop_info.header,
                    });
                }
        }
    }

    candidates
}

/// Detect monotonic accumulators: variables that only increase (or only decrease).
///
/// Pattern: variable assigned as `acc = acc + positive_value` inside loop.
/// Generates: `acc >= 0` for unsigned accumulators.
fn infer_monotonic_accumulators(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();

    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if !place.projections.is_empty() {
                    continue;
                }
                let local_idx = place.local;
                let Some(decl) = func.body.locals.get(local_idx) else {
                    continue;
                };
                if !decl.ty.is_integer() {
                    continue;
                }

                // Check for accumulation pattern: x = x + expr or x = x - expr
                let is_monotonic_add = matches!(
                    rvalue,
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(src), _)
                    | Rvalue::BinaryOp(BinOp::Add, _, Operand::Copy(src))
                        if src.local == local_idx && src.projections.is_empty()
                );

                if is_monotonic_add && !decl.ty.is_signed() {
                    let var_name = decl.name.clone().unwrap_or_else(|| format!("_{local_idx}"));
                    // Unsigned accumulator: acc >= 0
                    let invariant = Formula::Ge(
                        Box::new(Formula::Var(var_name, Sort::Int)),
                        Box::new(Formula::Int(0)),
                    );
                    candidates.push(InvariantCandidate {
                        expression: invariant,
                        confidence: 0.80,
                        source: InvariantSource::Monotonicity,
                        loop_header: loop_info.header,
                    });
                }
            }
        }
    }

    candidates
}

/// Detect index bounds: variables used as array/slice indices.
///
/// Pattern: `Rvalue::Use(Operand::Copy(Place { projections: [Index(i)], .. }))`
/// or a Len-comparison guard in the loop condition.
/// Generates: `idx < array_len`
fn infer_index_bounds(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();

    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                // Look for Index projections in the rvalue operands
                for (idx_local, array_place) in extract_index_accesses(rvalue) {
                    let Some(idx_decl) = func.body.locals.get(idx_local) else {
                        continue;
                    };
                    if !idx_decl.ty.is_integer() {
                        continue;
                    }

                    let idx_name = idx_decl
                        .name
                        .clone()
                        .unwrap_or_else(|| format!("_{idx_local}"));

                    // Look for a Len rvalue of the same array in the function
                    if let Some(len_var) = find_len_variable(func, &array_place) {
                        // idx < len
                        let invariant = Formula::Lt(
                            Box::new(Formula::Var(idx_name, Sort::Int)),
                            Box::new(Formula::Var(len_var, Sort::Int)),
                        );
                        candidates.push(InvariantCandidate {
                            expression: invariant,
                            confidence: 0.90,
                            source: InvariantSource::InductionVariable,
                            loop_header: loop_info.header,
                        });
                    }
                }
            }
        }
    }

    candidates
}

// --- Helpers ---

/// Check if a variable is incremented/decremented by a constant step.
/// Returns `Some(step)` if detected, `None` otherwise.
fn find_step_pattern(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    local_idx: usize,
) -> Option<i128> {
    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if place.local != local_idx || !place.projections.is_empty() {
                    continue;
                }
                match rvalue {
                    // x = x + const or x = x - const
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(src), Operand::Constant(cv))
                    | Rvalue::BinaryOp(BinOp::Add, Operand::Constant(cv), Operand::Copy(src))
                        if src.local == local_idx && src.projections.is_empty() =>
                    {
                        return const_to_i128(cv);
                    }
                    Rvalue::BinaryOp(BinOp::Sub, Operand::Copy(src), Operand::Constant(cv))
                        if src.local == local_idx && src.projections.is_empty() =>
                    {
                        return const_to_i128(cv).map(|v| -v);
                    }
                    _ => {}
                }
            }
        }
    }
    None
}

/// Find the loop bound from the loop header's SwitchInt or comparison.
///
/// Looks for patterns like:
///   - `cond = i < N; SwitchInt(cond)`  -> bound is N
///   - `cond = i > 0; SwitchInt(cond)`  -> bound is the initial value (heuristic)
fn find_loop_bound(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    local_idx: usize,
) -> Option<Formula> {
    let header_block = func.body.blocks.get(loop_info.header.0)?;

    // Search the header block's statements for a comparison involving local_idx
    for stmt in &header_block.stmts {
        if let Statement::Assign { rvalue, .. } = stmt {
            match rvalue {
                // i < bound or i <= bound
                Rvalue::BinaryOp(BinOp::Lt | BinOp::Le, Operand::Copy(lhs), rhs)
                    if lhs.local == local_idx && lhs.projections.is_empty() =>
                {
                    return Some(crate::operand_to_formula(func, rhs));
                }
                // bound > i or bound >= i
                Rvalue::BinaryOp(BinOp::Gt | BinOp::Ge, rhs, Operand::Copy(lhs))
                    if lhs.local == local_idx && lhs.projections.is_empty() =>
                {
                    return Some(crate::operand_to_formula(func, rhs));
                }
                _ => {}
            }
        }
    }

    None
}

/// Extract constant value as i128.
fn const_to_i128(cv: &ConstValue) -> Option<i128> {
    match cv {
        ConstValue::Int(n) => Some(*n),
        ConstValue::Uint(n, _) => Some(*n as i128),
        _ => None,
    }
}

/// Extract (index_local, array_place) pairs from index accesses in an rvalue.
fn extract_index_accesses(rvalue: &Rvalue) -> Vec<(usize, Place)> {
    let mut accesses = Vec::new();

    // Check operands for Index projections
    let operands: Vec<&Operand> = match rvalue {
        Rvalue::Use(op) => vec![op],
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => vec![a, b],
        Rvalue::UnaryOp(_, op) => vec![op],
        Rvalue::Cast(op, _) => vec![op],
        Rvalue::Aggregate(_, ops) => ops.iter().collect(),
        _ => vec![],
    };

    for op in operands {
        if let Operand::Copy(place) | Operand::Move(place) = op {
            for proj in &place.projections {
                if let Projection::Index(idx_local) = proj {
                    // The array is the place without the Index projection
                    let array_place = Place {
                        local: place.local,
                        projections: place
                            .projections
                            .iter()
                            .filter(|p| !matches!(p, Projection::Index(_)))
                            .cloned()
                            .collect(),
                    };
                    accesses.push((*idx_local, array_place));
                }
            }
        }
    }

    accesses
}

/// Find a Len variable for a given array/slice place.
///
/// Looks through the function body for `Rvalue::Len(place)` assignments.
fn find_len_variable(func: &VerifiableFunction, array_place: &Place) -> Option<String> {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place: dest, rvalue: Rvalue::Len(len_place), .. } = stmt
                && len_place.local == array_place.local {
                    let decl = func.body.locals.get(dest.local)?;
                    return Some(
                        decl.name
                            .clone()
                            .unwrap_or_else(|| format!("_{}", dest.local)),
                    );
                }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a counted loop function:
    /// ```
    /// fn sum_to_n(n: u32) -> u32 {
    ///     let mut i = 0;
    ///     let mut sum = 0;
    ///     while i < n { sum += i; i += 1; }
    ///     sum
    /// }
    /// ```
    fn sum_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "sum_to_n".to_string(),
            def_path: "test::sum_to_n".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },           // return
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    // bb0: i = 0; sum = 0; goto bb1
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
                    // bb1 (loop header): cond = i < n; SwitchInt(cond) -> [1: bb2, else: bb3]
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
                    // bb2 (loop body): sum = sum + i; i = i + 1; goto bb1
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
                        terminator: Terminator::Goto(BlockId(1)), // back-edge
                    },
                    // bb3 (exit): _0 = sum; return
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

    /// Build a search loop with array index access:
    /// ```
    /// fn linear_search(arr: &[u32], target: u32) -> bool {
    ///     let len = arr.len();
    ///     let mut i = 0;
    ///     while i < len { if arr[i] == target { return true; } i += 1; }
    ///     false
    /// }
    /// ```
    fn search_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "linear_search".to_string(),
            def_path: "test::linear_search".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },            // return
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }) },
                        name: Some("arr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("target".into()) },
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("len".into()) },
                    LocalDecl { index: 4, ty: Ty::usize(), name: Some("i".into()) },
                    LocalDecl { index: 5, ty: Ty::Bool, name: Some("cond".into()) },
                    LocalDecl { index: 6, ty: Ty::u32(), name: Some("elem".into()) },
                ],
                blocks: vec![
                    // bb0: len = arr.len(); i = 0; goto bb1
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
                    // bb1 (loop header): cond = i < len; SwitchInt -> [1: bb2, else: bb3]
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
                    // bb2 (loop body): elem = arr[i]; i += 1; goto bb1
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

    /// Build a simple function with no loops.
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

    /// Build a function with a user-annotated invariant.
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
        let invariants = infer_loop_invariants(&func);
        assert!(invariants.is_empty(), "no-loop function should have no invariants");
    }

    #[test]
    fn test_counter_bounds_inferred() {
        let func = sum_loop_function();
        let invariants = infer_loop_invariants(&func);

        // Should find counter bounds for `i` (0 <= i <= n)
        let counter_bounds: Vec<_> = invariants
            .iter()
            .filter(|inv| inv.source == InvariantSource::CounterBounds)
            .collect();
        assert!(
            !counter_bounds.is_empty(),
            "should infer counter bounds for `i`"
        );
        // Counter bounds should have the loop header
        assert_eq!(counter_bounds[0].loop_header, BlockId(1));
        assert!(counter_bounds[0].confidence > 0.0);
    }

    #[test]
    fn test_monotonic_accumulator_inferred() {
        let func = sum_loop_function();
        let invariants = infer_loop_invariants(&func);

        // Should find monotonic accumulator for `sum` (sum >= 0)
        let monotonic: Vec<_> = invariants
            .iter()
            .filter(|inv| inv.source == InvariantSource::Monotonicity)
            .collect();
        assert!(
            !monotonic.is_empty(),
            "should infer monotonic accumulator for `sum`"
        );
    }

    #[test]
    fn test_index_bounds_inferred() {
        let func = search_loop_function();
        let invariants = infer_loop_invariants(&func);

        // Should find index bounds for `i < len`
        let idx_bounds: Vec<_> = invariants
            .iter()
            .filter(|inv| inv.source == InvariantSource::InductionVariable)
            .collect();
        assert!(
            !idx_bounds.is_empty(),
            "should infer index bounds for `i < len`"
        );
        assert!(idx_bounds[0].confidence >= 0.90);
    }

    #[test]
    fn test_user_annotated_invariant() {
        let func = annotated_loop_function();
        let invariants = infer_loop_invariants(&func);

        let user: Vec<_> = invariants
            .iter()
            .filter(|inv| inv.source == InvariantSource::UserAnnotated)
            .collect();
        assert_eq!(user.len(), 1, "should extract 1 user invariant");
        assert_eq!(user[0].confidence, 1.0);
        assert!(matches!(&user[0].expression, Formula::Var(name, Sort::Bool) if name == "i_le_n"));
    }

    #[test]
    fn test_invariants_sorted_by_confidence() {
        let func = annotated_loop_function();
        let invariants = infer_loop_invariants(&func);

        // User-annotated (1.0) should come first
        assert!(!invariants.is_empty());
        let confidences: Vec<f64> = invariants.iter().map(|inv| inv.confidence).collect();
        for window in confidences.windows(2) {
            assert!(
                window[0] >= window[1],
                "invariants should be sorted by confidence descending: {:?}",
                confidences
            );
        }
    }

    #[test]
    fn test_inject_invariants_empty() {
        let mut vcs = vec![VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }];
        let original = vcs[0].formula.clone();
        inject_invariants(&mut vcs, &[]);
        // No change when there are no invariants
        assert!(
            matches!(&vcs[0].formula, Formula::Bool(true)),
            "formula should be unchanged with no invariants: got {:?}, expected {:?}",
            vcs[0].formula,
            original
        );
    }

    #[test]
    fn test_inject_invariants_wraps_formula() {
        let mut vcs = vec![VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        }];
        let invariants = vec![InvariantCandidate {
            expression: Formula::Ge(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            confidence: 0.85,
            source: InvariantSource::CounterBounds,
            loop_header: BlockId(0),
        }];

        inject_invariants(&mut vcs, &invariants);

        // Formula should now be: Implies(invariant, original)
        assert!(
            matches!(&vcs[0].formula, Formula::Implies(_, _)),
            "injected invariant should wrap formula as Implies, got: {:?}",
            vcs[0].formula
        );
    }

    #[test]
    fn test_inject_multiple_invariants_creates_conjunction() {
        let mut vcs = vec![VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }];
        let invariants = vec![
            InvariantCandidate {
                expression: Formula::Ge(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                confidence: 0.85,
                source: InvariantSource::CounterBounds,
                loop_header: BlockId(0),
            },
            InvariantCandidate {
                expression: Formula::Le(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Var("n".to_string(), Sort::Int)),
                ),
                confidence: 0.80,
                source: InvariantSource::CounterBounds,
                loop_header: BlockId(0),
            },
        ];

        inject_invariants(&mut vcs, &invariants);

        // Should be: Implies(And([inv1, inv2]), original)
        match &vcs[0].formula {
            Formula::Implies(assumption, _body) => {
                assert!(
                    matches!(assumption.as_ref(), Formula::And(parts) if parts.len() == 2),
                    "multiple invariants should be conjoined: {:?}",
                    assumption
                );
            }
            other => panic!("expected Implies, got: {other:?}"),
        }
    }

    #[test]
    fn test_infer_invariants_end_to_end_sum() {
        let func = sum_loop_function();
        let invariants = infer_loop_invariants(&func);
        let mut vcs = crate::generate_vcs(&func);

        let original_count = vcs.len();
        inject_invariants(&mut vcs, &invariants);

        // VC count should not change (we wrap, not add)
        assert_eq!(vcs.len(), original_count);

        // If there are VCs, they should be wrapped with Implies
        if !vcs.is_empty() && !invariants.is_empty() {
            for vc in &vcs {
                assert!(
                    matches!(&vc.formula, Formula::Implies(_, _)),
                    "all VCs should be wrapped with invariant assumptions"
                );
            }
        }
    }

    #[test]
    fn test_infer_invariants_end_to_end_search() {
        let func = search_loop_function();
        let invariants = infer_loop_invariants(&func);

        // Should find both counter bounds and index bounds
        let sources: Vec<&InvariantSource> = invariants.iter().map(|i| &i.source).collect();
        assert!(
            sources.contains(&&InvariantSource::InductionVariable),
            "search loop should produce index bounds invariant, got: {:?}",
            sources
        );
    }

    #[test]
    fn test_find_step_pattern_increment() {
        let func = sum_loop_function();
        let loops = detect_loops(&func.body);
        assert!(!loops.is_empty());

        // Variable `i` (local 2) is incremented by 1
        let step = find_step_pattern(&func, &loops[0], 2);
        assert_eq!(step, Some(1), "i should be incremented by 1");
    }

    #[test]
    fn test_find_loop_bound() {
        let func = sum_loop_function();
        let loops = detect_loops(&func.body);
        assert!(!loops.is_empty());

        // Variable `i` (local 2) is compared against `n` (local 1)
        let bound = find_loop_bound(&func, &loops[0], 2);
        assert!(bound.is_some(), "should find loop bound for i < n");
        // The bound should reference variable `n`
        assert!(
            matches!(&bound.unwrap(), Formula::Var(name, Sort::Int) if name == "n"),
            "bound should be variable n"
        );
    }

    #[test]
    fn test_extract_index_accesses() {
        // arr[i] => Use(Copy(Place { local: 1, projections: [Index(4)] }))
        let rvalue = Rvalue::Use(Operand::Copy(Place {
            local: 1,
            projections: vec![Projection::Index(4)],
        }));
        let accesses = extract_index_accesses(&rvalue);
        assert_eq!(accesses.len(), 1);
        assert_eq!(accesses[0].0, 4); // index local
        assert_eq!(accesses[0].1.local, 1); // array local
    }

    #[test]
    fn test_extract_index_accesses_no_index() {
        let rvalue = Rvalue::Use(Operand::Copy(Place::local(1)));
        let accesses = extract_index_accesses(&rvalue);
        assert!(accesses.is_empty());
    }

    #[test]
    fn test_find_len_variable() {
        let func = search_loop_function();
        let array_place = Place::local(1);
        let len_var = find_len_variable(&func, &array_place);
        assert_eq!(len_var.as_deref(), Some("len"), "should find len variable for arr");
    }
}
