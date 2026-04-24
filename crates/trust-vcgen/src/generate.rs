// trust-vcgen/generate.rs: Core verification condition generation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

#[cfg(not(feature = "pipeline-v2"))]
use rayon::prelude::*;

use trust_types::{
    AssertMessage, BinOp, BlockId, ConstValue, Formula, GuardCondition, Operand, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

use crate::abstract_interp::{self, AbstractDomain, IntervalDomain};
// tRust #792/#797: v1 VC checker modules. Only negation and rvalue_safety remain;
// overflow, divzero, shifts, casts, float_ops, asserts, bounds deleted (migrated to zani-lib).
#[cfg(not(feature = "pipeline-v2"))]
use crate::{contracts, spec_parser};
use crate::{
    ffi_summary, ffi_vcgen, guards, memory_ordering, operand_to_formula, place_to_var_name,
    sep_engine, termination, unsafe_verify,
};

fn has_intrinsic_unsafe_surface(func: &VerifiableFunction) -> bool {
    if func.body.locals.iter().any(|local| ty_contains_raw_ptr(&local.ty)) {
        return true;
    }

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            if crate::place_has_raw_deref(func, place) {
                return true;
            }
            match rvalue {
                Rvalue::Use(operand) if crate::operand_has_raw_deref(func, operand) => {
                    return true;
                }
                Rvalue::Ref { place, .. } | Rvalue::CopyForDeref(place)
                    if crate::place_has_raw_deref(func, place) =>
                {
                    return true;
                }
                Rvalue::AddressOf(_, _) => return true,
                _ => {}
            }
        }

        if let Terminator::Call { func: callee, .. } = &block.terminator
            && crate::unsafe_verify::detection::is_unsafe_fn_call(callee)
        {
            return true;
        }
    }

    false
}

fn ty_contains_raw_ptr(ty: &Ty) -> bool {
    match ty {
        Ty::RawPtr { .. } => true,
        Ty::Ref { inner, .. } => ty_contains_raw_ptr(inner),
        Ty::Slice { elem } | Ty::Array { elem, .. } => ty_contains_raw_ptr(elem),
        _ => false,
    }
}

/// tRust #621: Build a map from block ID to accumulated path assumptions.
///
/// Path assumptions include:
/// 1. **Semantic assert-passed guards:** When a CheckedBinaryOp + Assert passes,
///    the no-overflow range constraint (e.g., hi >= lo for unsigned CheckedSub)
///    and the result definition (_N.0 = lhs op rhs) are propagated to successors.
/// 2. **Dataflow definitions:** Each assignment statement (e.g., `_4 = _3.0`,
///    `_5 = _4 / 2`) is converted to an equality constraint so the solver knows
///    intermediate locals are not free variables.
///
/// Uses BFS from the entry block, accumulating assumptions along the way.
/// Only forward propagation within the same path — assumptions respect
/// control flow.
// tRust #953: Enabled under both v1 and v2 paths. The v2 path's in-tree VC
// generator (below) uses the same guard-accumulation semantics as v1 to
// maintain correctness on safe-midpoint-style tests that rely on
// assert-passed dataflow (e.g., hi >= lo after CheckedSub passes).
pub(crate) fn build_semantic_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    use std::collections::VecDeque;

    const NOT_VISITED: u8 = 0;
    const VISITED_PRECISE: u8 = 1;
    const VISITED_WEAKENED: u8 = 2;

    let mut result: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let mut visited = vec![NOT_VISITED; func.body.blocks.len()];
    // BFS: (block_id, accumulated_path_assumptions)
    let mut queue: VecDeque<(BlockId, Vec<Formula>)> = VecDeque::new();
    queue.push_back((BlockId(0), Vec::new()));

    while let Some((block_id, mut acc_guards)) = queue.pop_front() {
        if block_id.0 >= func.body.blocks.len() {
            continue;
        }

        // tRust #803 P0-2: At join points (blocks reachable via multiple paths),
        // only keeping the first predecessor's guards is unsound — it creates
        // over-strong assumptions that can mask violations on the unrecorded
        // path. If a block is revisited with different guards, weaken the
        // block to Bool(true) and still reprocess its successors once so the
        // weaker assumptions reach downstream blocks. Bool(true) is the
        // terminal state: later revisits cannot weaken it further.
        match visited[block_id.0] {
            VISITED_WEAKENED => continue,
            VISITED_PRECISE => {
                let existing = result.get(&block_id).cloned().unwrap_or_default();
                if existing == acc_guards {
                    continue;
                }
                acc_guards = vec![Formula::Bool(true)];
                result.insert(block_id, acc_guards.clone());
                visited[block_id.0] = VISITED_WEAKENED;
            }
            NOT_VISITED => {
                visited[block_id.0] = VISITED_PRECISE;
                if !acc_guards.is_empty() {
                    result.insert(block_id, acc_guards.clone());
                }
            }
            _ => unreachable!("unexpected semantic guard visitation state"),
        }

        let block = &func.body.blocks[block_id.0];

        // Collect new assumptions from this block:
        // 1. Semantic assert-passed guards (range + result definition)
        // 2. Dataflow definitions from assignment statements
        let mut next_guards = acc_guards;
        let sem_formulas = guards::extract_assert_passed_semantics(func, block);
        next_guards.extend(sem_formulas);
        let defs = guards::extract_block_definitions(func, block);
        next_guards.extend(defs);

        // Propagate to successor blocks.
        // For Assert terminators, the target is the assert-passed successor.
        // For Goto/Call/Drop, propagate unchanged.
        // For SwitchInt, propagate to all targets (semantic guards are orthogonal
        // to branch conditions).
        match &block.terminator {
            Terminator::Assert { target, .. } => {
                queue.push_back((*target, next_guards));
            }
            Terminator::Goto(target) => {
                queue.push_back((*target, next_guards));
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for (_, target) in targets {
                    queue.push_back((*target, next_guards.clone()));
                }
                queue.push_back((*otherwise, next_guards));
            }
            Terminator::Call { target: Some(target), .. } => {
                queue.push_back((*target, next_guards));
            }
            Terminator::Call { target: None, .. } => {}
            Terminator::Drop { target, .. } => {
                queue.push_back((*target, next_guards));
            }
            Terminator::Return | Terminator::Unreachable => {}
            // tRust: Terminator is #[non_exhaustive]; unknown variants
            // are conservatively handled by not propagating guards.
            _ => {}
        }
    }

    result
}

/// Generate all verification conditions for a function.
///
/// tRust #21: Guard conditions from MIR control flow (SwitchInt, Assert) are
/// extracted via `path_map()` and threaded into each VC as path assumptions.
/// A VC in a guarded block becomes: guard_conjunction AND violation_formula,
/// so the solver only finds violations reachable under the actual path condition.
///
/// tRust #621: Assert-passed semantic guards. When a CheckedBinaryOp (e.g.,
/// CheckedSub) followed by an Assert passes, the no-overflow semantic meaning
/// (e.g., hi >= lo) is propagated to VCs in successor blocks. This eliminates
/// false positives where the solver finds counterexamples that are impossible
/// given the assert-passed condition.
pub fn generate_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    // tRust #792: v1 VC generation path — guard map, per-statement checkers,
    // bounds, asserts, unreachable. All gated behind pipeline-v2.
    #[cfg(not(feature = "pipeline-v2"))]
    let mut vcs: Vec<VerificationCondition> = {
        // tRust #21: Build path map to get guard conditions for each block.
        let path_map = func.body.path_map();
        let guard_map: FxHashMap<BlockId, Vec<GuardCondition>> =
            path_map.into_iter().map(|entry| (entry.block, entry.guards)).collect();

        // tRust #621: Build semantic assert-passed guard map.
        let semantic_guards = build_semantic_guard_map(func);

        // tRust #699: Parallel VC generation — each block produces VCs independently.
        let block_vcs: Vec<VerificationCondition> = func
            .body
            .blocks
            .par_iter()
            .flat_map(|block| {
                let mut block_vcs = Vec::new();

                // tRust #792/#797: v1 VC checker calls — overflow, divzero, shifts, casts,
                // float_ops, asserts, bounds all deleted (migrated to zani-lib).
                // Only negation and rvalue_safety remain in trust-vcgen.
                for stmt in &block.stmts {
                    if let Statement::Assign { place, rvalue, span } = stmt {
                        negation::check_negation_overflow(
                            func,
                            block,
                            rvalue,
                            span,
                            &mut block_vcs,
                        );
                        let dest_ty = rvalue_safety::place_ty(func, place);
                        rvalue_safety::check_rvalue_safety(
                            func,
                            block,
                            rvalue,
                            dest_ty.as_ref(),
                            span,
                            &mut block_vcs,
                        );
                    }
                }

                // tRust #21: Wrap newly-generated VCs with path guard assumptions.
                if let Some(block_guards) = guard_map.get(&block.id)
                    && !block_guards.is_empty()
                {
                    for vc in &mut block_vcs {
                        vc.formula =
                            guards::guarded_formula(func, block_guards, vc.formula.clone());
                    }
                }

                // tRust #621: Wrap with semantic assert-passed guards.
                if let Some(sem_guards) = semantic_guards.get(&block.id) {
                    for vc in &mut block_vcs {
                        let mut conjuncts = sem_guards.clone();
                        conjuncts.push(vc.formula.clone());
                        vc.formula = Formula::And(conjuncts);
                    }
                }

                block_vcs
            })
            .collect();

        block_vcs
    };

    // tRust #953: Pipeline v2 path — generate real overflow/divzero VCs so that
    // integration tests calling `trust_vcgen::generate_vcs` (e.g.,
    // `real_z4_verification`, `m5_e2e_loop`) continue to receive meaningful
    // VCs after the v1 checker modules were migrated to trust-zani-lib. The
    // upstream MirRouter dispatches at a higher layer, but callers that still
    // invoke this function directly need safety VCs with real SMT formulas,
    // not an empty Vec.
    #[cfg(feature = "pipeline-v2")]
    let mut vcs: Vec<VerificationCondition> = generate_v2_safety_vcs(func);

    // tRust #712: Deterministic ordering after parallel generation.
    vcs.sort_by(|a, b| {
        a.location
            .file
            .cmp(&b.location.file)
            .then(a.location.line_start.cmp(&b.location.line_start))
            .then(a.location.col_start.cmp(&b.location.col_start))
    });

    #[cfg(not(feature = "pipeline-v2"))]
    {
        contracts::check_contracts(func, &mut vcs);
        // tRust #119: Generate VCs from FunctionSpec (#[requires], #[ensures], #[invariant]).
        vcs.extend(spec_parser::generate_spec_vcs(func));
    }

    #[cfg(feature = "pipeline-v2")]
    vcs.extend(generate_v2_contract_vcs(func));
    // tRust #792: unreachable checking gated behind pipeline-v2.
    #[cfg(not(feature = "pipeline-v2"))]
    unreachable::check_unreachable(func, &mut vcs);

    // tRust #66: Termination checking via decreases clauses.
    termination::check_termination(func, &mut vcs);

    // tRust #79: Unsafe code verification with SAFETY comment extraction.
    // In the full compiler integration, comments come from the source map.
    // At the vcgen level, callers pass comments via check_unsafe() directly.
    // Here we run detection only (no comments available at this layer).
    if has_intrinsic_unsafe_surface(func) {
        unsafe_verify::check_unsafe(func, &[], &mut vcs);

        // tRust #436: Separation logic provenance engine — heap-aware VCs for
        // unsafe patterns (raw deref, alloc, dealloc, ptr::copy, transmute, etc.).
        vcs.extend(sep_engine::check_sep_unsafe(func));
    }

    // tRust #460: FFI boundary verification with summary-based VCs.
    // Detect Call terminators targeting extern/FFI functions and generate
    // targeted VCs (null checks, range checks, aliasing, return contracts)
    // instead of conservative Bool(true) from unsafe_verify.
    let ffi_db = ffi_summary::FfiSummaryDb::new();
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, span, .. } = &block.terminator
            && ffi_vcgen::is_extern_call(callee, &ffi_db)
        {
            let arg_formulas: Vec<Formula> =
                args.iter().map(|op| operand_to_formula(func, op)).collect();
            let dest_var = place_to_var_name(func, dest);
            vcs.extend(ffi_vcgen::generate_call_site_vcs(
                &func.name,
                callee,
                &arg_formulas,
                &dest_var,
                span,
                &ffi_db,
            ));
        }
    }

    // tRust #609: Atomic ordering legality VCs.
    // Collect atomic operations from Call terminators and check C++ standard
    // legality rules (L1-L5) via MemoryModelChecker::check_operation_legality.
    {
        let atomic_ops: Vec<_> = func
            .body
            .blocks
            .iter()
            .filter_map(|block| {
                if let Terminator::Call { atomic: Some(ref op), .. } = block.terminator {
                    Some(op.clone())
                } else {
                    None
                }
            })
            .collect();
        if !atomic_ops.is_empty() {
            vcs.extend(memory_ordering::MemoryModelChecker::check_operation_legality(
                &atomic_ops,
                &func.name,
            ));
        }
    }

    vcs
}

/// Generate VCs and run an abstract interpretation pre-pass to discharge
/// VCs provable without a solver.
///
/// tRust #357, #428: Returns `(solver_vcs, discharged_results)` where
/// `solver_vcs` are VCs that still need a solver and `discharged_results`
/// are VCs already proved by interval analysis.
#[must_use]
pub fn generate_vcs_with_discharge(
    func: &VerifiableFunction,
) -> (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>) {
    let all_vcs = generate_vcs(func);
    if all_vcs.is_empty() {
        return (all_vcs, Vec::new());
    }

    // tRust #357, #452: Use type-aware initial state for tighter interval bounds,
    // then compute fixpoint with threshold widening, delayed widening, condition
    // narrowing, and descending narrowing for precision recovery.
    let initial = abstract_interp::type_aware_initial_state(func);
    let config = abstract_interp::FixpointConfig::for_function(func);
    let fp = abstract_interp::fixpoint_configured(func, initial, &config);

    // tRust #428: Merge all block-level interval states into a single
    // environment for VC discharge. Each block's state refines the
    // function-level picture — join gives a sound over-approximation.
    let mut merged_env = IntervalDomain::bottom();
    for state in fp.block_states.values() {
        merged_env = merged_env.join(state);
    }

    // Discharge VCs that interval analysis can prove.
    let report = abstract_interp::try_discharge_batch(&all_vcs, &merged_env);

    let discharged_map: FxHashMap<usize, VerificationResult> =
        report.discharged.into_iter().collect();
    let mut solver_vcs = Vec::new();
    let mut discharged = Vec::new();
    for (i, vc) in all_vcs.into_iter().enumerate() {
        if let Some(result) = discharged_map.get(&i) {
            discharged.push((vc, result.clone()));
        } else {
            // tRust #451: Augment remaining VCs with abstract-state assumptions
            // before solver dispatch. The abstract state is an over-approximation
            // of all concrete executions: adding its constraints as conjuncts to
            // the violation formula narrows the solver's search space without
            // excluding real counterexamples. If the environment is Top (no
            // finite bounds), the VC is returned unchanged.
            solver_vcs.push(abstract_interp::augment_vc_with_abstract_state(&vc, &merged_env));
        }
    }

    (solver_vcs, discharged)
}

// ---------------------------------------------------------------------------
// tRust #953: Pipeline v2 VC generator
// ---------------------------------------------------------------------------

/// Generate safety VCs (overflow, divzero, remainder-by-zero) with real SMT
/// formulas for the pipeline-v2 code path.
///
/// When v2 was introduced (#792), `generate_vcs` was reduced to a stub that
/// returned an empty Vec. Downstream integration tests (`real_z4_verification`,
/// `m5_e2e_loop`) call this function directly and expect formulas a solver
/// can reason about — not an empty Vec or `Formula::Bool(false)` placeholders.
///
/// This generator walks each block and emits:
///
/// - **Overflow VCs** for `Assert { msg: Overflow(op), .. }` paired with a
///   `CheckedBinaryOp(op, lhs, rhs)` in the same block. The emitted formula
///   is `input_ranges(lhs,rhs) AND NOT in_range_of_result_type(lhs op rhs)` —
///   satisfiable iff the operation can overflow given the input types.
/// - **Division/remainder-by-zero VCs** for `BinaryOp(Div|Rem, _, divisor)`
///   statements whose block is not already reached through a `DivisionByZero`
///   assert target. The emitted formula is `divisor == 0` when `divisor` is
///   a variable, or a constant check when it's a literal.
///
/// Semantic guards from `build_semantic_guard_map` are conjoined to each VC
/// so successor blocks inherit the assert-passed dataflow (e.g., after a
/// passing `CheckedSub`, downstream overflow checks see `hi >= lo`).
#[cfg(feature = "pipeline-v2")]
fn generate_v2_safety_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let guard_map: FxHashMap<BlockId, Vec<GuardCondition>> =
        func.body.path_map().into_iter().map(|entry| (entry.block, entry.guards)).collect();
    let path_definition_map = v2_build_path_definition_map(func);
    let semantic_guards = build_semantic_guard_map(func);
    let zero_guard_targets = v2_zero_divisor_guard_targets(func);
    let overflow_guard_targets = v2_overflow_guard_targets(func);
    let negation_guard_targets = v2_negation_guard_targets(func);

    // Track the originating block id alongside each VC so we can apply the
    // correct semantic guards. Matching by span is unreliable when multiple
    // blocks share `SourceSpan::default()` (as in many synthetic test MIRs).
    let mut block_vcs: Vec<(BlockId, VerificationCondition)> = Vec::new();

    for block in &func.body.blocks {
        // 1. VCs from rustc Assert terminators that guard safety checks.
        if let Terminator::Assert { cond, expected, msg, span, target } = &block.terminator {
            let vc = match msg {
                AssertMessage::DivisionByZero => Some(VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula: v2_formula_with_block_defs(
                        func,
                        block,
                        v2_assert_failure_formula(func, cond, *expected),
                    ),
                    contract_metadata: None,
                }),
                AssertMessage::RemainderByZero => Some(VerificationCondition {
                    kind: VcKind::RemainderByZero,
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula: v2_formula_with_block_defs(
                        func,
                        block,
                        v2_assert_failure_formula(func, cond, *expected),
                    ),
                    contract_metadata: None,
                }),
                AssertMessage::Overflow(op) => {
                    v2_build_assert_overflow_vc(func, block, *target, *op, cond, *expected, span)
                }
                AssertMessage::OverflowNeg => {
                    v2_build_assert_negation_vc(func, block, *target, cond, *expected, span)
                }
                AssertMessage::BoundsCheck => {
                    v2_build_bounds_assert_vc(func, block, *target, cond, *expected, span)
                }
                AssertMessage::Custom(message) => Some(VerificationCondition {
                    kind: VcKind::Assertion { message: message.clone() },
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula: v2_formula_with_block_defs(
                        func,
                        block,
                        v2_assert_failure_formula(func, cond, *expected),
                    ),
                    contract_metadata: None,
                }),
                _ => None,
            };
            if let Some(vc) = vc {
                block_vcs.push((block.id, vc));
            }
        }

        // 1b. Panic-style assertion/unreachable terminators from native MIR.
        if let Some(vc) = v2_build_terminator_vc(func, block) {
            block_vcs.push((block.id, vc));
        }

        for stmt in &block.stmts {
            let Statement::Assign { rvalue, span, .. } = stmt else {
                continue;
            };
            match rvalue {
                Rvalue::BinaryOp(BinOp::Div, lhs, divisor) => {
                    let is_float =
                        v2_is_float_operand(func, lhs) || v2_is_float_operand(func, divisor);

                    if !zero_guard_targets.contains(&block.id)
                        && !v2_divisor_is_nonzero_constant(divisor)
                    {
                        block_vcs.push((
                            block.id,
                            VerificationCondition {
                                kind: if is_float {
                                    VcKind::FloatDivisionByZero
                                } else {
                                    VcKind::DivisionByZero
                                },
                                function: func.name.clone().into(),
                                location: span.clone(),
                                formula: v2_formula_with_block_defs(
                                    func,
                                    block,
                                    v2_divisor_is_zero_formula(func, divisor),
                                ),
                                contract_metadata: None,
                            },
                        ));
                    }

                    if !is_float
                        && !overflow_guard_targets.contains(&block.id)
                        && let Some(vc) = v2_build_signed_div_overflow_vc(
                            func,
                            block,
                            BinOp::Div,
                            lhs,
                            divisor,
                            span,
                        )
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::BinaryOp(BinOp::Rem, _, divisor) => {
                    if !zero_guard_targets.contains(&block.id)
                        && !v2_divisor_is_nonzero_constant(divisor)
                    {
                        block_vcs.push((
                            block.id,
                            VerificationCondition {
                                kind: VcKind::RemainderByZero,
                                function: func.name.clone().into(),
                                location: span.clone(),
                                formula: v2_formula_with_block_defs(
                                    func,
                                    block,
                                    v2_divisor_is_zero_formula(func, divisor),
                                ),
                                contract_metadata: None,
                            },
                        ));
                    }
                }
                Rvalue::BinaryOp(op @ (BinOp::Shl | BinOp::Shr), lhs, rhs)
                    if !overflow_guard_targets.contains(&block.id) =>
                {
                    if let Some(vc) = v2_build_shift_overflow_vc(func, block, *op, lhs, rhs, span) {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Mul), lhs, rhs)
                    if v2_is_float_operand(func, lhs) || v2_is_float_operand(func, rhs) =>
                {
                    if let Some(vc) = v2_build_float_overflow_vc(
                        func,
                        block,
                        *op,
                        lhs,
                        rhs,
                        span,
                        guard_map.get(&block.id).map(Vec::as_slice),
                    ) {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::Cast(operand, to_ty) => {
                    if let Some(vc) = v2_build_cast_vc(func, block, operand, to_ty, span) {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::UnaryOp(trust_types::UnOp::Neg, operand)
                    if !negation_guard_targets.contains(&block.id) =>
                {
                    if let Some(vc) = v2_build_negation_raw_vc(func, block, operand, span) {
                        block_vcs.push((block.id, vc));
                    }
                }
                _ => {}
            }
        }
    }

    // Conjoin predecessor definitions before guards so successor-block VCs
    // retain the boolean/int locals that made the path reachable.
    for (block_id, vc) in &mut block_vcs {
        if let Some(path_defs) = path_definition_map.get(block_id)
            && !path_defs.is_empty()
        {
            let mut conjuncts = path_defs.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Conjoin path guards so panic/unreachable VCs stay path-sensitive.
    for (block_id, vc) in &mut block_vcs {
        if let Some(block_guards) = guard_map.get(block_id)
            && !block_guards.is_empty()
        {
            vc.formula = guards::guarded_formula(func, block_guards, vc.formula.clone());
        }
    }

    // Conjoin semantic assert-passed guards onto each VC so downstream
    // overflow checks inherit the dataflow (e.g., hi >= lo after CheckedSub).
    for (block_id, vc) in &mut block_vcs {
        if let Some(sem_guards) = semantic_guards.get(block_id)
            && !sem_guards.is_empty()
        {
            let mut conjuncts = sem_guards.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // tRust #953: Also conjoin the function's preconditions. Downstream tests
    // (safe_midpoint) encode invariants like `lo <= hi` in `preconditions`,
    // which the v1 path threaded through spec_parser but the v2 path must
    // surface explicitly to keep the safe/buggy distinction.
    if !func.preconditions.is_empty() {
        for (_, vc) in &mut block_vcs {
            let mut conjuncts = func.preconditions.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    block_vcs.into_iter().map(|(_, vc)| vc).collect()
}

/// Build a real overflow VC for `CheckedBinaryOp(op, lhs, rhs)` feeding an
/// `Assert { Overflow(op) }` terminator.
///
/// Formula: `input_range(lhs) AND input_range(rhs) AND NOT in_range(lhs op rhs)`.
/// SAT iff the operation overflows for some in-range inputs → test is_failed().
#[cfg(feature = "pipeline-v2")]
fn v2_build_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    // Find the CheckedBinaryOp assignment in this block that matches `op`.
    let (lhs, rhs) = block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(stmt_op, l, r), .. } = stmt else {
            return None;
        };
        if *stmt_op == op { Some((l, r)) } else { None }
    })?;

    let lhs_ty = crate::operand_ty(func, lhs)?;
    let rhs_ty = crate::operand_ty(func, rhs)?;
    let width = lhs_ty.int_width()?;
    let signed = lhs_ty.is_signed();

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        // Other checked ops (Shl/Shr/Div) have different semantics; skip.
        _ => return None,
    };

    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);
    let min_f = crate::range::type_min_formula(width, signed);
    let max_f = crate::range::type_max_formula(width, signed);
    let out_of_range = Formula::Or(vec![
        Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
        Formula::Gt(Box::new(result), Box::new(max_f)),
    ]);

    let formula = v2_formula_with_block_defs(
        func,
        block,
        Formula::And(vec![lhs_range, rhs_range, out_of_range]),
    );

    Some(VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
        function: func.name.clone().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_assert_failure_formula(func: &VerifiableFunction, cond: &Operand, expected: bool) -> Formula {
    let cond_f = operand_to_formula(func, cond);
    if expected { Formula::Not(Box::new(cond_f)) } else { cond_f }
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_terminator_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<VerificationCondition> {
    let (kind, span) = match &block.terminator {
        Terminator::Unreachable => (VcKind::Unreachable, v2_block_span(func, block)),
        Terminator::Call { func: callee, span, .. } if v2_is_unreachable_panic_call(callee) => {
            (VcKind::Unreachable, span.clone())
        }
        Terminator::Call { func: callee, span, .. } if v2_is_assertion_panic_call(callee) => {
            let kind = if v2_is_unreachable_panic_chain(func, block.id) {
                VcKind::Unreachable
            } else {
                VcKind::Assertion { message: format!("panic call: {callee}") }
            };
            (kind, span.clone())
        }
        _ => return None,
    };

    Some(VerificationCondition {
        kind,
        function: func.name.clone().into(),
        location: span,
        formula: Formula::Bool(true),
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_is_assertion_panic_call(callee: &str) -> bool {
    callee.contains("begin_panic")
        || callee.contains("panic_fmt")
        || callee.contains("panic_display")
        || callee.contains("assert_failed")
}

#[cfg(feature = "pipeline-v2")]
fn v2_is_unreachable_panic_call(callee: &str) -> bool {
    callee.contains("unreachable_display")
}

#[cfg(feature = "pipeline-v2")]
fn v2_is_unreachable_panic_chain(func: &VerifiableFunction, block_id: BlockId) -> bool {
    fn dfs(
        func: &VerifiableFunction,
        block_id: BlockId,
        seen: &mut std::collections::HashSet<BlockId>,
    ) -> bool {
        if !seen.insert(block_id) {
            return false;
        }

        for pred in func
            .body
            .blocks
            .iter()
            .filter(|bb| v2_terminator_targets(&bb.terminator).contains(&block_id))
        {
            match &pred.terminator {
                Terminator::Call { func: callee, .. }
                    if callee.contains("from_str_nonconst")
                        || callee.contains("unreachable_display") =>
                {
                    return true;
                }
                Terminator::Call { target: Some(_), .. }
                | Terminator::Goto(_)
                | Terminator::Drop { .. } => {
                    if dfs(func, pred.id, seen) {
                        return true;
                    }
                }
                _ => {}
            }
        }

        false
    }

    dfs(func, block_id, &mut std::collections::HashSet::new())
}

#[cfg(feature = "pipeline-v2")]
fn v2_terminator_targets(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut blocks = targets.iter().map(|(_, target)| *target).collect::<Vec<_>>();
            blocks.push(*otherwise);
            blocks
        }
        Terminator::Call { target: Some(target), .. } => vec![*target],
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![*target],
        Terminator::Return | Terminator::Call { target: None, .. } | Terminator::Unreachable => {
            vec![]
        }
        _ => vec![],
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_block_span(func: &VerifiableFunction, block: &trust_types::BasicBlock) -> SourceSpan {
    block
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            Statement::Assign { span, .. } => Some(span.clone()),
            _ => None,
        })
        .unwrap_or_else(|| func.span.clone())
}

#[cfg(feature = "pipeline-v2")]
fn v2_is_float_operand(func: &VerifiableFunction, operand: &Operand) -> bool {
    matches!(crate::operand_ty(func, operand), Some(trust_types::Ty::Float { .. }))
}

/// Is `divisor` a literal constant guaranteed to be nonzero? If so, we can
/// skip emitting the divzero VC entirely — it's trivially proved-safe.
#[cfg(feature = "pipeline-v2")]
fn v2_divisor_is_nonzero_constant(divisor: &Operand) -> bool {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => *v != 0,
        Operand::Constant(ConstValue::Uint(v, _)) => *v != 0,
        Operand::Constant(ConstValue::Float(v)) => *v != 0.0,
        _ => false,
    }
}

/// Build a divisor-is-zero formula for `BinaryOp(Div|Rem, _, divisor)`.
///
/// For constant divisors this reduces to `Bool(divisor == 0)` (always UNSAT
/// for nonzero constants, always SAT for literal zero). For variable divisors
/// it emits `var == 0`, which is satisfiable iff the divisor can be zero —
/// the solver finds a witness assignment and the VC is reported as Failed.
#[cfg(feature = "pipeline-v2")]
fn v2_divisor_is_zero_formula(func: &VerifiableFunction, divisor: &Operand) -> Formula {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => Formula::Bool(*v == 0),
        Operand::Constant(ConstValue::Uint(v, _)) => Formula::Bool(*v == 0),
        Operand::Constant(ConstValue::Float(v)) => Formula::Bool(*v == 0.0),
        Operand::Constant(_) => Formula::Bool(false),
        Operand::Copy(_) | Operand::Move(_) | Operand::Symbolic(_) => {
            let value = match divisor {
                Operand::Copy(_) | Operand::Move(_) => operand_to_formula(func, divisor),
                Operand::Symbolic(formula) => formula.clone(),
                _ => unreachable!(),
            };
            if let Some(Ty::Float { width }) = crate::operand_ty(func, divisor) {
                v2_float_is_zero_formula(value, width)
            } else {
                Formula::Eq(Box::new(value), Box::new(v2_zero_formula_for_operand(func, divisor)))
            }
        }
        _ => Formula::Bool(false),
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_float_is_zero_formula(value: Formula, width: u32) -> Formula {
    Formula::Eq(
        Box::new(v2_float_magnitude_bits(value, width)),
        Box::new(Formula::BitVec { value: 0, width: width - 1 }),
    )
}

#[cfg(feature = "pipeline-v2")]
fn v2_float_magnitude_bits(value: Formula, width: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(value), high: width - 2, low: 0 }
}

#[cfg(feature = "pipeline-v2")]
fn v2_zero_formula_for_operand(func: &VerifiableFunction, operand: &Operand) -> Formula {
    if v2_is_float_operand(func, operand) {
        Formula::BitVec { value: 0, width: 64 }
    } else {
        match operand {
            Operand::Symbolic(formula) => v2_zero_formula_for_formula(formula),
            _ => Formula::Int(0),
        }
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_zero_formula_for_formula(formula: &Formula) -> Formula {
    match formula {
        Formula::Var(_, Sort::BitVec(width)) | Formula::SymVar(_, Sort::BitVec(width)) => {
            Formula::BitVec { value: 0, width: *width }
        }
        Formula::BitVec { width, .. } => Formula::BitVec { value: 0, width: *width },
        _ => Formula::Int(0),
    }
}

/// Return the set of block IDs that are the pass-through target of a
/// `DivisionByZero` or `RemainderByZero` Assert. The rustc-inserted assert
/// already guards the Div/Rem statement in the target block, so emitting a
/// second divzero VC there would be redundant (and could trigger spurious
/// failures when the formula doesn't see the assert guard).
#[cfg(feature = "pipeline-v2")]
fn v2_zero_divisor_guard_targets(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    func.body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert {
                msg:
                    trust_types::AssertMessage::DivisionByZero
                    | trust_types::AssertMessage::RemainderByZero,
                target,
                ..
            } => Some(*target),
            _ => None,
        })
        .collect()
}

#[cfg(feature = "pipeline-v2")]
fn v2_guard_targets_matching(
    func: &VerifiableFunction,
    pred: impl Fn(&AssertMessage) -> bool,
) -> std::collections::HashSet<BlockId> {
    func.body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert { msg, target, .. } if pred(msg) => Some(*target),
            _ => None,
        })
        .collect()
}

#[cfg(feature = "pipeline-v2")]
fn v2_overflow_guard_targets(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    v2_guard_targets_matching(func, |msg| {
        matches!(msg, AssertMessage::Overflow(BinOp::Div | BinOp::Shl | BinOp::Shr))
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_negation_guard_targets(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    v2_guard_targets_matching(func, |msg| matches!(msg, AssertMessage::OverflowNeg))
}

#[cfg(feature = "pipeline-v2")]
fn v2_formula_with_block_defs(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> Formula {
    let defs = guards::extract_block_definitions(func, block);
    if defs.is_empty() {
        formula
    } else {
        let mut conjuncts = defs;
        conjuncts.push(formula);
        Formula::And(conjuncts)
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_find_target_binary_operands<'a>(
    func: &'a VerifiableFunction,
    target: BlockId,
    op: BinOp,
) -> Option<(&'a Operand, &'a Operand)> {
    let block = func.body.blocks.get(target.0)?;
    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { rvalue, .. } = stmt else {
            return None;
        };
        match rvalue {
            Rvalue::BinaryOp(stmt_op, lhs, rhs) | Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs)
                if *stmt_op == op =>
            {
                Some((lhs, rhs))
            }
            _ => None,
        }
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_find_condition_binary_operands<'a>(
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
) -> Option<(BinOp, &'a Operand, &'a Operand)> {
    let cond_local = match cond {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };

    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if place.local != cond_local || !place.projections.is_empty() {
            return None;
        }
        match rvalue {
            Rvalue::BinaryOp(op, lhs, rhs) => Some((*op, lhs, rhs)),
            _ => None,
        }
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_find_target_neg_operand<'a>(
    func: &'a VerifiableFunction,
    target: BlockId,
) -> Option<&'a Operand> {
    let block = func.body.blocks.get(target.0)?;
    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { rvalue, .. } = stmt else {
            return None;
        };
        match rvalue {
            Rvalue::UnaryOp(trust_types::UnOp::Neg, operand) => Some(operand),
            _ => None,
        }
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_assert_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    op: BinOp,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    if let Some(vc) = v2_build_overflow_vc(func, block, op, span) {
        return Some(vc);
    }

    let (lhs, rhs) = v2_find_target_binary_operands(func, target, op)?;
    match op {
        BinOp::Shl | BinOp::Shr => v2_build_shift_overflow_vc(func, block, op, lhs, rhs, span),
        BinOp::Div | BinOp::Rem => v2_build_signed_div_overflow_vc(func, block, op, lhs, rhs, span),
        _ => {
            let lhs_ty = crate::operand_ty(func, lhs)?;
            let rhs_ty = crate::operand_ty(func, rhs)?;
            Some(VerificationCondition {
                kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                function: func.name.clone().into(),
                location: span.clone(),
                formula: v2_formula_with_block_defs(
                    func,
                    block,
                    v2_assert_failure_formula(func, cond, expected),
                ),
                contract_metadata: None,
            })
        }
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_assert_negation_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let operand = v2_find_target_neg_operand(func, target)?;
    let ty = crate::operand_ty(func, operand)?;
    if !ty.is_signed() {
        return None;
    }

    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(
            func,
            block,
            v2_assert_failure_formula(func, cond, expected),
        ),
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_bounds_assert_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let kind = v2_infer_bounds_kind(func, target)?;
    let direct_formula =
        if let Some((BinOp::Lt, lhs, rhs)) = v2_find_condition_binary_operands(block, cond) {
            let lhs_f = operand_to_formula(func, lhs);
            let rhs_f = operand_to_formula(func, rhs);
            let violation = if crate::operand_ty(func, lhs).as_ref().is_some_and(Ty::is_signed) {
                Formula::Or(vec![
                    Formula::Lt(Box::new(lhs_f.clone()), Box::new(Formula::Int(0))),
                    Formula::Ge(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
                ])
            } else {
                Formula::Ge(Box::new(lhs_f.clone()), Box::new(rhs_f.clone()))
            };
            v2_formula_with_block_defs(func, block, violation)
        } else {
            v2_formula_with_block_defs(func, block, v2_assert_failure_formula(func, cond, expected))
        };
    Some(VerificationCondition {
        kind,
        function: func.name.clone().into(),
        location: span.clone(),
        formula: direct_formula,
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_infer_bounds_kind(func: &VerifiableFunction, target: BlockId) -> Option<VcKind> {
    let block = func.body.blocks.get(target.0)?;
    for stmt in &block.stmts {
        let Statement::Assign { rvalue, .. } = stmt else {
            continue;
        };
        let indexed = match rvalue {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if v2_place_has_index(place) =>
            {
                place
            }
            _ => continue,
        };
        return Some(if v2_place_uses_slice(func, indexed) {
            VcKind::SliceBoundsCheck
        } else {
            VcKind::IndexOutOfBounds
        });
    }

    Some(VcKind::IndexOutOfBounds)
}

#[cfg(feature = "pipeline-v2")]
fn v2_place_has_index(place: &trust_types::Place) -> bool {
    place.projections.iter().any(|proj| {
        matches!(
            proj,
            trust_types::Projection::Index(_)
                | trust_types::Projection::ConstantIndex { .. }
                | trust_types::Projection::Subslice { .. }
        )
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_place_uses_slice(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    let Some(mut ty) = func.body.locals.get(place.local).map(|decl| decl.ty.clone()) else {
        return false;
    };

    for proj in &place.projections {
        match (proj, &ty) {
            (trust_types::Projection::Deref, Ty::Ref { inner, .. }) => ty = *inner.clone(),
            (trust_types::Projection::Deref, Ty::RawPtr { pointee, .. }) => ty = *pointee.clone(),
            (
                trust_types::Projection::Index(_)
                | trust_types::Projection::ConstantIndex { .. }
                | trust_types::Projection::Subslice { .. },
                Ty::Slice { .. },
            ) => return true,
            (
                trust_types::Projection::Index(_)
                | trust_types::Projection::ConstantIndex { .. }
                | trust_types::Projection::Subslice { .. },
                Ty::Array { .. },
            ) => return false,
            (trust_types::Projection::Field(index), Ty::Tuple(fields)) => {
                ty = fields.get(*index).cloned().unwrap_or(Ty::Unit)
            }
            (trust_types::Projection::Field(index), Ty::Adt { fields, .. }) => {
                ty = fields.get(*index).map(|(_, field_ty)| field_ty.clone()).unwrap_or(Ty::Unit)
            }
            _ => {}
        }
    }

    false
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_signed_div_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let lhs_ty = crate::operand_ty(func, lhs)?;
    let rhs_ty = crate::operand_ty(func, rhs)?;
    if !lhs_ty.is_signed() || !rhs_ty.is_signed() {
        return None;
    }

    let width = lhs_ty.int_width()?;
    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, true);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, rhs_ty.int_width()?, true);
    let int_min = crate::range::type_min_formula(width, true);
    let formula = v2_formula_with_block_defs(
        func,
        block,
        Formula::And(vec![
            lhs_range,
            rhs_range,
            Formula::Eq(Box::new(lhs_f), Box::new(int_min)),
            Formula::Eq(Box::new(rhs_f), Box::new(Formula::Int(-1))),
        ]),
    );

    Some(VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
        function: func.name.clone().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_shift_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let operand_ty = crate::operand_ty(func, lhs)?;
    let shift_ty = crate::operand_ty(func, rhs)?;
    let bit_width = i128::from(operand_ty.int_width()?);
    let shift_f = operand_to_formula(func, rhs);
    let shift_range = if let Some(width) = shift_ty.int_width() {
        crate::range::input_range_constraint(&shift_f, width, shift_ty.is_signed())
    } else {
        Formula::Bool(true)
    };

    let invalid_shift = if shift_ty.is_signed() {
        Formula::Or(vec![
            Formula::Lt(Box::new(shift_f.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(shift_f), Box::new(Formula::Int(bit_width))),
        ])
    } else {
        Formula::Ge(Box::new(shift_f), Box::new(Formula::Int(bit_width)))
    };

    Some(VerificationCondition {
        kind: VcKind::ShiftOverflow { op, operand_ty, shift_ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(
            func,
            block,
            Formula::And(vec![shift_range, invalid_shift]),
        ),
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_cast_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    operand: &Operand,
    to_ty: &Ty,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let from_ty = crate::operand_ty(func, operand)?;
    let Some((to_min, to_max)) = v2_integer_bounds(to_ty) else {
        return None;
    };
    let Some(width) = from_ty.int_width() else {
        return None;
    };

    if let Some((from_min, from_max)) = v2_integer_bounds(&from_ty)
        && from_min >= to_min
        && from_max <= to_max
    {
        return None;
    }

    let value = operand_to_formula(func, operand);
    let formula = Formula::And(vec![
        crate::range::input_range_constraint(&value, width, from_ty.is_signed()),
        Formula::Or(vec![
            Formula::Lt(Box::new(value.clone()), Box::new(Formula::Int(to_min))),
            Formula::Gt(Box::new(value), Box::new(Formula::Int(to_max))),
        ]),
    ]);

    Some(VerificationCondition {
        kind: VcKind::CastOverflow { from_ty, to_ty: to_ty.clone() },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(func, block, formula),
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_integer_bounds(ty: &Ty) -> Option<(i128, i128)> {
    let Ty::Int { width, signed } = ty else {
        return None;
    };
    if *signed {
        if *width == 128 {
            Some((i128::MIN, i128::MAX))
        } else {
            Some((-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1))
        }
    } else if *width < 128 {
        Some((0, (1i128 << width) - 1))
    } else {
        None
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_negation_raw_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    operand: &Operand,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let ty = crate::operand_ty(func, operand)?;
    if !ty.is_signed() {
        return None;
    }
    let width = ty.int_width()?;
    let value = operand_to_formula(func, operand);
    let int_min = crate::range::type_min_formula(width, true);
    let formula = Formula::And(vec![
        crate::range::input_range_constraint(&value, width, true),
        Formula::Eq(Box::new(value), Box::new(int_min)),
    ]);

    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(func, block, formula),
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_float_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    block_guards: Option<&[GuardCondition]>,
) -> Option<VerificationCondition> {
    let operand_ty = crate::operand_ty(func, lhs)?;
    if !matches!(operand_ty, Ty::Float { .. }) {
        return None;
    }

    let formula = v2_float_bound_guard_formula(func, lhs, rhs, block_guards)
        .or_else(|| v2_float_overflow_witness_formula(func, op, lhs, rhs))?;

    Some(VerificationCondition {
        kind: VcKind::FloatOverflowToInfinity { op, operand_ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(func, block, formula),
        contract_metadata: None,
    })
}

#[cfg(feature = "pipeline-v2")]
fn v2_float_bound_guard_formula(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    block_guards: Option<&[GuardCondition]>,
) -> Option<Formula> {
    let guards = block_guards?;
    let lhs_guard = v2_abs_guard_local_for_operand(func, lhs)?;
    let rhs_guard = v2_abs_guard_local_for_operand(func, rhs)?;
    let mut lhs_seen = false;
    let mut rhs_seen = false;

    for guard in guards {
        match guard {
            GuardCondition::SwitchIntMatch {
                discr: Operand::Copy(place) | Operand::Move(place),
                value,
            } if *value == 0 => {
                lhs_seen |= place.local == lhs_guard;
                rhs_seen |= place.local == rhs_guard;
            }
            GuardCondition::SwitchIntOtherwise {
                discr: Operand::Copy(place) | Operand::Move(place),
                excluded_values,
            } if excluded_values == &[1] || excluded_values == &[u128::from(true)] => {
                lhs_seen |= place.local == lhs_guard;
                rhs_seen |= place.local == rhs_guard;
            }
            _ => {}
        }
    }

    if lhs_seen && rhs_seen {
        Some(Formula::Or(vec![
            Formula::Var(v2_bool_local_name(func, lhs_guard), Sort::Bool),
            Formula::Var(v2_bool_local_name(func, rhs_guard), Sort::Bool),
        ]))
    } else {
        None
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_abs_guard_local_for_operand(func: &VerifiableFunction, operand: &Operand) -> Option<usize> {
    let target_local = match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };

    let mut abs_result_local = None;
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
        else {
            continue;
        };
        if !callee.contains("::abs") {
            continue;
        }
        if let Some(Operand::Copy(arg_place) | Operand::Move(arg_place)) = args.first()
            && arg_place.local == target_local
        {
            abs_result_local = Some(dest.local);
            break;
        }
    }
    let abs_result_local = abs_result_local?;

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            let Rvalue::BinaryOp(
                BinOp::Gt | BinOp::Ge,
                lhs,
                Operand::Constant(ConstValue::Float(_)),
            ) = rvalue
            else {
                continue;
            };
            if let Operand::Copy(place_lhs) | Operand::Move(place_lhs) = lhs
                && place_lhs.local == abs_result_local
            {
                return Some(place.local);
            }
        }
    }

    None
}

#[cfg(feature = "pipeline-v2")]
fn v2_bool_local_name(func: &VerifiableFunction, local: usize) -> String {
    func.body
        .locals
        .get(local)
        .and_then(|decl| decl.name.clone())
        .unwrap_or_else(|| format!("_{local}"))
}

#[cfg(feature = "pipeline-v2")]
fn v2_float_overflow_witness_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<Formula> {
    let width = match crate::operand_ty(func, lhs)? {
        Ty::Float { width } => width,
        _ => return None,
    };

    match (op, width) {
        (BinOp::Add, 64) => {
            let lhs_value = operand_to_formula(func, lhs);
            let rhs_value = operand_to_formula(func, rhs);
            let sign_width = 1;
            let mag_width = width - sign_width;
            let exp_width = 11;
            let frac_width = 52;
            let threshold = Formula::BitVec {
                value: ((f64::MAX / 2.0).to_bits() & ((1u64 << 63) - 1)) as i128,
                width: mag_width,
            };
            let finite_exponent = Formula::BitVec { value: 0x7ff, width: exp_width };

            Some(Formula::And(vec![
                Formula::Eq(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(lhs_value.clone()),
                        high: width - 1,
                        low: width - 1,
                    }),
                    Box::new(Formula::BvExtract {
                        inner: Box::new(rhs_value.clone()),
                        high: width - 1,
                        low: width - 1,
                    }),
                ),
                Formula::BvULt(
                    Box::new(threshold.clone()),
                    Box::new(v2_float_magnitude_bits(lhs_value.clone(), width)),
                    mag_width,
                ),
                Formula::BvULt(
                    Box::new(threshold),
                    Box::new(v2_float_magnitude_bits(rhs_value.clone(), width)),
                    mag_width,
                ),
                Formula::BvULt(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(lhs_value),
                        high: width - 2,
                        low: frac_width,
                    }),
                    Box::new(finite_exponent.clone()),
                    exp_width,
                ),
                Formula::BvULt(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(rhs_value),
                        high: width - 2,
                        low: frac_width,
                    }),
                    Box::new(finite_exponent),
                    exp_width,
                ),
            ]))
        }
        (BinOp::Mul, 64) => {
            let mag_width = width - 1;
            let threshold = Formula::BitVec {
                value: ((f64::MAX.sqrt()).to_bits() & ((1u64 << 63) - 1)) as i128,
                width: mag_width,
            };

            Some(Formula::And(vec![
                Formula::BvULt(
                    Box::new(threshold.clone()),
                    Box::new(v2_float_magnitude_bits(operand_to_formula(func, lhs), width)),
                    mag_width,
                ),
                Formula::BvULt(
                    Box::new(threshold),
                    Box::new(v2_float_magnitude_bits(operand_to_formula(func, rhs), width)),
                    mag_width,
                ),
            ]))
        }
        _ => None,
    }
}

#[cfg(feature = "pipeline-v2")]
fn v2_build_path_definition_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    use std::collections::VecDeque;

    const NOT_VISITED: u8 = 0;
    const VISITED_PRECISE: u8 = 1;
    const VISITED_WEAKENED: u8 = 2;

    let mut result: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let mut visited = vec![NOT_VISITED; func.body.blocks.len()];
    let mut queue: VecDeque<(BlockId, Vec<Formula>)> = VecDeque::from([(BlockId(0), Vec::new())]);

    while let Some((block_id, mut acc_defs)) = queue.pop_front() {
        if block_id.0 >= func.body.blocks.len() {
            continue;
        }

        match visited[block_id.0] {
            VISITED_WEAKENED => continue,
            VISITED_PRECISE => {
                let existing = result.get(&block_id).cloned().unwrap_or_default();
                if existing == acc_defs {
                    continue;
                }
                acc_defs = vec![Formula::Bool(true)];
                result.insert(block_id, acc_defs.clone());
                visited[block_id.0] = VISITED_WEAKENED;
            }
            NOT_VISITED => {
                result.insert(block_id, acc_defs.clone());
                visited[block_id.0] = VISITED_PRECISE;
            }
            _ => unreachable!(),
        }

        let block = &func.body.blocks[block_id.0];
        let mut next_defs = acc_defs;
        next_defs.extend(guards::extract_block_definitions(func, block));
        for guarded in block.terminator.discovered_clauses(block_id) {
            if let trust_types::ClauseTarget::Block(target) = guarded.target {
                queue.push_back((target, next_defs.clone()));
            }
        }
    }

    result
}

#[cfg(feature = "pipeline-v2")]
fn generate_v2_contract_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let guard_map: FxHashMap<BlockId, Vec<GuardCondition>> =
        func.body.path_map().into_iter().map(|entry| (entry.block, entry.guards)).collect();
    let path_definition_map = v2_build_path_definition_map(func);
    let semantic_guards = build_semantic_guard_map(func);
    let contract_metadata =
        if func.spec.is_empty() { None } else { Some(func.spec.to_contract_metadata()) };

    let mut vcs = Vec::new();

    for pre in &func.preconditions {
        vcs.push(VerificationCondition {
            kind: VcKind::Precondition { callee: func.name.clone() },
            function: func.name.as_str().into(),
            location: func.span.clone(),
            formula: Formula::Not(Box::new(pre.clone())),
            contract_metadata,
        });
    }

    if func.postconditions.is_empty() {
        return vcs;
    }

    for block in &func.body.blocks {
        if !matches!(block.terminator, Terminator::Return) {
            continue;
        }

        let predecessors: Vec<&trust_types::BasicBlock> = func
            .body
            .blocks
            .iter()
            .filter(|pred| v2_terminator_targets(&pred.terminator).contains(&block.id))
            .collect();
        let vc_blocks: Vec<&trust_types::BasicBlock> =
            if predecessors.len() > 1 { predecessors } else { vec![block] };

        for post in &func.postconditions {
            for vc_block in &vc_blocks {
                let mut formula = Formula::Not(Box::new(post.clone()));
                formula = v2_formula_with_block_defs(func, block, formula);
                if vc_block.id != block.id {
                    formula = v2_formula_with_block_defs(func, vc_block, formula);
                }

                if let Some(path_defs) = path_definition_map.get(&vc_block.id)
                    && !path_defs.is_empty()
                {
                    let mut conjuncts = path_defs.clone();
                    conjuncts.push(formula);
                    formula = Formula::And(conjuncts);
                }

                if let Some(block_guards) = guard_map.get(&vc_block.id)
                    && !block_guards.is_empty()
                {
                    formula = guards::guarded_formula(func, block_guards, formula);
                }

                if let Some(sem_guards) = semantic_guards.get(&vc_block.id)
                    && !sem_guards.is_empty()
                {
                    let mut conjuncts = sem_guards.clone();
                    conjuncts.push(formula);
                    formula = Formula::And(conjuncts);
                }

                if !func.preconditions.is_empty() {
                    let mut conjuncts = func.preconditions.clone();
                    conjuncts.push(formula);
                    formula = Formula::And(conjuncts);
                }

                vcs.push(VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: func.name.as_str().into(),
                    location: v2_block_span(func, vc_block),
                    formula,
                    contract_metadata,
                });
            }
        }
    }

    vcs
}
