// trust-vcgen/generate.rs: Core verification condition generation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

#[cfg(not(feature = "pipeline-v2"))]
use rayon::prelude::*;

use trust_types::{
    Formula,
    Terminator, VerifiableFunction, VerificationCondition, VerificationResult,
};

use crate::abstract_interp::{self, IntervalDomain, AbstractDomain};
// tRust #792/#797: v1 VC checker modules. Only negation and rvalue_safety remain;
// overflow, divzero, shifts, casts, float_ops, asserts, bounds deleted (migrated to zani-lib).
use crate::{
    contracts, resilience, resilience_analysis,
    sep_engine, spec_parser, termination, unsafe_verify,
    ffi_summary, ffi_vcgen, memory_ordering,
    operand_to_formula, place_to_var_name,
};

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
// tRust #792: Gated behind pipeline-v2 — guard extraction is v1-only.
#[cfg(not(feature = "pipeline-v2"))]
pub(crate) fn build_semantic_guard_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
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
            Terminator::Call { target, .. } => {
                if let Some(target) = target {
                    queue.push_back((*target, next_guards));
                }
            }
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
        let block_vcs: Vec<VerificationCondition> = func.body.blocks.par_iter().flat_map(|block| {
            let mut block_vcs = Vec::new();

            // tRust #792/#797: v1 VC checker calls — overflow, divzero, shifts, casts,
            // float_ops, asserts, bounds all deleted (migrated to zani-lib).
            // Only negation and rvalue_safety remain in trust-vcgen.
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, span } = stmt {
                    negation::check_negation_overflow(func, block, rvalue, span, &mut block_vcs);
                    let dest_ty = rvalue_safety::place_ty(func, place);
                    rvalue_safety::check_rvalue_safety(
                        func, block, rvalue, dest_ty.as_ref(), span, &mut block_vcs,
                    );
                }
            }

            // tRust #21: Wrap newly-generated VCs with path guard assumptions.
            if let Some(block_guards) = guard_map.get(&block.id)
                && !block_guards.is_empty() {
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
        }).collect();

        block_vcs
    };

    // tRust #792: Pipeline v2 path — VCs generated by zani-lib/sunder-lib at MIR level.
    // This stub returns an empty Vec; actual dispatch happens in trust-router::mir_router.
    #[cfg(feature = "pipeline-v2")]
    let mut vcs: Vec<VerificationCondition> = Vec::new();

    // tRust #712: Deterministic ordering after parallel generation.
    vcs.sort_by(|a, b| {
        a.location.file.cmp(&b.location.file)
            .then(a.location.line_start.cmp(&b.location.line_start))
            .then(a.location.col_start.cmp(&b.location.col_start))
    });

    contracts::check_contracts(func, &mut vcs);
    // tRust #119: Generate VCs from FunctionSpec (#[requires], #[ensures], #[invariant]).
    vcs.extend(spec_parser::generate_spec_vcs(func));
    // tRust #792: unreachable checking gated behind pipeline-v2.
    #[cfg(not(feature = "pipeline-v2"))]
    unreachable::check_unreachable(func, &mut vcs);

    // tRust #53: Check external dependency resilience.
    let failure_model = resilience_analysis::extract_failure_model(func);
    if !failure_model.is_empty() {
        resilience::check_resilience(func, &failure_model, &mut vcs);
    }

    // tRust #66: Termination checking via decreases clauses.
    termination::check_termination(func, &mut vcs);

    // tRust #79: Unsafe code verification with SAFETY comment extraction.
    // In the full compiler integration, comments come from the source map.
    // At the vcgen level, callers pass comments via check_unsafe() directly.
    // Here we run detection only (no comments available at this layer).
    unsafe_verify::check_unsafe(func, &[], &mut vcs);

    // tRust #436: Separation logic provenance engine — heap-aware VCs for
    // unsafe patterns (raw deref, alloc, dealloc, ptr::copy, transmute, etc.).
    vcs.extend(sep_engine::check_sep_unsafe(func));

    // tRust #460: FFI boundary verification with summary-based VCs.
    // Detect Call terminators targeting extern/FFI functions and generate
    // targeted VCs (null checks, range checks, aliasing, return contracts)
    // instead of conservative Bool(true) from unsafe_verify.
    let ffi_db = ffi_summary::FfiSummaryDb::new();
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, span, .. } = &block.terminator
            && ffi_vcgen::is_extern_call(callee, &ffi_db) {
                let arg_formulas: Vec<Formula> = args.iter()
                    .map(|op| operand_to_formula(func, op))
                    .collect();
                let dest_var = place_to_var_name(func, dest);
                vcs.extend(ffi_vcgen::generate_call_site_vcs(
                    &func.name, callee, &arg_formulas, &dest_var, span, &ffi_db,
                ));
            }
    }

    // tRust #609: Atomic ordering legality VCs.
    // Collect atomic operations from Call terminators and check C++ standard
    // legality rules (L1-L5) via MemoryModelChecker::check_operation_legality.
    {
        let atomic_ops: Vec<_> = func.body.blocks.iter()
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
