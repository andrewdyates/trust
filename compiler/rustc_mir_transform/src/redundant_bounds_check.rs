// tRust: MIR pass to eliminate redundant array bounds checks (#867)
// tRust: rust-lang#127553: "Missed bounds check elimination"
//
// tRust: When code performs a bounds check (e.g., `assert!(i < arr.len())`) and
// tRust: then indexes `arr[i]`, the compiler generates two BoundsCheck asserts.
// tRust: If the first dominates the second and checks the same index against the
// tRust: same length, the second is redundant.
//
// tRust: This pass uses two complementary strategies:
// tRust: 1. Condition-based: If two Assert terminators share the same condition
// tRust:    local and expected value, and the first dominates the second, the
// tRust:    second is redundant.
// tRust: 2. BoundsCheck-specific: If two BoundsCheck asserts reference the same
// tRust:    index and length locals, the dominated one is redundant.
//
// tRust: Strategy 1 benefits from running after GVN, which merges identical
// tRust: computations into the same SSA local.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_data_structures::graph::dominators::Dominators;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use tracing::{debug, trace};

pub(super) struct RedundantBoundsCheckElim;

impl<'tcx> crate::MirPass<'tcx> for RedundantBoundsCheckElim {
    fn name(&self) -> &'static str {
        "RedundantBoundsCheckElim"
    }

    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() >= 2
    }

    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let dominators = body.basic_blocks.dominators().clone();

        // tRust: Phase 1 — Collect all Assert(cond, true, ...) terminators.
        // We record (block, cond_local, expected) for condition-based dedup,
        // and (block, index_local, len_local) for BoundsCheck-specific dedup.
        let mut assert_cond_blocks: Vec<(BasicBlock, Local, bool)> = Vec::new();
        let mut bounds_check_blocks: Vec<(BasicBlock, Local, Local)> = Vec::new();

        for (bb, block) in body.basic_blocks.iter_enumerated() {
            let terminator = block.terminator();
            if let TerminatorKind::Assert { ref cond, expected, ref msg, .. } = terminator.kind {
                if let Some(cond_local) = operand_as_local(cond) {
                    assert_cond_blocks.push((bb, cond_local, expected));
                }
                if expected {
                    if let box AssertKind::BoundsCheck { ref len, ref index } = *msg {
                        if let (Some(idx), Some(ln)) =
                            (operand_as_local(index), operand_as_local(len))
                        {
                            bounds_check_blocks.push((bb, idx, ln));
                        }
                    }
                }
            }
        }

        // tRust: Phase 2 — Eliminate redundant asserts.
        let mut eliminated = 0u32;
        let blocks = body.basic_blocks.as_mut();
        for bb_idx in 0..blocks.len() {
            let bb = BasicBlock::from_usize(bb_idx);
            let terminator = &blocks[bb].terminator();
            let TerminatorKind::Assert { ref cond, expected, ref msg, target, .. } =
                terminator.kind
            else {
                continue;
            };

            let cond_local = match operand_as_local(cond) {
                Some(l) => l,
                None => continue,
            };

            // tRust: Strategy 1 — Same condition local, same expected value,
            // dominating block. Works for any Assert, not just BoundsCheck.
            let redundant_by_cond = assert_cond_blocks.iter().any(|(dom_bb, dom_cond, dom_exp)| {
                *dom_bb != bb
                    && *dom_cond == cond_local
                    && *dom_exp == expected
                    && dominators.dominates(*dom_bb, bb)
            });

            // tRust: Strategy 2 — BoundsCheck-specific: same index and length locals.
            let redundant_by_bounds = if expected {
                if let box AssertKind::BoundsCheck { ref len, ref index } = *msg {
                    if let (Some(idx), Some(ln)) = (operand_as_local(index), operand_as_local(len))
                    {
                        bounds_check_blocks.iter().any(|(dom_bb, dom_idx, dom_len)| {
                            *dom_bb != bb
                                && *dom_idx == idx
                                && *dom_len == ln
                                && dominators.dominates(*dom_bb, bb)
                        })
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            };

            if redundant_by_cond || redundant_by_bounds {
                let strategy = if redundant_by_cond { "condition" } else { "bounds-check" };
                trace!(
                    "tRust: eliminating redundant assert in {:?} via {} strategy \
                     (cond={:?})",
                    bb,
                    strategy,
                    cond_local
                );
                blocks[bb].terminator_mut().kind = TerminatorKind::Goto { target };
                eliminated += 1;
            }
        }

        if eliminated > 0 {
            debug!(
                "tRust: RedundantBoundsCheckElim eliminated {} redundant check(s) in {:?}",
                eliminated,
                body.source.def_id()
            );
        }
    }

    fn is_required(&self) -> bool {
        false
    }
}

/// tRust: Extract the Local from an Operand if it's a Copy or Move of a simple local.
fn operand_as_local(op: &Operand<'_>) -> Option<Local> {
    match op {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}
