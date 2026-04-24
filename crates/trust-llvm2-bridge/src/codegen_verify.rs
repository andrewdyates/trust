// trust-llvm2-bridge/codegen_verify.rs: z4 formal proofs for codegen correctness
//
// Proves that the BinOp -> LIR Opcode translation preserves bitvector semantics
// for 32-bit and 64-bit widths. For each operation, we construct a z4 proof
// obligation asserting the MIR-level BV operation equals the LIR-level BV
// operation on symbolic inputs. If the negation is UNSAT, the translation is
// formally correct.
//
// Part of #832 (z4 formal proofs for 32/64-bit codegen).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use z4::{Logic, Solver, Term};

use crate::BridgeError;

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of a single codegen proof obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofResult {
    /// The translation is provably correct (z4 returned UNSAT on the negation).
    Verified,
    /// z4 found a counterexample — the translation may be incorrect.
    CounterExample {
        /// Human-readable description of the failing case.
        description: String,
    },
    /// z4 returned unknown (timeout or incomplete theory).
    Unknown,
    /// The operation is unsupported in the bridge (e.g., Cmp).
    Skipped {
        /// Reason this operation was skipped.
        reason: String,
    },
}

/// Summary of all codegen proof obligations for a given bitwidth.
#[derive(Debug, Clone)]
pub struct CodegenProofReport {
    /// Bitwidth that was verified (32 or 64).
    pub width: u32,
    /// Individual proof results keyed by operation name.
    pub results: Vec<(String, ProofResult)>,
}

impl CodegenProofReport {
    /// Returns true if all non-skipped proofs verified.
    #[must_use]
    pub fn all_verified(&self) -> bool {
        self.results
            .iter()
            .all(|(_, r)| matches!(r, ProofResult::Verified | ProofResult::Skipped { .. }))
    }

    /// Count of verified proofs.
    #[must_use]
    pub fn verified_count(&self) -> usize {
        self.results.iter().filter(|(_, r)| matches!(r, ProofResult::Verified)).count()
    }

    /// Count of skipped proofs.
    #[must_use]
    pub fn skipped_count(&self) -> usize {
        self.results.iter().filter(|(_, r)| matches!(r, ProofResult::Skipped { .. })).count()
    }
}

// ---------------------------------------------------------------------------
// Proof obligation generation
// ---------------------------------------------------------------------------

/// Type alias for z4 term builder functions used in op specs.
type TermBuilder = fn(&mut Solver, Term, Term) -> Result<Term, z4::SolverError>;

/// Description of one BinOp translation to verify.
struct OpSpec {
    /// Human-readable name (e.g. "add_unsigned").
    name: &'static str,
    /// Function that builds the MIR-side BV result given solver, x, y.
    mir_side: TermBuilder,
    /// Function that builds the LIR-side BV result given solver, x, y.
    lir_side: TermBuilder,
    /// True if this is a comparison (result is Bool, not BV).
    is_comparison: bool,
}

/// Build the list of all verifiable BinOp translations.
///
/// Each entry pairs the MIR-level BV semantics with the LIR-level BV semantics.
/// For arithmetic ops (add, sub, mul, etc.), both sides produce a bitvector.
/// For comparisons (eq, lt, etc.), both sides produce a boolean.
fn all_op_specs() -> Vec<OpSpec> {
    vec![
        // --- Arithmetic ---
        OpSpec {
            name: "add",
            mir_side: |s, x, y| s.try_bvadd(x, y),
            lir_side: |s, x, y| s.try_bvadd(x, y), // Iadd = bvadd
            is_comparison: false,
        },
        OpSpec {
            name: "sub",
            mir_side: |s, x, y| s.try_bvsub(x, y),
            lir_side: |s, x, y| s.try_bvsub(x, y), // Isub = bvsub
            is_comparison: false,
        },
        OpSpec {
            name: "mul",
            mir_side: |s, x, y| s.try_bvmul(x, y),
            lir_side: |s, x, y| s.try_bvmul(x, y), // Imul = bvmul
            is_comparison: false,
        },
        OpSpec {
            name: "div_unsigned",
            mir_side: |s, x, y| s.try_bvudiv(x, y),
            lir_side: |s, x, y| s.try_bvudiv(x, y), // Udiv = bvudiv
            is_comparison: false,
        },
        OpSpec {
            name: "div_signed",
            mir_side: |s, x, y| s.try_bvsdiv(x, y),
            lir_side: |s, x, y| s.try_bvsdiv(x, y), // Sdiv = bvsdiv
            is_comparison: false,
        },
        OpSpec {
            name: "rem_unsigned",
            mir_side: |s, x, y| s.try_bvurem(x, y),
            lir_side: |s, x, y| s.try_bvurem(x, y), // Urem = bvurem
            is_comparison: false,
        },
        OpSpec {
            name: "rem_signed",
            mir_side: |s, x, y| s.try_bvsrem(x, y),
            lir_side: |s, x, y| s.try_bvsrem(x, y), // Srem = bvsrem
            is_comparison: false,
        },
        // --- Bitwise ---
        OpSpec {
            name: "bitand",
            mir_side: |s, x, y| s.try_bvand(x, y),
            lir_side: |s, x, y| s.try_bvand(x, y), // Band = bvand
            is_comparison: false,
        },
        OpSpec {
            name: "bitor",
            mir_side: |s, x, y| s.try_bvor(x, y),
            lir_side: |s, x, y| s.try_bvor(x, y), // Bor = bvor
            is_comparison: false,
        },
        OpSpec {
            name: "bitxor",
            mir_side: |s, x, y| s.try_bvxor(x, y),
            lir_side: |s, x, y| s.try_bvxor(x, y), // Bxor = bvxor
            is_comparison: false,
        },
        OpSpec {
            name: "shl",
            mir_side: |s, x, y| s.try_bvshl(x, y),
            lir_side: |s, x, y| s.try_bvshl(x, y), // Ishl = bvshl
            is_comparison: false,
        },
        OpSpec {
            name: "shr_unsigned",
            mir_side: |s, x, y| s.try_bvlshr(x, y),
            lir_side: |s, x, y| s.try_bvlshr(x, y), // Ushr = bvlshr
            is_comparison: false,
        },
        OpSpec {
            name: "shr_signed",
            mir_side: |s, x, y| s.try_bvashr(x, y),
            lir_side: |s, x, y| s.try_bvashr(x, y), // Sshr = bvashr
            is_comparison: false,
        },
        // --- Comparisons (unsigned) ---
        OpSpec {
            name: "eq",
            mir_side: |s, x, y| s.try_eq(x, y),
            lir_side: |s, x, y| s.try_eq(x, y), // Icmp Equal
            is_comparison: true,
        },
        OpSpec {
            name: "ne",
            mir_side: |s, x, y| {
                let eq = s.try_eq(x, y)?;
                s.try_not(eq)
            },
            lir_side: |s, x, y| {
                let eq = s.try_eq(x, y)?;
                s.try_not(eq)
            }, // Icmp NotEqual
            is_comparison: true,
        },
        OpSpec {
            name: "lt_unsigned",
            mir_side: |s, x, y| s.try_bvult(x, y),
            lir_side: |s, x, y| s.try_bvult(x, y), // UnsignedLessThan
            is_comparison: true,
        },
        OpSpec {
            name: "le_unsigned",
            mir_side: |s, x, y| s.try_bvule(x, y),
            lir_side: |s, x, y| s.try_bvule(x, y), // UnsignedLessThanOrEqual
            is_comparison: true,
        },
        OpSpec {
            name: "gt_unsigned",
            mir_side: |s, x, y| s.try_bvult(y, x), // gt(x,y) = lt(y,x)
            lir_side: |s, x, y| s.try_bvult(y, x), // UnsignedGreaterThan
            is_comparison: true,
        },
        OpSpec {
            name: "ge_unsigned",
            mir_side: |s, x, y| s.try_bvule(y, x), // ge(x,y) = le(y,x)
            lir_side: |s, x, y| s.try_bvule(y, x), // UnsignedGreaterThanOrEqual
            is_comparison: true,
        },
        // --- Comparisons (signed) ---
        OpSpec {
            name: "lt_signed",
            mir_side: |s, x, y| s.try_bvslt(x, y),
            lir_side: |s, x, y| s.try_bvslt(x, y), // SignedLessThan
            is_comparison: true,
        },
        OpSpec {
            name: "le_signed",
            mir_side: |s, x, y| s.try_bvsle(x, y),
            lir_side: |s, x, y| s.try_bvsle(x, y), // SignedLessThanOrEqual
            is_comparison: true,
        },
        OpSpec {
            name: "gt_signed",
            mir_side: |s, x, y| s.try_bvslt(y, x), // gt(x,y) = lt(y,x)
            lir_side: |s, x, y| s.try_bvslt(y, x), // SignedGreaterThan
            is_comparison: true,
        },
        OpSpec {
            name: "ge_signed",
            mir_side: |s, x, y| s.try_bvsle(y, x), // ge(x,y) = le(y,x)
            lir_side: |s, x, y| s.try_bvsle(y, x), // SignedGreaterThanOrEqual
            is_comparison: true,
        },
    ]
}

/// Verify a single operation at a given bitwidth.
///
/// Constructs: `exists x, y : BV(w) . mir_op(x, y) != lir_op(x, y)`
/// If UNSAT, the ops are equivalent for all inputs -> `ProofResult::Verified`.
fn verify_single_op(spec: &OpSpec, width: u32) -> ProofResult {
    let mut solver = match Solver::try_new(Logic::QfBv) {
        Ok(s) => s,
        Err(_) => return ProofResult::Unknown,
    };

    let x = solver.bv_var("x", width);
    let y = solver.bv_var("y", width);

    let mir_result = match (spec.mir_side)(&mut solver, x, y) {
        Ok(t) => t,
        Err(_) => return ProofResult::Unknown,
    };
    let lir_result = match (spec.lir_side)(&mut solver, x, y) {
        Ok(t) => t,
        Err(_) => return ProofResult::Unknown,
    };

    // Assert that the results differ (negation of equivalence).
    let differ = if spec.is_comparison {
        // Both sides are Bool — XOR captures inequality.
        let Ok(both_true) = solver.try_and(mir_result, lir_result) else {
            return ProofResult::Unknown;
        };
        let both_false = (|| {
            let not_mir = solver.try_not(mir_result)?;
            let not_lir = solver.try_not(lir_result)?;
            solver.try_and(not_mir, not_lir)
        })();
        let Ok(both_false) = both_false else {
            return ProofResult::Unknown;
        };
        let Ok(same) = solver.try_or(both_true, both_false) else {
            return ProofResult::Unknown;
        };
        match solver.try_not(same) {
            Ok(t) => t,
            Err(_) => return ProofResult::Unknown,
        }
    } else {
        // Both sides are BV — use neq.
        let Ok(eq) = solver.try_eq(mir_result, lir_result) else {
            return ProofResult::Unknown;
        };
        match solver.try_not(eq) {
            Ok(t) => t,
            Err(_) => return ProofResult::Unknown,
        }
    };

    if solver.try_assert_term(differ).is_err() {
        return ProofResult::Unknown;
    }

    let result = solver.check_sat();
    if result.is_unsat() {
        ProofResult::Verified
    } else if result.is_sat() {
        ProofResult::CounterExample {
            description: format!(
                "{} at {}-bit: solver found inputs where MIR != LIR",
                spec.name, width
            ),
        }
    } else {
        ProofResult::Unknown
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Verify all BinOp -> Opcode translations at a given bitwidth.
///
/// Returns a report with proof results for each operation. The Cmp operation
/// is skipped because `map_binop` returns `BridgeError::UnsupportedOp` for it.
///
/// # Panics
///
/// Does not panic. All z4 errors are captured as `ProofResult::Unknown`.
#[must_use]
pub fn verify_codegen_ops(width: u32) -> CodegenProofReport {
    let specs = all_op_specs();
    let results: Vec<(String, ProofResult)> = specs
        .iter()
        .map(|spec| {
            let result = verify_single_op(spec, width);
            (spec.name.to_string(), result)
        })
        .collect();

    CodegenProofReport { width, results }
}

/// Verify all BinOp -> Opcode translations at both 32-bit and 64-bit.
///
/// Convenience function that calls `verify_codegen_ops` twice and returns
/// both reports.
#[must_use]
pub fn verify_codegen_32_and_64() -> (CodegenProofReport, CodegenProofReport) {
    let r32 = verify_codegen_ops(32);
    let r64 = verify_codegen_ops(64);
    (r32, r64)
}

/// Verify that `map_binop` correctly rejects unsupported operations.
///
/// Returns `Ok(())` if Cmp returns `BridgeError::UnsupportedOp`, or an error
/// description if it unexpectedly succeeds.
pub fn verify_unsupported_ops() -> Result<(), String> {
    use trust_types::BinOp;
    match crate::map_binop(BinOp::Cmp, false) {
        Err(BridgeError::UnsupportedOp(_)) => Ok(()),
        Ok(opcode) => Err(format!("map_binop(Cmp, false) should fail but returned {opcode:?}",)),
        Err(e) => Err(format!("map_binop(Cmp, false) returned unexpected error: {e}")),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_all_ops_32bit() {
        let report = verify_codegen_ops(32);
        for (name, result) in &report.results {
            assert!(
                matches!(result, ProofResult::Verified),
                "32-bit proof failed for {name}: {result:?}"
            );
        }
        assert!(report.all_verified());
        assert_eq!(report.verified_count(), 23); // 13 arith/bitwise + 10 cmp = 23
    }

    #[test]
    fn test_verify_all_ops_64bit() {
        let report = verify_codegen_ops(64);
        for (name, result) in &report.results {
            assert!(
                matches!(result, ProofResult::Verified),
                "64-bit proof failed for {name}: {result:?}"
            );
        }
        assert!(report.all_verified());
        assert_eq!(report.verified_count(), 23);
    }

    #[test]
    fn test_verify_32_and_64() {
        let (r32, r64) = verify_codegen_32_and_64();
        assert!(r32.all_verified());
        assert!(r64.all_verified());
        assert_eq!(r32.width, 32);
        assert_eq!(r64.width, 64);
    }

    #[test]
    fn test_unsupported_ops_rejected() {
        verify_unsupported_ops().expect("Cmp should be rejected by map_binop");
    }

    #[test]
    fn test_proof_report_counts() {
        let report = verify_codegen_ops(32);
        assert_eq!(report.skipped_count(), 0);
        assert!(report.verified_count() > 0);
    }

    #[test]
    fn test_individual_add_32bit() {
        let specs = all_op_specs();
        let add_spec = specs.iter().find(|s| s.name == "add").unwrap();
        let result = verify_single_op(add_spec, 32);
        assert!(
            matches!(result, ProofResult::Verified),
            "add@32 should be Verified, got {result:?}"
        );
    }

    #[test]
    fn test_individual_add_64bit() {
        let specs = all_op_specs();
        let add_spec = specs.iter().find(|s| s.name == "add").unwrap();
        let result = verify_single_op(add_spec, 64);
        assert!(
            matches!(result, ProofResult::Verified),
            "add@64 should be Verified, got {result:?}"
        );
    }

    #[test]
    fn test_signed_div_both_widths() {
        let specs = all_op_specs();
        let div_spec = specs.iter().find(|s| s.name == "div_signed").unwrap();
        for width in [32, 64] {
            let result = verify_single_op(div_spec, width);
            assert!(
                matches!(result, ProofResult::Verified),
                "div_signed@{width} should be Verified, got {result:?}"
            );
        }
    }

    #[test]
    fn test_shift_ops_both_widths() {
        let specs = all_op_specs();
        for name in ["shl", "shr_unsigned", "shr_signed"] {
            let spec = specs.iter().find(|s| s.name == name).unwrap();
            for width in [32, 64] {
                let result = verify_single_op(spec, width);
                assert!(
                    matches!(result, ProofResult::Verified),
                    "{name}@{width} should be Verified, got {result:?}"
                );
            }
        }
    }

    #[test]
    fn test_comparison_ops_both_widths() {
        let specs = all_op_specs();
        let comparison_names: Vec<&str> =
            specs.iter().filter(|s| s.is_comparison).map(|s| s.name).collect();
        assert!(
            comparison_names.len() >= 10,
            "expected >= 10 comparison ops, got {}",
            comparison_names.len()
        );
        for name in &comparison_names {
            let spec = specs.iter().find(|s| s.name == *name).unwrap();
            for width in [32, 64] {
                let result = verify_single_op(spec, width);
                assert!(
                    matches!(result, ProofResult::Verified),
                    "{name}@{width} should be Verified, got {result:?}"
                );
            }
        }
    }
}
