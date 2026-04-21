// trust-type-recover: return type inference from register analysis
//
// Infers function return types by analyzing how the caller uses the return
// register (RAX/X0 for integers, XMM0/D0 for floats) after a call instruction.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::TypeRecoveryError;
use crate::evidence::{EvidenceSource, TypeEvidence};
use crate::strategy::{RecoveryContext, TypeRecoveryStrategy};
use crate::types::RecoveredType;
use trust_types::Ty;

/// How the return register is used after a function call.
///
/// Each variant represents a distinct usage pattern observed in the caller's
/// code following the call instruction. Multiple uses can be observed for a
/// single call site.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ReturnRegisterUse {
    /// Return value participates in address calculations (e.g., `ADD Xn, X0, #offset`).
    /// Strongly suggests the function returns a pointer.
    PointerArithmetic {
        /// The constant offset added to the return value, if known.
        offset: i64,
    },

    /// Return value is compared against zero or null (e.g., `CBZ X0, ...` or `TEST RAX, RAX`).
    /// Suggests the function returns a pointer, Option, or Result.
    NullCheck,

    /// Return value is sign-extended from a narrower width (e.g., `SXTW` on AArch64,
    /// `MOVSXD` on x86-64). Indicates the function returns a smaller signed integer.
    SignExtend {
        /// Original width in bits before extension.
        from_bits: u32,
        /// Target width in bits after extension.
        to_bits: u32,
    },

    /// Return value is zero-extended from a narrower width (e.g., `UXTB` on AArch64,
    /// `MOVZX` on x86-64). Indicates the function returns a smaller unsigned integer.
    ZeroExtend {
        /// Original width in bits before extension.
        from_bits: u32,
        /// Target width in bits after extension.
        to_bits: u32,
    },

    /// Return value is moved to a floating-point register or used in FP operations
    /// (e.g., `FMOV D0, X0` or `MOVSD XMM0, ...`). Indicates a float return type.
    FloatUse,

    /// Return register is never read after the call. Suggests the function
    /// returns `()` or the caller discards the return value.
    Ignored,

    /// Return value is used in integer arithmetic (add, sub, mul, bitwise ops)
    /// without pointer-like patterns. Suggests a general integer return type.
    IntegerArithmetic,
}

/// Target architecture for calling convention analysis.
///
/// Determines which registers are used for return values:
/// - AArch64: X0 (integer), D0 (float)
/// - x86-64: RAX (integer), XMM0 (float)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CallingConvArch {
    /// AArch64 (ARM64) calling convention. Return register: X0/D0.
    Aarch64,
    /// x86-64 (AMD64) System V / Windows calling convention. Return register: RAX/XMM0.
    X86_64,
}

/// An observation of how a function's return register is used at a call site.
///
/// Constructed by the disassembler/lifter when it detects a call instruction
/// and analyzes the subsequent instructions that consume the return register.
#[derive(Debug, Clone)]
pub struct ReturnTypeObservation {
    /// Address of the call instruction.
    pub call_addr: u64,
    /// Name of the called function, if resolved from symbols.
    pub callee_name: Option<String>,
    /// Architecture, for determining which register is the return register.
    pub arch: CallingConvArch,
    /// Observed uses of the return register after the call.
    pub uses: Vec<ReturnRegisterUse>,
}

/// The state of the return register at a function exit point.
///
/// Constructed by the disassembler/lifter by analyzing the instructions
/// leading to a `RET` and summarizing what value is left in the architectural
/// return register (X0 on AArch64, RAX on x86-64).
#[derive(Debug, Clone)]
pub struct ExitRegisterState {
    /// Address of the `RET` instruction.
    pub exit_addr: u64,
    /// Whether the return register was written in the function body before exit.
    pub register_written: bool,
    /// Width in bits of the last write to the return register, if known.
    pub last_write_width: Option<u32>,
    /// Whether a boolean-producing pattern was detected (e.g., `CMP` + `CSET`).
    pub is_boolean_pattern: bool,
    /// Whether the return register is known to hold constant zero at exit.
    pub is_constant_zero: bool,
    /// Whether the return register is known to hold constant one at exit.
    pub is_constant_one: bool,
}

/// Callee-side observations about a function's return register state.
///
/// Each observation summarizes the state of the architectural return register
/// across all exits (`RET` instructions) in a single function.
#[derive(Debug, Clone)]
pub struct CalleeReturnObservation {
    /// Start address of the function.
    pub function_addr: u64,
    /// Name of the function, if resolved from symbols.
    pub function_name: Option<String>,
    /// Architecture, for determining which register is the return register.
    pub arch: CallingConvArch,
    /// Summary of the return register state for each exit point.
    pub exit_states: Vec<ExitRegisterState>,
}

/// Infers function return types by analyzing post-call register usage patterns.
///
/// This strategy examines how the caller uses the return register (RAX on
/// x86-64, X0 on AArch64) after each call instruction. The usage pattern
/// reveals the return type with moderate to high confidence:
///
/// | Pattern | Inferred Type | Confidence |
/// |---------|--------------|------------|
/// | Pointer arithmetic | `*mut T` | 0.75 |
/// | Null check | `*mut T` (nullable) | 0.60 |
/// | Sign-extend | `iN` (signed int) | 0.70 |
/// | Zero-extend | `uN` (unsigned int) | 0.70 |
/// | Float use | `f64` | 0.80 |
/// | Ignored | `()` | 0.50 |
/// | Integer arithmetic | `u64` | 0.55 |
/// | Null check + pointer arith | `*mut T` | 0.85 |
#[derive(Debug, Default)]
pub struct ReturnTypeStrategy;

impl TypeRecoveryStrategy for ReturnTypeStrategy {
    fn name(&self) -> &str {
        "return_type"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        for obs in &ctx.return_register_observations {
            if obs.uses.is_empty() {
                continue;
            }

            let (recovered_type, confidence) = infer_from_uses(&obs.uses);

            evidence.push(TypeEvidence::new(
                recovered_type,
                confidence,
                EvidenceSource::ReturnRegisterAnalysis {
                    call_addr: obs.call_addr,
                    callee_name: obs.callee_name.clone(),
                },
            ));
        }

        Ok(evidence)
    }
}

/// Infers function return types by analyzing callee exit register state.
///
/// This strategy examines what the callee leaves in the architectural return
/// register (RAX on x86-64, X0 on AArch64) at each function exit. Agreement
/// across exits yields higher-confidence evidence than mixed-width or
/// ambiguous exit states.
#[derive(Debug, Clone, Default)]
pub struct CalleeReturnTypeStrategy;

impl TypeRecoveryStrategy for CalleeReturnTypeStrategy {
    fn name(&self) -> &str {
        "callee_return_type"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        for obs in &ctx.callee_return_observations {
            let Some((recovered_type, confidence)) = infer_from_exit_states(&obs.exit_states)
            else {
                continue;
            };

            evidence.push(TypeEvidence::new(
                recovered_type,
                confidence,
                EvidenceSource::CalleeReturnAnalysis {
                    function_addr: obs.function_addr,
                    function_name: obs.function_name.clone(),
                    exit_count: obs.exit_states.len(),
                },
            ));
        }

        Ok(evidence)
    }
}

/// Infer a return type and confidence from observed register uses.
///
/// When multiple uses are present, they are combined to produce a
/// higher-confidence result. For example, both NullCheck and
/// PointerArithmetic strongly suggest a pointer return type.
fn infer_from_uses(uses: &[ReturnRegisterUse]) -> (RecoveredType, f64) {
    let has_ptr_arith =
        uses.iter().any(|u| matches!(u, ReturnRegisterUse::PointerArithmetic { .. }));
    let has_null_check = uses.iter().any(|u| matches!(u, ReturnRegisterUse::NullCheck));
    let has_float = uses.iter().any(|u| matches!(u, ReturnRegisterUse::FloatUse));

    // Combined evidence: pointer arithmetic + null check → strong pointer evidence
    if has_ptr_arith && has_null_check {
        return (opaque_mut_ptr(), 0.85);
    }

    // Single-use inference: pick the highest-confidence applicable pattern
    if has_ptr_arith {
        return (opaque_mut_ptr(), 0.75);
    }

    if has_float {
        return (RecoveredType::Primitive(Ty::Float { width: 64 }), 0.80);
    }

    // Check for sign/zero extension (use the first one found)
    for u in uses {
        match u {
            ReturnRegisterUse::SignExtend { from_bits, .. } => {
                return (
                    RecoveredType::Primitive(Ty::Int { width: *from_bits, signed: true }),
                    0.70,
                );
            }
            ReturnRegisterUse::ZeroExtend { from_bits, .. } => {
                return (
                    RecoveredType::Primitive(Ty::Int { width: *from_bits, signed: false }),
                    0.70,
                );
            }
            _ => {}
        }
    }

    if has_null_check {
        return (opaque_mut_ptr(), 0.60);
    }

    // Check for integer arithmetic
    let has_int_arith = uses.iter().any(|u| matches!(u, ReturnRegisterUse::IntegerArithmetic));
    if has_int_arith {
        return (RecoveredType::Primitive(Ty::Int { width: 64, signed: false }), 0.55);
    }

    // Ignored: return value unused
    let has_ignored = uses.iter().any(|u| matches!(u, ReturnRegisterUse::Ignored));
    if has_ignored {
        return (RecoveredType::Primitive(Ty::Unit), 0.50);
    }

    // Fallback: unknown usage pattern
    (RecoveredType::Opaque { size: 8 }, 0.3)
}

/// Infer a return type and confidence from callee exit register states.
fn infer_from_exit_states(exit_states: &[ExitRegisterState]) -> Option<(RecoveredType, f64)> {
    if exit_states.is_empty() {
        return None;
    }

    if exit_states.iter().all(|state| !state.register_written) {
        return Some((RecoveredType::Primitive(Ty::Unit), 0.80));
    }

    if exit_states.iter().all(|state| state.is_boolean_pattern) {
        return Some((RecoveredType::Primitive(Ty::Bool), 0.85));
    }

    if exit_states.iter().all(|state| state.is_constant_zero || state.is_constant_one) {
        return Some((RecoveredType::Primitive(Ty::Bool), 0.70));
    }

    let widths: Vec<u32> = exit_states.iter().filter_map(|state| state.last_write_width).collect();

    if widths.is_empty() {
        return None;
    }

    let first_width = widths[0];
    if widths.len() == exit_states.len() && widths.iter().all(|width| *width == first_width) {
        return Some((unsigned_int(first_width), 0.65));
    }

    let widest_width = widths.into_iter().max().expect("checked non-empty");
    Some((unsigned_int(widest_width), 0.45))
}

/// Construct a mutable pointer to an opaque (unknown) pointee.
fn opaque_mut_ptr() -> RecoveredType {
    RecoveredType::Pointer { mutable: true, pointee: Box::new(RecoveredType::Opaque { size: 0 }) }
}

/// Construct an unsigned integer primitive of the given width.
fn unsigned_int(width: u32) -> RecoveredType {
    RecoveredType::Primitive(Ty::Int { width, signed: false })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_ctx(observations: Vec<ReturnTypeObservation>) -> RecoveryContext {
        RecoveryContext { return_register_observations: observations, ..Default::default() }
    }

    fn make_callee_ctx(observations: Vec<CalleeReturnObservation>) -> RecoveryContext {
        RecoveryContext { callee_return_observations: observations, ..Default::default() }
    }

    fn make_obs(uses: Vec<ReturnRegisterUse>) -> ReturnTypeObservation {
        ReturnTypeObservation {
            call_addr: 0x1000,
            callee_name: Some("test_func".to_string()),
            arch: CallingConvArch::Aarch64,
            uses,
        }
    }

    fn make_exit_state(
        register_written: bool,
        last_write_width: Option<u32>,
        is_boolean_pattern: bool,
        is_constant_zero: bool,
        is_constant_one: bool,
    ) -> ExitRegisterState {
        ExitRegisterState {
            exit_addr: 0x2000,
            register_written,
            last_write_width,
            is_boolean_pattern,
            is_constant_zero,
            is_constant_one,
        }
    }

    fn make_callee_obs(exit_states: Vec<ExitRegisterState>) -> CalleeReturnObservation {
        CalleeReturnObservation {
            function_addr: 0x4000,
            function_name: Some("callee_func".to_string()),
            arch: CallingConvArch::Aarch64,
            exit_states,
        }
    }

    #[test]
    fn test_return_type_pointer_arithmetic() {
        let ctx =
            make_ctx(vec![make_obs(vec![ReturnRegisterUse::PointerArithmetic { offset: 16 }])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, opaque_mut_ptr());
        assert!((evidence[0].confidence - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_null_check() {
        let ctx = make_ctx(vec![make_obs(vec![ReturnRegisterUse::NullCheck])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, opaque_mut_ptr());
        assert!((evidence[0].confidence - 0.60).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_sign_extend() {
        let ctx = make_ctx(vec![make_obs(vec![ReturnRegisterUse::SignExtend {
            from_bits: 32,
            to_bits: 64,
        }])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Int { width: 32, signed: true })
        );
        assert!((evidence[0].confidence - 0.70).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_zero_extend() {
        let ctx = make_ctx(vec![make_obs(vec![ReturnRegisterUse::ZeroExtend {
            from_bits: 16,
            to_bits: 64,
        }])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Int { width: 16, signed: false })
        );
        assert!((evidence[0].confidence - 0.70).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_float_use() {
        let ctx = make_ctx(vec![make_obs(vec![ReturnRegisterUse::FloatUse])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, RecoveredType::Primitive(Ty::Float { width: 64 }));
        assert!((evidence[0].confidence - 0.80).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_ignored() {
        let ctx = make_ctx(vec![make_obs(vec![ReturnRegisterUse::Ignored])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, RecoveredType::Primitive(Ty::Unit));
        assert!((evidence[0].confidence - 0.50).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_integer_arithmetic() {
        let ctx = make_ctx(vec![make_obs(vec![ReturnRegisterUse::IntegerArithmetic])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Int { width: 64, signed: false })
        );
        assert!((evidence[0].confidence - 0.55).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_combined_pointer_evidence() {
        let ctx = make_ctx(vec![make_obs(vec![
            ReturnRegisterUse::NullCheck,
            ReturnRegisterUse::PointerArithmetic { offset: 8 },
        ])]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, opaque_mut_ptr());
        // Combined evidence should boost confidence
        assert!(evidence[0].confidence >= 0.80);
        assert!((evidence[0].confidence - 0.85).abs() < f64::EPSILON);
    }

    #[test]
    fn test_return_type_empty_observations() {
        let ctx = make_ctx(vec![]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_return_type_multiple_observations() {
        let ctx = make_ctx(vec![
            ReturnTypeObservation {
                call_addr: 0x1000,
                callee_name: Some("malloc".to_string()),
                arch: CallingConvArch::X86_64,
                uses: vec![ReturnRegisterUse::NullCheck],
            },
            ReturnTypeObservation {
                call_addr: 0x2000,
                callee_name: Some("strlen".to_string()),
                arch: CallingConvArch::X86_64,
                uses: vec![ReturnRegisterUse::IntegerArithmetic],
            },
        ]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 2);

        // First: malloc returns pointer (null check)
        assert_eq!(evidence[0].recovered_type, opaque_mut_ptr());

        // Second: strlen returns integer
        assert_eq!(
            evidence[1].recovered_type,
            RecoveredType::Primitive(Ty::Int { width: 64, signed: false })
        );
    }

    #[test]
    fn test_return_type_aarch64_and_x86() {
        // Both architectures should produce the same type inference —
        // the arch field is metadata, not used for type selection.
        let aarch64_obs = ReturnTypeObservation {
            call_addr: 0x1000,
            callee_name: None,
            arch: CallingConvArch::Aarch64,
            uses: vec![ReturnRegisterUse::FloatUse],
        };
        let x86_obs = ReturnTypeObservation {
            call_addr: 0x2000,
            callee_name: None,
            arch: CallingConvArch::X86_64,
            uses: vec![ReturnRegisterUse::FloatUse],
        };

        let strategy = ReturnTypeStrategy;

        let ctx_aarch64 = make_ctx(vec![aarch64_obs]);
        let ev_aarch64 = strategy.recover(&ctx_aarch64).expect("should recover");

        let ctx_x86 = make_ctx(vec![x86_obs]);
        let ev_x86 = strategy.recover(&ctx_x86).expect("should recover");

        assert_eq!(ev_aarch64.len(), 1);
        assert_eq!(ev_x86.len(), 1);
        assert_eq!(ev_aarch64[0].recovered_type, ev_x86[0].recovered_type);
        assert_eq!(ev_aarch64[0].recovered_type, RecoveredType::Primitive(Ty::Float { width: 64 }));
    }

    #[test]
    fn test_return_type_empty_uses_skipped() {
        // An observation with no uses should produce no evidence
        let ctx = make_ctx(vec![ReturnTypeObservation {
            call_addr: 0x1000,
            callee_name: None,
            arch: CallingConvArch::Aarch64,
            uses: vec![],
        }]);

        let strategy = ReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_callee_void_function() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![
            make_exit_state(false, None, false, false, false),
            make_exit_state(false, None, false, false, false),
        ])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, RecoveredType::Primitive(Ty::Unit));
        assert!((evidence[0].confidence - 0.80).abs() < f64::EPSILON);
    }

    #[test]
    fn test_callee_boolean_cset_pattern() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![
            make_exit_state(true, Some(32), true, false, false),
            make_exit_state(true, Some(32), true, false, false),
        ])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, RecoveredType::Primitive(Ty::Bool));
        assert!((evidence[0].confidence - 0.85).abs() < f64::EPSILON);
    }

    #[test]
    fn test_callee_boolean_constant_values() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![
            make_exit_state(true, Some(32), false, true, false),
            make_exit_state(true, Some(32), false, false, true),
        ])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, RecoveredType::Primitive(Ty::Bool));
        assert!((evidence[0].confidence - 0.70).abs() < f64::EPSILON);
    }

    #[test]
    fn test_callee_integer_width_32() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![
            make_exit_state(true, Some(32), false, false, false),
            make_exit_state(true, Some(32), false, false, false),
        ])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, unsigned_int(32));
        assert!((evidence[0].confidence - 0.65).abs() < f64::EPSILON);
    }

    #[test]
    fn test_callee_integer_width_8() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![
            make_exit_state(true, Some(8), false, false, false),
            make_exit_state(true, Some(8), false, false, false),
        ])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, unsigned_int(8));
        assert!((evidence[0].confidence - 0.65).abs() < f64::EPSILON);
    }

    #[test]
    fn test_callee_mixed_widths() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![
            make_exit_state(true, Some(8), false, false, false),
            make_exit_state(true, Some(32), false, false, false),
            make_exit_state(true, Some(16), false, false, false),
        ])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, unsigned_int(32));
        assert!((evidence[0].confidence - 0.45).abs() < f64::EPSILON);
    }

    #[test]
    fn test_callee_empty_observations() {
        let ctx = make_callee_ctx(vec![]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_callee_no_exits() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_callee_single_exit_boolean() {
        let ctx = make_callee_ctx(vec![make_callee_obs(vec![make_exit_state(
            true,
            Some(32),
            true,
            false,
            false,
        )])]);

        let strategy = CalleeReturnTypeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].recovered_type, RecoveredType::Primitive(Ty::Bool));
        assert!((evidence[0].confidence - 0.85).abs() < f64::EPSILON);
        assert!(matches!(
            &evidence[0].source,
            EvidenceSource::CalleeReturnAnalysis {
                function_addr: 0x4000,
                function_name: Some(name),
                exit_count: 1,
            } if name == "callee_func"
        ));
    }
}
