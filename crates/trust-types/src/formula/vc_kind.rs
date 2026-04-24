// trust-types/formula/vc_kind: Verification condition kind classification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::ProofLevel;
use super::temporal::{FairnessConstraint, LivenessProperty};
use crate::model::{BinOp, Ty};

/// What kind of property a VC checks.
///
/// Each variant maps to a specific safety or functional property. The
/// `proof_level()` method classifies VcKinds into `ProofLevel` tiers
/// used by the router for backend selection.
///
/// # Examples
///
/// ```
/// use trust_types::{VcKind, ProofLevel};
///
/// // L0Safety kinds
/// assert_eq!(VcKind::DivisionByZero.proof_level(), ProofLevel::L0Safety);
/// assert_eq!(VcKind::IndexOutOfBounds.proof_level(), ProofLevel::L0Safety);
///
/// // L1Functional kinds
/// assert_eq!(VcKind::Postcondition.proof_level(), ProofLevel::L1Functional);
///
/// // Display shows a human-readable description
/// assert_eq!(format!("{}", VcKind::DivisionByZero), "division by zero");
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcKind {
    ArithmeticOverflow {
        op: BinOp,
        operand_tys: (Ty, Ty),
    },
    ShiftOverflow {
        op: BinOp,
        operand_ty: Ty,
        shift_ty: Ty,
    },
    DivisionByZero,
    RemainderByZero,
    IndexOutOfBounds,
    SliceBoundsCheck,
    Assertion {
        message: String,
    },
    Precondition {
        callee: String,
    },
    Postcondition,
    CastOverflow {
        from_ty: Ty,
        to_ty: Ty,
    },
    NegationOverflow {
        ty: Ty,
    },
    Unreachable,
    // State machine properties (tla2)
    DeadState {
        state: String,
    },
    Deadlock,
    Temporal {
        property: String,
    },
    // tRust: Liveness and fairness properties (#49)
    Liveness {
        property: LivenessProperty,
    },
    Fairness {
        constraint: FairnessConstraint,
    },
    TaintViolation {
        source_label: String,
        sink_kind: String,
        path_length: usize,
    },
    RefinementViolation {
        spec_file: String,
        action: String,
    },
    // tRust #53: External dependency resilience
    ResilienceViolation {
        service: String,
        failure_mode: String,
        reason: String,
    },
    // tRust: Cross-service protocol composition (#55)
    ProtocolViolation {
        protocol: String,
        violation: String,
    },
    // tRust #66: Termination checking via decreases clauses
    NonTermination {
        /// "loop" or "recursion"
        context: String,
        /// Which measure failed to decrease (e.g., "n", "len - i")
        measure: String,
    },
    // tRust #186: Neural network verification VcKinds for gamma-crown backend
    /// Verify that a neural network's output is robust to input perturbations
    /// within an epsilon ball (L-infinity norm).
    NeuralRobustness {
        /// Perturbation bound (stored as String to avoid f64 Serialize issues).
        epsilon: String,
    },
    /// Verify that a neural network's output stays within specified bounds.
    NeuralOutputRange {
        /// Lower bound on output (String for serialization safety).
        lower: String,
        /// Upper bound on output (String for serialization safety).
        upper: String,
    },
    /// Verify that a neural network satisfies a Lipschitz continuity bound.
    NeuralLipschitz {
        /// Lipschitz constant bound (String for serialization safety).
        constant: String,
    },
    /// Verify that a neural network is monotonic with respect to a given input dimension.
    NeuralMonotonicity {
        /// Input dimension index that should be monotonic.
        input_dim: usize,
    },
    // tRust #203: Data race and memory ordering verification
    /// Two threads access the same variable without happens-before ordering,
    /// and at least one access is a write.
    DataRace {
        /// The shared variable being accessed.
        variable: String,
        /// Thread ID of the first access.
        thread_a: String,
        /// Thread ID of the second access.
        thread_b: String,
    },
    /// An atomic access uses an ordering that is insufficient for correctness.
    InsufficientOrdering {
        /// The variable being accessed.
        variable: String,
        /// The ordering actually used (e.g., "Relaxed").
        actual: String,
        /// The minimum ordering required (e.g., "Acquire").
        required: String,
    },
    // tRust #149: Translation validation — compiled code refines source MIR semantics.
    /// Asserts that a post-optimization (or compiled) function refines the
    /// pre-optimization MIR. UNSAT means the transformation is correct.
    TranslationValidation {
        /// Name of the optimization pass (e.g., "constant_folding", "dce").
        pass: String,
        /// Which check category this VC covers.
        check: String,
    },
    // tRust #433: Floating-point operation verification conditions.
    /// Float division where divisor may be zero (produces +/-Inf per IEEE 754).
    FloatDivisionByZero,
    /// Float arithmetic that may overflow to infinity (+/-Inf).
    FloatOverflowToInfinity {
        op: BinOp,
        operand_ty: Ty,
    },
    // tRust #438: Rvalue safety VCs for Discriminant, Aggregate, Ref, and Len.
    /// Discriminant read on a place that does not hold an enum/ADT type.
    InvalidDiscriminant {
        /// Human-readable name of the place whose discriminant was read.
        place_name: String,
    },
    /// Array aggregate constructed with a mismatched element count.
    AggregateArrayLengthMismatch {
        /// Expected number of elements from the array type.
        expected: usize,
        /// Actual number of operands provided.
        actual: usize,
    },
    // tRust #463: Unsafe code VC.
    /// Unsafe operation detected (raw pointer deref, transmute, FFI, etc.).
    UnsafeOperation {
        desc: String,
    },
    // tRust #460: FFI boundary verification with summary-based VCs.
    /// FFI call site where a summary-based contract was checked.
    FfiBoundaryViolation {
        /// Name of the extern callee (e.g., "malloc", "memcpy").
        callee: String,
        /// Description of the specific violation (null, range, alias, etc.).
        desc: String,
    },
    // tRust #546: Typed ownership VcKind variants for certus integration.
    /// Accessing memory after it has been freed (use-after-free).
    UseAfterFree,
    /// Freeing the same allocation twice (double-free).
    DoubleFree,
    /// Aliasing violation: &mut coexists with another &/&mut reference.
    AliasingViolation {
        /// true if the conflicting alias is &mut, false if shared &.
        mutable: bool,
    },
    /// Reference outlives its referent (dangling reference).
    LifetimeViolation,
    /// Non-Send type sent across thread boundary.
    SendViolation,
    /// Non-Sync type shared across threads.
    SyncViolation,
    // tRust #597: Functional correctness verification condition.
    /// The function produces an incorrect result (e.g., binary search returns
    /// wrong index on unsorted input). The `property` field describes the
    /// expected property (e.g., "result correctness"), and `context` carries
    /// domain-specific information (e.g., "binary_search: input not sorted").
    FunctionalCorrectness {
        /// High-level property being checked (e.g., "result_correctness").
        property: String,
        /// Domain context explaining the failure (e.g., "input array not sorted").
        context: String,
    },
    // tRust #588: Sunder-style contract VcKinds for Horn clause lowering.
    /// Loop invariant initiation: the invariant holds on entry to the loop.
    LoopInvariantInitiation {
        /// The invariant expression that must hold at loop entry.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Loop invariant consecution: if the invariant holds before an iteration,
    /// it holds after the iteration (inductive step).
    LoopInvariantConsecution {
        /// The invariant expression being checked inductively.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Loop invariant sufficiency: the invariant implies the postcondition
    /// upon loop exit.
    LoopInvariantSufficiency {
        /// The invariant expression that must imply the post-loop property.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Type refinement violation: a value does not satisfy its refinement predicate.
    TypeRefinementViolation {
        /// The variable or expression being refined.
        variable: String,
        /// The refinement predicate that was violated (e.g., "v > 0").
        predicate: String,
    },
    /// Frame condition violation: a variable not in the modifies set was changed.
    FrameConditionViolation {
        /// The variable that was modified but not in the modifies clause.
        variable: String,
        /// The function whose frame condition was violated.
        function: String,
    },
}

impl VcKind {
    /// Human-readable description.
    pub fn description(&self) -> String {
        match self {
            VcKind::ArithmeticOverflow { op, .. } => {
                format!("arithmetic overflow ({op:?})")
            }
            VcKind::ShiftOverflow { op, .. } => {
                format!("shift overflow ({op:?})")
            }
            VcKind::DivisionByZero => "division by zero".to_string(),
            VcKind::RemainderByZero => "remainder by zero".to_string(),
            VcKind::IndexOutOfBounds => "index out of bounds".to_string(),
            VcKind::SliceBoundsCheck => "slice bounds check".to_string(),
            VcKind::Assertion { message } => format!("assertion: {message}"),
            VcKind::Precondition { callee } => format!("precondition of `{callee}`"),
            VcKind::Postcondition => "postcondition".to_string(),
            VcKind::CastOverflow { from_ty, to_ty } => {
                format!("cast overflow ({from_ty:?} -> {to_ty:?})")
            }
            VcKind::NegationOverflow { ty } => {
                format!("negation overflow ({ty:?})")
            }
            VcKind::Unreachable => "unreachable code reached".to_string(),
            VcKind::DeadState { state } => format!("dead state `{state}`"),
            VcKind::Deadlock => "deadlock".to_string(),
            VcKind::Temporal { property } => format!("temporal: {property}"),
            VcKind::Liveness { property } => format!("liveness: {}", property.description()),
            VcKind::Fairness { constraint } => {
                format!("fairness: {}", constraint.description())
            }
            VcKind::TaintViolation { source_label, sink_kind, path_length } => {
                format!(
                    "taint violation: {} data reaches {} sink (path length: {})",
                    source_label, sink_kind, path_length
                )
            }
            VcKind::RefinementViolation { spec_file, action } => {
                format!(
                    "refinement violation: action `{action}` does not refine spec `{spec_file}`"
                )
            }
            VcKind::ResilienceViolation { service, failure_mode, reason } => {
                format!("resilience: {service} {failure_mode} - {reason}")
            }
            VcKind::ProtocolViolation { protocol, violation } => {
                format!("protocol `{protocol}`: {violation}")
            }
            VcKind::NonTermination { context, measure } => {
                format!("non-termination: {context} measure `{measure}` may not decrease")
            }
            // tRust #186: Neural network verification descriptions
            VcKind::NeuralRobustness { epsilon } => {
                format!("neural robustness (epsilon={epsilon})")
            }
            VcKind::NeuralOutputRange { lower, upper } => {
                format!("neural output range [{lower}, {upper}]")
            }
            VcKind::NeuralLipschitz { constant } => {
                format!("neural Lipschitz (constant={constant})")
            }
            VcKind::NeuralMonotonicity { input_dim } => {
                format!("neural monotonicity (input_dim={input_dim})")
            }
            // tRust #203: Data race and memory ordering descriptions
            VcKind::DataRace { variable, thread_a, thread_b } => {
                format!("data race on `{variable}` between threads {thread_a} and {thread_b}")
            }
            VcKind::InsufficientOrdering { variable, actual, required } => {
                format!(
                    "insufficient memory ordering on `{variable}`: {actual}, requires {required}"
                )
            }
            VcKind::TranslationValidation { pass, check } => {
                format!("translation validation ({pass}): {check}")
            }
            // tRust #433: Floating-point VC descriptions
            VcKind::FloatDivisionByZero => "float division by zero".to_string(),
            VcKind::FloatOverflowToInfinity { op, .. } => {
                format!("float overflow to infinity ({op:?})")
            }
            // tRust #438: Rvalue safety VC descriptions
            VcKind::InvalidDiscriminant { place_name } => {
                format!("invalid discriminant read on `{place_name}` (not an enum)")
            }
            VcKind::AggregateArrayLengthMismatch { expected, actual } => {
                format!(
                    "array aggregate length mismatch: expected {expected} elements, got {actual}"
                )
            }
            // tRust #463: Unsafe operation description.
            VcKind::UnsafeOperation { desc } => format!("unsafe operation: {desc}"),
            // tRust #460: FFI boundary verification description.
            VcKind::FfiBoundaryViolation { callee, desc } => {
                format!("FFI boundary violation in `{callee}`: {desc}")
            }
            // tRust #546: Ownership VcKind descriptions.
            VcKind::UseAfterFree => "use after free".to_string(),
            VcKind::DoubleFree => "double free".to_string(),
            VcKind::AliasingViolation { mutable } => {
                if *mutable {
                    "aliasing violation: &mut aliases with &mut".to_string()
                } else {
                    "aliasing violation: &mut aliases with &".to_string()
                }
            }
            VcKind::LifetimeViolation => {
                "lifetime violation: reference outlives referent".to_string()
            }
            VcKind::SendViolation => {
                "Send violation: non-Send type sent across threads".to_string()
            }
            VcKind::SyncViolation => {
                "Sync violation: non-Sync type shared across threads".to_string()
            }
            // tRust #597: Functional correctness description.
            VcKind::FunctionalCorrectness { property, context } => {
                format!("functional correctness ({property}): {context}")
            }
            // tRust #588: Sunder contract VC descriptions.
            VcKind::LoopInvariantInitiation { invariant, header_block } => {
                format!("loop invariant initiation (bb{header_block}): {invariant}")
            }
            VcKind::LoopInvariantConsecution { invariant, header_block } => {
                format!("loop invariant consecution (bb{header_block}): {invariant}")
            }
            VcKind::LoopInvariantSufficiency { invariant, header_block } => {
                format!("loop invariant sufficiency (bb{header_block}): {invariant}")
            }
            VcKind::TypeRefinementViolation { variable, predicate } => {
                format!("type refinement violation: {variable} does not satisfy {predicate}")
            }
            VcKind::FrameConditionViolation { variable, function } => {
                format!(
                    "frame condition violation: `{variable}` modified outside modifies clause of `{function}`"
                )
            }
        }
    }

    /// Returns the proof level (L0, L1, L2).
    pub fn proof_level(&self) -> ProofLevel {
        match self {
            VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::Assertion { .. }
            | VcKind::CastOverflow { .. }
            | VcKind::NegationOverflow { .. }
            | VcKind::Unreachable
            // tRust #438: Discriminant on non-enum and array length mismatch are safety (L0).
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            | VcKind::UnsafeOperation { .. }
            // tRust #460: FFI boundary violations are safety (L0).
            | VcKind::FfiBoundaryViolation { .. } => ProofLevel::L0Safety,
            VcKind::Precondition { .. } | VcKind::Postcondition => ProofLevel::L1Functional,
            VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. } => ProofLevel::L2Domain,
            VcKind::TaintViolation { .. } => ProofLevel::L1Functional,
            VcKind::ResilienceViolation { .. } => ProofLevel::L1Functional,
            VcKind::NonTermination { .. } => ProofLevel::L1Functional,
            VcKind::NeuralRobustness { .. }
            | VcKind::NeuralOutputRange { .. }
            | VcKind::NeuralLipschitz { .. }
            | VcKind::NeuralMonotonicity { .. } => ProofLevel::L2Domain,
            // tRust #203: Data races are UB (L0 safety), ordering is correctness (L1).
            VcKind::DataRace { .. } => ProofLevel::L0Safety,
            VcKind::InsufficientOrdering { .. } => ProofLevel::L1Functional,
            // tRust #149: Translation validation is functional correctness (L1).
            VcKind::TranslationValidation { .. } => ProofLevel::L1Functional,
            // tRust #433: Float division by zero and overflow to infinity are L0 safety.
            // IEEE 754 defines these as producing Inf/NaN (not UB), but they are
            // almost always programming errors worth flagging.
            VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
                ProofLevel::L0Safety
            }
            // tRust #546: Ownership violations are all UB (L0 safety).
            VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation => ProofLevel::L0Safety,
            // tRust #597: Functional correctness is L1.
            VcKind::FunctionalCorrectness { .. } => ProofLevel::L1Functional,
            // tRust #588: Sunder contract VCs are L1 functional correctness.
            VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
            | VcKind::TypeRefinementViolation { .. }
            | VcKind::FrameConditionViolation { .. } => ProofLevel::L1Functional,
        }
    }

    /// Returns whether Rust has a corresponding runtime check for this VC kind.
    #[must_use]
    pub fn has_runtime_fallback(&self, overflow_checks: bool) -> bool {
        match self {
            VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::NegationOverflow { .. } => overflow_checks,
            VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::Assertion { .. }
            | VcKind::Unreachable => true,
            VcKind::CastOverflow { .. }
            | VcKind::Precondition { .. }
            | VcKind::Postcondition
            | VcKind::ResilienceViolation { .. }
            | VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::TaintViolation { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. }
            | VcKind::NonTermination { .. }
            | VcKind::NeuralRobustness { .. }
            | VcKind::NeuralOutputRange { .. }
            | VcKind::NeuralLipschitz { .. }
            | VcKind::NeuralMonotonicity { .. }
            // tRust #203: No runtime checks for data races or ordering violations.
            | VcKind::DataRace { .. }
            | VcKind::InsufficientOrdering { .. }
            // tRust #149: Translation validation has no runtime fallback.
            | VcKind::TranslationValidation { .. }
            // tRust #433: Float ops silently produce Inf/NaN per IEEE 754 — no runtime check.
            | VcKind::FloatDivisionByZero
            | VcKind::FloatOverflowToInfinity { .. } => false,
            // tRust #438: No runtime checks for type-level safety VCs.
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            // tRust #463: No runtime check for unsafe operations.
            | VcKind::UnsafeOperation { .. }
            // tRust #460: No runtime check for FFI boundary violations.
            | VcKind::FfiBoundaryViolation { .. }
            // tRust #546: Ownership violations have no runtime check (UB in unsafe code).
            | VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation
            // tRust #597: Functional correctness has no runtime fallback.
            | VcKind::FunctionalCorrectness { .. }
            // tRust #588: Sunder contract VCs have no runtime fallback.
            | VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
            | VcKind::TypeRefinementViolation { .. }
            | VcKind::FrameConditionViolation { .. } => false,
        }
    }
}

// tRust #594: Display delegates to description() so `.to_string()` works in tests.
impl std::fmt::Display for VcKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.description())
    }
}
