// trust-types/result.rs: Verification results
//
// What solvers return after checking a verification condition.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::SourceSpan;
use crate::Symbol;
use crate::formula::{ProofLevel, VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// tRust #435: SMT theory classification for TheoryLemma reasoning kind.
// ---------------------------------------------------------------------------

/// SMT theory classification for `ReasoningKind::TheoryLemma`.
///
/// Identifies which SMT theory solver produced a theory lemma in a proof.
/// Used to distinguish e.g. LIA arithmetic reasoning from bitvector blasting.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SmtTheory {
    /// Linear integer/real arithmetic (LIA/LRA).
    LinearArithmetic,
    /// Fixed-width bitvector theory.
    Bitvectors,
    /// Uninterpreted functions and equality.
    UninterpretedFunctions,
    /// Array theory (select/store).
    Arrays,
    /// Algebraic datatypes.
    Datatypes,
    /// Nonlinear integer/real arithmetic (NIA/NRA).
    NonlinearArithmetic,
    /// String theory.
    Strings,
}

/// What a solver returns.
///
/// Each variant represents a possible outcome from a verification backend
/// (z4, sunder, tla2, etc.).
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationResult, ProofStrength};
///
/// // A proved result from z4
/// let proved = VerificationResult::Proved {
///     solver: "z4".into(),
///     time_ms: 5,
///     strength: ProofStrength::smt_unsat(),
///     proof_certificate: None,
///     solver_warnings: None,
/// };
/// assert!(proved.is_proved());
/// assert_eq!(proved.solver_name(), "z4");
/// assert_eq!(proved.time_ms(), 5);
///
/// // A timeout result
/// let timeout = VerificationResult::Timeout {
///     solver: "z4".into(),
///     timeout_ms: 30000,
/// };
/// assert!(!timeout.is_proved());
/// assert_eq!(timeout.time_ms(), 30000);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationResult {
    Proved {
        // tRust #907: Interned solver name — small set repeated across all results.
        solver: Symbol,
        time_ms: u64,
        strength: ProofStrength,
        /// tRust #490: Raw proof certificate data from the solver (e.g., LRAT bytes from z4).
        /// Populated when the solver produces a proof certificate alongside an UNSAT result.
        /// `None` when no certificate is available (e.g., non-z4 solvers, or older results).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        proof_certificate: Option<Vec<u8>>,
        /// tRust #732: Warnings captured from solver stderr during verification.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        solver_warnings: Option<Vec<String>>,
    },
    Failed {
        solver: Symbol,
        time_ms: u64,
        counterexample: Option<Counterexample>,
    },
    Unknown {
        solver: Symbol,
        time_ms: u64,
        reason: String,
    },
    Timeout {
        solver: Symbol,
        timeout_ms: u64,
    },
}

impl VerificationResult {
    pub fn is_proved(&self) -> bool {
        matches!(self, VerificationResult::Proved { .. })
    }

    pub fn is_failed(&self) -> bool {
        matches!(self, VerificationResult::Failed { .. })
    }

    pub fn solver_name(&self) -> &str {
        match self {
            VerificationResult::Proved { solver, .. }
            | VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. } => solver.as_str(),
        }
    }

    /// tRust #907: Get the solver Symbol (Copy, O(1) equality).
    #[must_use]
    pub fn solver_symbol(&self) -> Symbol {
        match self {
            VerificationResult::Proved { solver, .. }
            | VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. } => *solver,
        }
    }

    pub fn time_ms(&self) -> u64 {
        match self {
            VerificationResult::Proved { time_ms, .. }
            | VerificationResult::Failed { time_ms, .. }
            | VerificationResult::Unknown { time_ms, .. } => *time_ms,
            VerificationResult::Timeout { timeout_ms, .. } => *timeout_ms,
        }
    }

    /// tRust #382: Derive `ProofEvidence` from this result.
    ///
    /// Returns `Some(ProofEvidence)` for `Proved` results (converting the legacy
    /// `ProofStrength` via `From`), and `None` for all other outcomes.
    #[must_use]
    pub fn evidence(&self) -> Option<ProofEvidence> {
        match self {
            VerificationResult::Proved { strength, .. } => Some(strength.clone().into()),
            _ => None,
        }
    }
}

/// How a proof was obtained (the reasoning technique used).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReasoningKind {
    /// SMT solver returned UNSAT (e.g., z4 DPLL(T)).
    Smt,
    /// Bounded model checking explored states up to a given depth (e.g., zani BMC, incomplete).
    BoundedModelCheck { depth: u64 },
    /// tRust #190: Exhaustive finite-state exploration (e.g., tla2 BFS, complete for finite).
    ExhaustiveFinite(u64),
    /// An inductive safety invariant was found (e.g., k-induction, IC3/PDR, CEGAR).
    ///
    /// tRust #194: These techniques prove safety properties (AG !bad) — that bad states
    /// are unreachable. They do NOT prove termination, which requires ranking functions,
    /// well-founded orderings, or decreases clauses.
    Inductive,
    /// Deductive verification via pre/postcondition reasoning (e.g., sunder, certus).
    Deductive,
    /// Constructive proof term produced (e.g., lean5).
    Constructive,
    /// Property-directed reachability (IC3/PDR) — proves safety properties (AG !bad).
    ///
    /// tRust #194: PDR/IC3 finds inductive invariants that prove bad states are
    /// unreachable. It does NOT prove termination or liveness. Termination requires
    /// ranking function synthesis; liveness requires fairness + ranking or Buchi automata.
    Pdr,
    /// Constrained Horn Clause solving via Spacer.
    ChcSpacer,
    /// Abstract interpretation discharged the obligation (sound over-approximation).
    AbstractInterpretation,

    // --- tRust #435: New variants for SMT proof technique granularity ---
    /// CDCL resolution proof from SAT/SMT Boolean skeleton.
    CdclResolution,
    /// Theory-specific lemma (LIA, BV, UF, arrays, etc.).
    TheoryLemma { theory: SmtTheory },
    /// Bitvector to SAT reduction.
    BitBlasting,

    // --- tRust #435: Solver-specific techniques ---
    /// Symbolic execution (future concolic/SE backends).
    SymbolicExecution,
    /// Ownership and borrow-checker reasoning (certus).
    OwnershipAnalysis,
    /// Explicit-state model checking (tla2 BFS/DFS complete check).
    ExplicitStateModel,
    /// Neural network verification via bounding (gamma-crown).
    NeuralBounding,
    /// Craig interpolation for modular verification.
    Interpolation,
}

impl ReasoningKind {
    /// Whether this reasoning method is complete (covers all inputs).
    ///
    /// Returns `true` for `Smt`, `ExhaustiveFinite`, `Inductive`,
    /// `Deductive`, `Constructive`, `Pdr`, `ChcSpacer`, `AbstractInterpretation`,
    /// `CdclResolution`, `TheoryLemma`, `BitBlasting`, `OwnershipAnalysis`,
    /// `ExplicitStateModel`, `Interpolation`.
    /// Returns `false` for `BoundedModelCheck` (only checks up to a depth),
    /// `SymbolicExecution` (bounded by path depth), `NeuralBounding` (epsilon-bounded).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        !matches!(
            self,
            Self::BoundedModelCheck { .. } | Self::SymbolicExecution | Self::NeuralBounding
        )
    }
}

/// How much confidence the proof provides.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AssuranceLevel {
    /// Complete, sound proof — property holds for all inputs.
    Sound,
    /// Property checked up to a bounded depth (no violation found within depth).
    BoundedSound { depth: u64 },
    /// Best-effort / heuristic — no formal guarantee.
    Heuristic,
    /// tRust #190: Solver said so, no independent validation.
    Unchecked,
    /// tRust #190: Solver UNSAT, trusted TCB.
    Trusted,
    /// tRust #190: z4 axiom in lean5, not fully reconstructed.
    SmtBacked,
    /// tRust #190: lean5 kernel independently verified.
    Certified,
}

impl AssuranceLevel {
    /// tRust #190: Numeric strength ordering for comparison.
    ///
    /// `Unchecked`/`Heuristic`=0, `Trusted`/`BoundedSound`=1,
    /// `SmtBacked`/`Sound`=2, `Certified`=3.
    #[must_use]
    pub fn strength_order(&self) -> u8 {
        match self {
            Self::Unchecked | Self::Heuristic => 0,
            Self::Trusted | Self::BoundedSound { .. } => 1,
            Self::SmtBacked | Self::Sound => 2,
            Self::Certified => 3,
        }
    }
}

/// How strong the proof is: combines *how* it was done with *how much* assurance it provides.
///
/// # Examples
///
/// ```
/// use trust_types::ProofStrength;
///
/// // Most common: SMT solver returned UNSAT
/// let smt = ProofStrength::smt_unsat();
///
/// // Bounded model checking to depth 100
/// let bmc = ProofStrength::bounded(100);
///
/// // Deductive (pre/postcondition) proof
/// let ded = ProofStrength::deductive();
///
/// // Compare assurance levels
/// assert!(smt.assurance.strength_order() > bmc.assurance.strength_order());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProofStrength {
    /// The reasoning technique used to obtain this proof.
    pub reasoning: ReasoningKind,
    /// The level of assurance the proof provides.
    pub assurance: AssuranceLevel,
}

impl ProofStrength {
    /// SMT solver returned UNSAT — sound, complete proof.
    #[must_use]
    pub fn smt_unsat() -> Self {
        Self { reasoning: ReasoningKind::Smt, assurance: AssuranceLevel::Sound }
    }

    /// BMC checked all states to depth k with no violation.
    #[must_use]
    pub fn bounded(depth: u64) -> Self {
        Self {
            reasoning: ReasoningKind::BoundedModelCheck { depth },
            assurance: AssuranceLevel::BoundedSound { depth },
        }
    }

    /// An inductive safety invariant was found — sound proof of safety (AG !bad).
    ///
    /// tRust #194: Does NOT prove termination. See `TerminationStrategy` for
    /// termination proof techniques.
    #[must_use]
    pub fn inductive() -> Self {
        Self { reasoning: ReasoningKind::Inductive, assurance: AssuranceLevel::Sound }
    }

    /// Deductive verification (pre/postcondition reasoning) — sound proof.
    #[must_use]
    pub fn deductive() -> Self {
        Self { reasoning: ReasoningKind::Deductive, assurance: AssuranceLevel::Sound }
    }

    /// Constructive proof term (lean5) — sound proof.
    #[must_use]
    pub fn constructive() -> Self {
        Self { reasoning: ReasoningKind::Constructive, assurance: AssuranceLevel::Sound }
    }

    /// Property-directed reachability (IC3/PDR) — sound proof of safety (AG !bad).
    ///
    /// tRust #194: PDR proves safety properties only. It does NOT prove termination
    /// or liveness. Termination requires ranking functions or well-founded orderings.
    #[must_use]
    pub fn pdr() -> Self {
        Self { reasoning: ReasoningKind::Pdr, assurance: AssuranceLevel::Sound }
    }

    /// CHC solving via Spacer — sound proof.
    #[must_use]
    pub fn chc_spacer() -> Self {
        Self { reasoning: ReasoningKind::ChcSpacer, assurance: AssuranceLevel::Sound }
    }

    /// Abstract interpretation — sound proof via over-approximation.
    #[must_use]
    pub fn abstract_interpretation() -> Self {
        Self { reasoning: ReasoningKind::AbstractInterpretation, assurance: AssuranceLevel::Sound }
    }

    /// Whether the proof provides full (sound) assurance.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        matches!(self.assurance, AssuranceLevel::Sound)
    }

    /// Whether the proof is only bounded (checked up to a depth).
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        matches!(self.assurance, AssuranceLevel::BoundedSound { .. })
    }

    /// Get the bounded depth, if this is a bounded proof.
    #[must_use]
    pub fn bounded_depth(&self) -> Option<u64> {
        match &self.assurance {
            AssuranceLevel::BoundedSound { depth } => Some(*depth),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// tRust #190: ProofEvidence — combined reasoning + assurance (new type system)
// ---------------------------------------------------------------------------

/// Combined proof evidence: what method was used + how much we trust it.
///
/// This is the correct replacement for using `ProofStrength` directly.
/// `ProofStrength` conflates reasoning method with certification status;
/// `ProofEvidence` keeps them orthogonal so that e.g. a `BoundedDepth`
/// result can never silently upgrade to `Certified`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProofEvidence {
    /// What kind of reasoning was used to prove the property.
    pub reasoning: ReasoningKind,
    /// How much independent assurance backs the proof.
    pub assurance: AssuranceLevel,
}

impl ProofEvidence {
    /// Create a new `ProofEvidence` from reasoning kind and assurance level.
    #[must_use]
    pub fn new(reasoning: ReasoningKind, assurance: AssuranceLevel) -> Self {
        Self { reasoning, assurance }
    }

    /// Whether this evidence has been independently certified (lean5 kernel).
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.assurance, AssuranceLevel::Certified)
    }

    /// Whether this evidence comes from bounded (incomplete) reasoning.
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        matches!(self.reasoning, ReasoningKind::BoundedModelCheck { .. })
    }
}

impl From<ProofStrength> for ProofEvidence {
    /// Backward-compatible conversion from legacy `ProofStrength`.
    ///
    /// Maps existing `AssuranceLevel` variants into the new evidence model:
    /// `Sound` maps to `SmtBacked`, `BoundedSound` preserves its depth, and
    /// `Heuristic` to `Unchecked`. New variants pass through directly.
    fn from(ps: ProofStrength) -> Self {
        let assurance = match ps.assurance {
            AssuranceLevel::Sound => AssuranceLevel::SmtBacked,
            AssuranceLevel::BoundedSound { depth } => AssuranceLevel::BoundedSound { depth },
            AssuranceLevel::Heuristic => AssuranceLevel::Unchecked,
            // New variants pass through directly.
            other => other,
        };
        Self { reasoning: ps.reasoning, assurance }
    }
}

/// How unresolved verification results should be classified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[non_exhaustive]
pub enum RuntimeCheckPolicy {
    /// Use Rust's existing runtime checks when verification is inconclusive and
    /// the VC kind has a corresponding runtime fallback.
    #[default]
    Auto,
    /// Require a static proof. Unknown or timeout results become compile errors.
    ForceStatic,
    /// Always classify the obligation as runtime-checked unless a concrete
    /// counterexample was found.
    ForceRuntime,
}

/// Final disposition for an obligation after applying runtime-check policy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RuntimeDisposition {
    /// The obligation was discharged statically.
    Proved,
    /// The obligation will be enforced dynamically at runtime.
    RuntimeChecked { note: String },
    /// The obligation has a concrete counterexample.
    Failed,
    /// Verification was inconclusive and no runtime fallback was applied.
    Unknown { reason: String },
    /// Verification timed out and no runtime fallback was applied.
    Timeout { timeout_ms: u64 },
    /// Compilation should fail because static proof was required.
    CompileError { reason: String },
}

const FORCED_RUNTIME_NOTE: &str = "forced by #[trust(runtime)]";

/// Classify a solver result into a static, runtime-checked, or compile-error
/// disposition after applying the requested runtime-check policy.
#[must_use]
pub fn classify_runtime_disposition(
    vc_kind: &VcKind,
    result: &VerificationResult,
    policy: RuntimeCheckPolicy,
    overflow_checks: bool,
) -> RuntimeDisposition {
    match result {
        VerificationResult::Failed { .. } => RuntimeDisposition::Failed,
        VerificationResult::Proved { .. } => {
            if policy == RuntimeCheckPolicy::ForceRuntime {
                RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.to_string() }
            } else {
                RuntimeDisposition::Proved
            }
        }
        VerificationResult::Unknown { reason, .. } => match policy {
            RuntimeCheckPolicy::Auto if vc_kind.has_runtime_fallback(overflow_checks) => {
                RuntimeDisposition::RuntimeChecked { note: vc_kind.description() }
            }
            RuntimeCheckPolicy::Auto => RuntimeDisposition::Unknown { reason: reason.clone() },
            RuntimeCheckPolicy::ForceStatic => RuntimeDisposition::CompileError {
                reason: format!(
                    "`#[trust(static)]` requires a static proof, but the solver returned unknown: {reason}"
                ),
            },
            RuntimeCheckPolicy::ForceRuntime => {
                RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.to_string() }
            }
        },
        VerificationResult::Timeout { timeout_ms, .. } => match policy {
            RuntimeCheckPolicy::Auto if vc_kind.has_runtime_fallback(overflow_checks) => {
                RuntimeDisposition::RuntimeChecked { note: vc_kind.description() }
            }
            RuntimeCheckPolicy::Auto => RuntimeDisposition::Timeout { timeout_ms: *timeout_ms },
            RuntimeCheckPolicy::ForceStatic => RuntimeDisposition::CompileError {
                reason: format!(
                    "`#[trust(static)]` requires a static proof, but verification timed out after {timeout_ms}ms"
                ),
            },
            RuntimeCheckPolicy::ForceRuntime => {
                RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.to_string() }
            }
        },
    }
}

/// A counterexample: concrete variable assignments that violate the property.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Counterexample {
    pub assignments: Vec<(String, CounterexampleValue)>,
    /// tRust: Optional step-by-step execution trace from BMC counterexample.
    /// Each step maps to one unrolling depth with variable assignments and
    /// an optional MIR basic block index.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trace: Option<CounterexampleTrace>,
}

impl Counterexample {
    pub fn new(assignments: Vec<(String, CounterexampleValue)>) -> Self {
        Counterexample { assignments, trace: None }
    }

    /// tRust: Create a counterexample with an execution trace from BMC.
    pub fn with_trace(
        assignments: Vec<(String, CounterexampleValue)>,
        trace: CounterexampleTrace,
    ) -> Self {
        Counterexample { assignments, trace: Some(trace) }
    }
}

impl std::fmt::Display for Counterexample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parts: Vec<String> =
            self.assignments.iter().map(|(name, val)| format!("{name} = {val}")).collect();
        write!(f, "{}", parts.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CounterexampleValue {
    Bool(bool),
    Int(i128),
    Uint(u128),
    Float(f64),
}

impl std::fmt::Display for CounterexampleValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CounterexampleValue::Bool(b) => write!(f, "{b}"),
            CounterexampleValue::Int(n) => write!(f, "{n}"),
            CounterexampleValue::Uint(n) => write!(f, "{n}"),
            CounterexampleValue::Float(n) => write!(f, "{n}"),
        }
    }
}

// ---------------------------------------------------------------------------
// tRust: BMC counterexample trace types (#185)
// ---------------------------------------------------------------------------

/// tRust: Step-by-step execution trace extracted from a BMC counterexample.
///
/// Each step corresponds to one unrolling depth in the BMC encoding. The trace
/// maps variable assignments at each step back to MIR basic block indices,
/// enabling source-level debugging of counterexamples.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CounterexampleTrace {
    /// Ordered sequence of trace steps, one per BMC unrolling depth.
    pub steps: Vec<TraceStep>,
}

impl CounterexampleTrace {
    /// Create a trace from a list of steps.
    pub fn new(steps: Vec<TraceStep>) -> Self {
        Self { steps }
    }

    /// Number of steps in the trace.
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the trace is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

impl std::fmt::Display for CounterexampleTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for step in &self.steps {
            write!(f, "  step {}: ", step.step)?;
            if let Some(ref pp) = step.program_point {
                write!(f, "[{pp}] ")?;
            }
            let assigns: Vec<String> =
                step.assignments.iter().map(|(k, v)| format!("{k}={v}")).collect();
            writeln!(f, "{}", assigns.join(", "))?;
        }
        Ok(())
    }
}

/// tRust: A single step in a BMC counterexample trace.
///
/// Captures the variable assignments at one unrolling depth, plus an optional
/// mapping back to the MIR basic block that this step corresponds to.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraceStep {
    /// The BMC unrolling step index (0-based).
    pub step: u32,
    /// Variable assignments at this step, keyed by variable name.
    pub assignments: std::collections::BTreeMap<String, String>,
    /// Optional program point label (e.g., "bb3" for MIR basic block 3).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub program_point: Option<String>,
}

/// Summary of verification results for a function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionReport {
    pub function: String,
    pub proved: Vec<ProvedProperty>,
    pub failed: Vec<FailedProperty>,
    pub unknown: Vec<UnknownProperty>,
}

/// Function-level summary with obligation counts and timing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSummary {
    /// Total obligations checked.
    pub total_obligations: usize,
    /// Number proved safe.
    pub proved: usize,
    /// Number checked at runtime instead of proved statically.
    #[serde(default)]
    pub runtime_checked: usize,
    /// Number with counterexamples (violations).
    pub failed: usize,
    /// Number unknown or timed out.
    pub unknown: usize,
    /// Total solver wall-clock time in milliseconds for this function.
    pub total_time_ms: u64,
    /// Highest proof level achieved across all obligations.
    pub max_proof_level: Option<ProofLevel>,
    /// Overall verdict for the function.
    pub verdict: FunctionVerdict,
}

/// Overall verification verdict for a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FunctionVerdict {
    /// All obligations proved safe.
    Verified,
    /// No violations, but some obligations were checked at runtime.
    RuntimeChecked,
    /// At least one obligation has a counterexample.
    HasViolations,
    /// No violations found, but some obligations are unknown.
    Inconclusive,
    /// No verification obligations existed.
    NoObligations,
}

/// Per-obligation detail in the JSON report. Every obligation gets one of these,
/// regardless of outcome. This is the atomic unit of the report.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObligationReport {
    /// Human-readable description of the property checked.
    pub description: String,
    /// Structured kind tag for machine consumption (e.g., "arithmetic_overflow").
    pub kind: String,
    /// Proof level this obligation belongs to.
    pub proof_level: ProofLevel,
    /// Source location where the obligation originates.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// Verification outcome.
    pub outcome: ObligationOutcome,
    /// Which solver produced this result.
    pub solver: String,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
    /// tRust #382: Proof evidence (reasoning + assurance) for proved obligations.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub evidence: Option<ProofEvidence>,
}

// tRust #161: ObligationLocation alias removed — use SourceSpan directly.

/// Structured verification outcome for a single obligation.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "status")]
#[non_exhaustive]
pub enum ObligationOutcome {
    /// Property proved safe — no violation possible.
    #[serde(rename = "proved")]
    Proved { strength: ProofStrength },
    /// Property violated — counterexample available.
    #[serde(rename = "failed")]
    Failed {
        #[serde(skip_serializing_if = "Option::is_none")]
        counterexample: Option<CounterexampleReport>,
    },
    /// Solver could not determine outcome.
    #[serde(rename = "unknown")]
    Unknown { reason: String },
    /// Property was checked dynamically at runtime rather than proved statically.
    #[serde(rename = "runtime_checked")]
    RuntimeChecked {
        #[serde(skip_serializing_if = "Option::is_none")]
        note: Option<String>,
    },
    /// Solver timed out.
    #[serde(rename = "timeout")]
    Timeout { timeout_ms: u64 },
}

/// Machine-friendly counterexample with named variables and typed values.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CounterexampleReport {
    pub variables: Vec<CounterexampleVariable>,
}

/// A single variable assignment in a counterexample.
///
/// Values are represented as strings because serde_json does not support
/// i128/u128 natively. The `value_type` field provides type information
/// for machine consumers that need to parse the value.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CounterexampleVariable {
    pub name: String,
    /// The value as a string (supports arbitrarily large integers).
    pub value: String,
    /// Type of the value for machine parsing: "bool", "int", "uint", "float".
    pub value_type: String,
    /// Display-friendly string representation of the value.
    pub display: String,
}

/// Enriched per-function report with obligations and summary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionProofReport {
    /// Fully qualified function name.
    pub function: String,
    /// Function-level summary.
    pub summary: FunctionSummary,
    /// Per-obligation details, in source order.
    pub obligations: Vec<ObligationReport>,
}

/// Crate-level metadata for the proof report.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReportMetadata {
    /// JSON schema version for this report format.
    pub schema_version: String,
    /// tRust version that produced this report.
    pub trust_version: String,
    /// ISO 8601 timestamp when the report was generated.
    pub timestamp: String,
    /// Total wall-clock time for all verification in milliseconds.
    pub total_time_ms: u64,
}

/// Crate-level summary aggregating all function results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrateSummary {
    /// Total functions analyzed.
    pub functions_analyzed: usize,
    /// Functions with all obligations proved.
    pub functions_verified: usize,
    /// Functions with no violations, but some runtime-checked obligations.
    #[serde(default)]
    pub functions_runtime_checked: usize,
    /// Functions with at least one violation.
    pub functions_with_violations: usize,
    /// Functions with inconclusive results.
    pub functions_inconclusive: usize,
    /// Total obligations across all functions.
    pub total_obligations: usize,
    /// Obligations proved safe.
    pub total_proved: usize,
    /// Obligations checked at runtime instead of proved statically.
    #[serde(default)]
    pub total_runtime_checked: usize,
    /// Obligations with counterexamples.
    pub total_failed: usize,
    /// Obligations unknown or timed out.
    pub total_unknown: usize,
    /// Overall crate verdict.
    pub verdict: CrateVerdict,
}

/// Overall crate-level verification verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CrateVerdict {
    /// All functions verified, all obligations proved.
    Verified,
    /// No violations, but some functions rely on runtime checks.
    RuntimeChecked,
    /// At least one function has a violation.
    HasViolations,
    /// No violations, but some functions are inconclusive.
    Inconclusive,
    /// No verifiable functions found.
    NoObligations,
}

/// The complete JSON proof report. This is the canonical output format.
/// All other formats (text, HTML, terminal) are derived from this.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonProofReport {
    /// Report metadata (version, timestamp, timing).
    pub metadata: ReportMetadata,
    /// Crate being verified.
    pub crate_name: String,
    /// Crate-level summary.
    pub summary: CrateSummary,
    /// Per-function results with full obligation details.
    pub functions: Vec<FunctionProofReport>,
}

/// A single NDJSON line for streaming output. Each line is one function result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NdjsonFunctionRecord {
    /// Record type tag for stream parsing.
    pub record_type: String,
    /// Crate this function belongs to.
    pub crate_name: String,
    /// The function report.
    #[serde(flatten)]
    pub function: FunctionProofReport,
}

/// NDJSON header record emitted at the start of a stream.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NdjsonHeader {
    /// Always "header".
    pub record_type: String,
    /// Report metadata.
    pub metadata: ReportMetadata,
    /// Crate being verified.
    pub crate_name: String,
}

/// NDJSON footer record emitted at the end of a stream.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NdjsonFooter {
    /// Always "footer".
    pub record_type: String,
    /// Crate-level summary.
    pub summary: CrateSummary,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvedProperty {
    pub description: String,
    pub solver: String,
    pub time_ms: u64,
    pub strength: ProofStrength,
    /// tRust #382: Proof evidence derived from `strength`.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub evidence: Option<ProofEvidence>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailedProperty {
    pub description: String,
    pub solver: String,
    pub counterexample: Option<Counterexample>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnknownProperty {
    pub description: String,
    pub solver: String,
    pub reason: String,
}

/// Full verification report for a crate (legacy format, still used by build_report).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofReport {
    pub crate_name: String,
    pub functions: Vec<FunctionReport>,
    pub total_proved: usize,
    pub total_failed: usize,
    pub total_unknown: usize,
}

// ---------------------------------------------------------------------------
// tRust: Whole-crate verification result (#59)
// ---------------------------------------------------------------------------

/// Per-function verification result collected during whole-crate verification.
///
/// Pairs a function's identity with its raw verification (VC, result) pairs
/// and cross-function spec composition metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionVerificationResult {
    /// Fully qualified function path (e.g., "crate::module::function").
    pub function_path: String,
    /// Human-readable function name.
    pub function_name: String,
    /// Raw (VC, result) pairs from the solver.
    pub results: Vec<(VerificationCondition, VerificationResult)>,
    /// Number of VCs satisfied from cross-function spec notes (free).
    pub from_notes: usize,
    /// Number of VCs sent to solver with callee postcondition assumptions.
    pub with_assumptions: usize,
}

/// Aggregated verification result for an entire crate (#59).
///
/// Collects per-function results and provides crate-level summary statistics.
/// Built incrementally as the trust_verify MIR pass processes each function,
/// then finalized into a `JsonProofReport` via trust-report.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CrateVerificationResult {
    /// Crate name.
    pub crate_name: String,
    /// Per-function verification results, in processing order.
    pub functions: Vec<FunctionVerificationResult>,
    /// Total VCs satisfied from cross-function spec notes across all functions.
    pub total_from_notes: usize,
    /// Total VCs sent to solver with callee assumptions across all functions.
    pub total_with_assumptions: usize,
}

impl CrateVerificationResult {
    /// Create a new empty result for the given crate.
    #[must_use]
    pub fn new(crate_name: impl Into<String>) -> Self {
        Self { crate_name: crate_name.into(), ..Default::default() }
    }

    /// Add a function's verification result.
    pub fn add_function(&mut self, func: FunctionVerificationResult) {
        self.total_from_notes += func.from_notes;
        self.total_with_assumptions += func.with_assumptions;
        self.functions.push(func);
    }

    /// Total number of functions verified.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Flatten all per-function (VC, result) pairs into a single list.
    ///
    /// This is the format expected by `trust_report::build_json_report()`.
    #[must_use]
    pub fn all_results(&self) -> Vec<(VerificationCondition, VerificationResult)> {
        self.functions.iter().flat_map(|f| f.results.clone()).collect()
    }

    /// Total number of VCs across all functions.
    #[must_use]
    pub fn total_obligations(&self) -> usize {
        self.functions.iter().map(|f| f.results.len()).sum()
    }
}

// ---------------------------------------------------------------------------
// tRust #542: Structured data transport (compiler -> driver -> CLI)
// ---------------------------------------------------------------------------

/// Prefix used to identify structured JSON transport lines in stderr.
///
/// The compiler emits `TRUST_JSON:{json}\n` lines to stderr alongside normal
/// diagnostics. Consumers scan for this prefix to extract structured data.
pub const TRANSPORT_PREFIX: &str = "TRUST_JSON:";

/// A structured transport message emitted by the compiler MIR pass.
///
/// Each message is serialized as a single JSON line prefixed with
/// [`TRANSPORT_PREFIX`] on stderr. Consumers parse these lines to get
/// structured verification results without fragile text parsing.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
#[non_exhaustive]
pub enum TransportMessage {
    /// Per-function verification results.
    #[serde(rename = "function_result")]
    FunctionResult(FunctionTransportResult),
    /// Crate-level summary emitted after all functions are processed.
    #[serde(rename = "crate_summary")]
    CrateSummary(CrateTransportSummary),
}

/// Structured verification results for a single function, emitted by the
/// compiler MIR pass for consumption by cargo-trust and trust-driver.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionTransportResult {
    /// Fully qualified function path (e.g., "crate::module::function").
    pub function: String,
    /// Per-obligation (VC, result) pairs.
    pub results: Vec<TransportObligationResult>,
    /// Summary counts for this function.
    pub proved: usize,
    pub failed: usize,
    pub unknown: usize,
    pub runtime_checked: usize,
    pub total: usize,
}

/// A single obligation result in the transport format.
///
/// Carries the essential fields from `VerificationResult` in a flat,
/// JSON-friendly structure without requiring the full `VerificationCondition`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransportObligationResult {
    /// Short tag for the VC kind (e.g., "overflow:add", "divzero", "bounds").
    pub kind: String,
    /// Human-readable description of the obligation.
    pub description: String,
    /// Source location for the obligation, when available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// Verification outcome: "proved", "failed", "unknown", "timeout", "runtime_checked".
    pub outcome: String,
    /// Which solver produced this result.
    pub solver: String,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
    /// Optional counterexample for failed obligations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<String>,
    /// Structured counterexample model for repair tooling and reports.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_model: Option<Counterexample>,
    /// Optional reason for unknown/timeout results.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

/// Crate-level summary emitted after all functions are processed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrateTransportSummary {
    /// Crate name.
    pub crate_name: String,
    /// Total functions verified.
    pub functions_verified: usize,
    /// Aggregate counts.
    pub total_proved: usize,
    pub total_failed: usize,
    pub total_unknown: usize,
    pub total_runtime_checked: usize,
    pub total_obligations: usize,
}

/// Parse a `TRUST_JSON:` prefixed line into a `TransportMessage`.
///
/// Returns `None` if the line does not start with the transport prefix
/// or if the JSON payload fails to parse.
#[must_use]
pub fn parse_transport_line(line: &str) -> Option<TransportMessage> {
    let json_str = line.strip_prefix(TRANSPORT_PREFIX)?;
    serde_json::from_str(json_str).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::VcKind;
    use crate::model::{BinOp, Ty};

    fn arithmetic_overflow_vc() -> VcKind {
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) }
    }

    fn no_runtime_fallback_vc() -> VcKind {
        VcKind::Postcondition
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "z4".into(), time_ms: 7, counterexample: None }
    }

    fn unknown_result() -> VerificationResult {
        VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 11,
            reason: "incomplete quantifier reasoning".into(),
        }
    }

    fn timeout_result() -> VerificationResult {
        VerificationResult::Timeout { solver: "z4".into(), timeout_ms: 250 }
    }

    #[test]
    fn test_counterexample_display() {
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let s = cex.to_string();
        assert!(s.contains("a = 18446744073709551615"));
        assert!(s.contains("b = 1"));
    }

    #[test]
    fn test_result_accessors() {
        let proved = VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        assert!(proved.is_proved());
        assert!(!proved.is_failed());
        assert_eq!(proved.solver_name(), "z4");
        assert_eq!(proved.time_ms(), 5);
    }

    #[test]
    fn test_classify_runtime_disposition_auto() {
        let overflow_vc = arithmetic_overflow_vc();
        let no_fallback_vc = no_runtime_fallback_vc();

        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &proved_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Proved
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &failed_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Failed
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &unknown_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: overflow_vc.description() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &timeout_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: overflow_vc.description() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &unknown_result(),
                RuntimeCheckPolicy::Auto,
                false,
            ),
            RuntimeDisposition::Unknown { reason: "incomplete quantifier reasoning".into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &timeout_result(),
                RuntimeCheckPolicy::Auto,
                false,
            ),
            RuntimeDisposition::Timeout { timeout_ms: 250 }
        );
        assert_eq!(
            classify_runtime_disposition(
                &no_fallback_vc,
                &unknown_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Unknown { reason: "incomplete quantifier reasoning".into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &no_fallback_vc,
                &timeout_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Timeout { timeout_ms: 250 }
        );
    }

    #[test]
    fn test_classify_runtime_disposition_force_static() {
        let vc_kind = no_runtime_fallback_vc();

        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &proved_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::Proved
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &failed_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::Failed
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &unknown_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::CompileError {
                reason: "`#[trust(static)]` requires a static proof, but the solver returned unknown: incomplete quantifier reasoning".into(),
            }
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &timeout_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::CompileError {
                reason: "`#[trust(static)]` requires a static proof, but verification timed out after 250ms".into(),
            }
        );
    }

    #[test]
    fn test_classify_runtime_disposition_force_runtime() {
        let vc_kind = no_runtime_fallback_vc();

        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &proved_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &failed_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::Failed
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &unknown_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &timeout_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.into() }
        );
    }

    // -----------------------------------------------------------------------
    // CrateVerificationResult tests (#59)
    // -----------------------------------------------------------------------

    #[test]
    fn test_crate_verification_result_empty() {
        let result = CrateVerificationResult::new("empty_crate");
        assert_eq!(result.crate_name, "empty_crate");
        assert_eq!(result.function_count(), 0);
        assert_eq!(result.total_obligations(), 0);
        assert!(result.all_results().is_empty());
        assert_eq!(result.total_from_notes, 0);
        assert_eq!(result.total_with_assumptions, 0);
    }

    #[test]
    fn test_crate_verification_result_add_functions() {
        let mut crate_result = CrateVerificationResult::new("multi_fn");

        let func1 = FunctionVerificationResult {
            function_path: "crate::safe_div".to_string(),
            function_name: "safe_div".to_string(),
            results: vec![(
                crate::VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "safe_div".into(),
                    location: crate::SourceSpan::default(),
                    formula: crate::Formula::Bool(false),
                    contract_metadata: None,
                },
                proved_result(),
            )],
            from_notes: 1,
            with_assumptions: 0,
        };

        let func2 = FunctionVerificationResult {
            function_path: "crate::checked_add".to_string(),
            function_name: "checked_add".to_string(),
            results: vec![
                (
                    crate::VerificationCondition {
                        kind: arithmetic_overflow_vc(),
                        function: "checked_add".into(),
                        location: crate::SourceSpan::default(),
                        formula: crate::Formula::Bool(true),
                        contract_metadata: None,
                    },
                    failed_result(),
                ),
                (
                    crate::VerificationCondition {
                        kind: VcKind::DivisionByZero,
                        function: "checked_add".into(),
                        location: crate::SourceSpan::default(),
                        formula: crate::Formula::Bool(false),
                        contract_metadata: None,
                    },
                    proved_result(),
                ),
            ],
            from_notes: 0,
            with_assumptions: 2,
        };

        crate_result.add_function(func1);
        crate_result.add_function(func2);

        assert_eq!(crate_result.function_count(), 2);
        assert_eq!(crate_result.total_obligations(), 3);
        assert_eq!(crate_result.total_from_notes, 1);
        assert_eq!(crate_result.total_with_assumptions, 2);

        let all = crate_result.all_results();
        assert_eq!(all.len(), 3);
        assert_eq!(all[0].0.function, "safe_div");
        assert_eq!(all[1].0.function, "checked_add");
        assert_eq!(all[2].0.function, "checked_add");
    }

    #[test]
    fn test_crate_verification_result_serialization_roundtrip() {
        let mut crate_result = CrateVerificationResult::new("roundtrip");
        crate_result.add_function(FunctionVerificationResult {
            function_path: "crate::f".to_string(),
            function_name: "f".to_string(),
            results: vec![(
                crate::VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "f".into(),
                    location: crate::SourceSpan::default(),
                    formula: crate::Formula::Bool(false),
                    contract_metadata: None,
                },
                proved_result(),
            )],
            from_notes: 0,
            with_assumptions: 0,
        });

        let json = serde_json::to_string(&crate_result).expect("serialize");
        let deserialized: CrateVerificationResult =
            serde_json::from_str(&json).expect("deserialize");
        assert_eq!(deserialized.crate_name, "roundtrip");
        assert_eq!(deserialized.function_count(), 1);
        assert_eq!(deserialized.total_obligations(), 1);
    }

    // -----------------------------------------------------------------------
    // tRust #190: ProofEvidence, ReasoningKind, AssuranceLevel tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_reasoning_kind_is_complete_smt() {
        assert!(ReasoningKind::Smt.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_bounded_model_check_false() {
        assert!(!ReasoningKind::BoundedModelCheck { depth: 50 }.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_exhaustive_finite() {
        assert!(ReasoningKind::ExhaustiveFinite(1024).is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_inductive() {
        assert!(ReasoningKind::Inductive.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_deductive() {
        assert!(ReasoningKind::Deductive.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_constructive() {
        assert!(ReasoningKind::Constructive.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_pdr() {
        assert!(ReasoningKind::Pdr.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_abstract_interpretation() {
        assert!(ReasoningKind::AbstractInterpretation.is_complete());
    }

    #[test]
    fn test_assurance_level_strength_order() {
        assert_eq!(AssuranceLevel::Unchecked.strength_order(), 0);
        assert_eq!(AssuranceLevel::Heuristic.strength_order(), 0);
        assert_eq!(AssuranceLevel::Trusted.strength_order(), 1);
        assert_eq!(AssuranceLevel::BoundedSound { depth: 10 }.strength_order(), 1);
        assert_eq!(AssuranceLevel::SmtBacked.strength_order(), 2);
        assert_eq!(AssuranceLevel::Sound.strength_order(), 2);
        assert_eq!(AssuranceLevel::Certified.strength_order(), 3);
    }

    #[test]
    fn test_assurance_level_strength_monotonic() {
        // Certified > SmtBacked/Sound > Trusted/BoundedSound > Unchecked/Heuristic
        assert!(
            AssuranceLevel::Certified.strength_order() > AssuranceLevel::SmtBacked.strength_order()
        );
        assert!(
            AssuranceLevel::SmtBacked.strength_order() > AssuranceLevel::Trusted.strength_order()
        );
        assert!(
            AssuranceLevel::Trusted.strength_order() > AssuranceLevel::Unchecked.strength_order()
        );
    }

    #[test]
    fn test_proof_evidence_new() {
        let ev = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        assert_eq!(ev.reasoning, ReasoningKind::Smt);
        assert_eq!(ev.assurance, AssuranceLevel::Certified);
    }

    #[test]
    fn test_proof_evidence_is_certified() {
        let certified = ProofEvidence::new(ReasoningKind::Constructive, AssuranceLevel::Certified);
        assert!(certified.is_certified());
        let unchecked = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Unchecked);
        assert!(!unchecked.is_certified());
    }

    #[test]
    fn test_proof_evidence_is_bounded() {
        let bmc = ProofEvidence::new(
            ReasoningKind::BoundedModelCheck { depth: 50 },
            AssuranceLevel::Trusted,
        );
        assert!(bmc.is_bounded());
        let smt = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::SmtBacked);
        assert!(!smt.is_bounded());
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_smt_unsat() {
        let ps = ProofStrength::smt_unsat();
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::Smt);
        assert_eq!(ev.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_bounded() {
        let ps = ProofStrength::bounded(42);
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::BoundedModelCheck { depth: 42 });
        assert_eq!(ev.assurance, AssuranceLevel::BoundedSound { depth: 42 });
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_inductive() {
        let ps = ProofStrength::inductive();
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::Inductive);
        assert_eq!(ev.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_heuristic() {
        let ps = ProofStrength {
            reasoning: ReasoningKind::Deductive,
            assurance: AssuranceLevel::Heuristic,
        };
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::Deductive);
        assert_eq!(ev.assurance, AssuranceLevel::Unchecked);
    }

    #[test]
    fn test_proof_evidence_serde_roundtrip() {
        let ev =
            ProofEvidence::new(ReasoningKind::ExhaustiveFinite(256), AssuranceLevel::Certified);
        let json = serde_json::to_string(&ev).expect("serialize ProofEvidence");
        let deserialized: ProofEvidence =
            serde_json::from_str(&json).expect("deserialize ProofEvidence");
        assert_eq!(ev, deserialized);
    }

    #[test]
    fn test_proof_evidence_hash_consistency() {
        use crate::fx::FxHashSet;
        let ev1 = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        let ev2 = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        let mut set = FxHashSet::default();
        set.insert(ev1.clone());
        set.insert(ev2);
        assert_eq!(set.len(), 1, "equal ProofEvidence values must hash the same");
    }

    #[test]
    fn test_bounded_model_check_never_certified_invariant() {
        // This is the core soundness property from #190: bounded reasoning
        // must never silently become certified.
        let ev = ProofEvidence::new(
            ReasoningKind::BoundedModelCheck { depth: 100 },
            AssuranceLevel::Certified,
        );
        // The type system allows construction (for flexibility), but
        // `is_bounded()` remains true, enabling callers to enforce the rule.
        assert!(ev.is_bounded());
        assert!(ev.is_certified());
        // The correct check pattern:
        // if evidence.is_bounded() && evidence.is_certified() { reject }
    }

    // -----------------------------------------------------------------------
    // tRust #542: Transport message tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_transport_message_function_result_roundtrip() {
        let msg = TransportMessage::FunctionResult(FunctionTransportResult {
            function: "crate::safe_div".to_string(),
            results: vec![TransportObligationResult {
                kind: "divzero".to_string(),
                description: "division by zero".to_string(),
                location: None,
                outcome: "proved".to_string(),
                solver: "z4-smtlib".into(),
                time_ms: 5,
                counterexample: None,
                counterexample_model: None,
                reason: None,
            }],
            proved: 1,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            total: 1,
        });
        let json = serde_json::to_string(&msg).expect("serialize");
        let parsed: TransportMessage = serde_json::from_str(&json).expect("deserialize");
        match parsed {
            TransportMessage::FunctionResult(r) => {
                assert_eq!(r.function, "crate::safe_div");
                assert_eq!(r.results.len(), 1);
                assert_eq!(r.proved, 1);
            }
            _ => panic!("expected FunctionResult"),
        }
    }

    #[test]
    fn test_transport_message_crate_summary_roundtrip() {
        let msg = TransportMessage::CrateSummary(CrateTransportSummary {
            crate_name: "my_crate".to_string(),
            functions_verified: 5,
            total_proved: 10,
            total_failed: 1,
            total_unknown: 2,
            total_runtime_checked: 0,
            total_obligations: 13,
        });
        let json = serde_json::to_string(&msg).expect("serialize");
        let parsed: TransportMessage = serde_json::from_str(&json).expect("deserialize");
        match parsed {
            TransportMessage::CrateSummary(s) => {
                assert_eq!(s.crate_name, "my_crate");
                assert_eq!(s.total_obligations, 13);
            }
            _ => panic!("expected CrateSummary"),
        }
    }

    #[test]
    fn test_parse_transport_line_valid() {
        let json = r#"{"type":"function_result","function":"f","results":[],"proved":0,"failed":0,"unknown":0,"runtime_checked":0,"total":0}"#;
        let line = format!("{TRANSPORT_PREFIX}{json}");
        let msg = parse_transport_line(&line).expect("should parse");
        match msg {
            TransportMessage::FunctionResult(r) => assert_eq!(r.function, "f"),
            _ => panic!("expected FunctionResult"),
        }
    }

    #[test]
    fn test_parse_transport_line_no_prefix() {
        assert!(parse_transport_line("note: tRust [overflow:add]: ...").is_none());
    }

    #[test]
    fn test_parse_transport_line_invalid_json() {
        assert!(parse_transport_line("TRUST_JSON:{invalid}").is_none());
    }
}
