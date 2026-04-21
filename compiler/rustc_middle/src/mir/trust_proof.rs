// tRust: Proof-carrying MIR type definitions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
//
// Per-function verification results accessible via compiler query.
// Design: designs/2026-03-27-proof-carrying-mir.md
//
// Hot/cold split:
//   TrustProofResults  — semantic facts, deterministic, HashStable, drives codegen
//   TrustProofTelemetry — solver timings, counterexamples, NOT hashable
//
// Key decisions:
//   - Query keyed by ty::InstanceKind (follows coverage_ids_info pattern)
//   - ObligationId is a newtype index with 128-bit Fingerprint for stable identity
//   - arena_cache: provider returns Option<T> (owned), query system arenas automatically
//   - Vec<T> → &'tcx [T] for arena safety (arenas don't call Drop)
//   - Only lean5-Certified results permit codegen check elision

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_index::IndexVec;
use rustc_macros::{HashStable, TyDecodable, TyEncodable};
use rustc_span::Symbol;

// ---------------------------------------------------------------------------
// tRust: ObligationId — stable proof obligation identity
// ---------------------------------------------------------------------------

rustc_index::newtype_index! {
    /// tRust: Index into per-function obligation arrays.
    ///
    /// Each obligation gets a dense index for O(1) codegen lookup via IndexVec.
    /// The canonical identity is the VC fingerprint (see `TrustObligationFingerprint`),
    /// but ObligationId is the fast runtime key.
    #[stable_hash]
    #[encodable]
    #[orderable]
    #[debug_format = "ObligationId({})"]
    pub struct ObligationId {}
}

// ---------------------------------------------------------------------------
// tRust: Semantic proof results (HOT path — drives codegen)
// ---------------------------------------------------------------------------

/// tRust: Per-function verification results. Arena-allocated, returned by query.
///
/// This is the canonical proof data that flows through the compiler.
/// Codegen reads `dispositions` to skip runtime checks (only if `Certified`).
/// Reporting reads `summary` for JSON output.
///
/// Keyed by `ty::InstanceKind` in the query (follows `coverage_ids_info` pattern).
/// Provider returns `Option<TrustProofResults>` (owned); `arena_cache` handles allocation.
#[derive(Clone, Debug, TyEncodable, TyDecodable, HashStable)]
pub struct TrustProofResults {
    /// tRust: Dense per-obligation dispositions for O(1) codegen lookup.
    /// Indexed by `ObligationId`.
    pub dispositions: IndexVec<ObligationId, TrustDisposition>,

    // tRust: NOTE — Location→ObligationId mapping is NOT stored here.
    // Location doesn't derive TyEncodable/TyDecodable (and it's fragile — shifts
    // during inlining). The location_map is computed at query time from the MIR
    // body and cached separately. See designs/2026-03-27-proof-carrying-mir.md
    // §"CRITICAL: Replace Location with Stable ObligationId".
    /// tRust: 128-bit fingerprint per obligation for cross-compilation stability.
    /// Indexed by `ObligationId`. Computed structurally over the logical VC formula,
    /// NOT over MIR locations (which shift during optimization).
    pub fingerprints: IndexVec<ObligationId, Fingerprint>,

    /// tRust: Function-level summary statistics.
    pub summary: TrustFunctionSummary,
}

impl TrustProofResults {
    /// tRust: Lookup a per-obligation disposition by dense obligation index.
    #[must_use]
    pub fn disposition(&self, obligation: ObligationId) -> Option<TrustDisposition> {
        self.dispositions.get(obligation).copied()
    }

    /// tRust: Returns true when every obligation is statically discharged.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.summary.failed == 0 && self.summary.unknown == 0 && self.summary.runtime_checked == 0
    }

    /// tRust: Returns true when any obligation falls back to a runtime check.
    #[must_use]
    pub fn has_runtime_checks(&self) -> bool {
        self.summary.runtime_checked > 0
    }
}

/// tRust: Per-obligation codegen disposition. The hot-path type.
///
/// 8 bytes or less. Copy. This is what codegen reads at every checked operation.
/// If `status == Certified`, codegen can elide the runtime check.
/// If `status == Trusted`, the check stays but we report it as proved.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, HashStable)]
pub struct TrustDisposition {
    /// tRust: What property was checked.
    pub kind: TrustObligationKind,

    /// tRust: Proof status (Trusted/Certified/Failed/Unknown/RuntimeChecked).
    pub status: TrustStatus,

    /// tRust: How strong the proof is.
    pub strength: TrustProofStrength,

    /// tRust: Only true if lean5 kernel independently verified the certificate.
    /// This is the gate for codegen check elision.
    pub certified: bool,
}

// ---------------------------------------------------------------------------
// tRust: Telemetry / diagnostics (COLD path — reporting only)
// ---------------------------------------------------------------------------

/// tRust: Per-function diagnostic telemetry. Non-deterministic, NOT hashable.
///
/// Solver timings fluctuate with system load. Counterexamples may differ between
/// solver versions. This data drives reporting but MUST NOT affect incremental
/// compilation hashes (hence no `HashStable` derive).
///
/// Returned by a separate `trust_proof_telemetry` query with `no_hash` modifier.
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct TrustProofTelemetry {
    /// tRust: Per-obligation diagnostic details, indexed by ObligationId.
    pub details: IndexVec<ObligationId, TrustObligationDetail>,
}

impl TrustProofTelemetry {
    /// tRust: Lookup a diagnostic detail by dense obligation index.
    #[must_use]
    pub fn detail(&self, obligation: ObligationId) -> Option<&TrustObligationDetail> {
        self.details.get(obligation)
    }

    /// tRust: Iterate only over obligations that fell back to runtime checking.
    #[must_use]
    pub fn runtime_checked_details(
        &self,
    ) -> impl Iterator<Item = (ObligationId, &TrustObligationDetail)> {
        self.details.iter_enumerated().filter(|(_, detail)| detail.runtime_fallback.is_some())
    }

    /// tRust: Count obligations that were runtime-checked instead of statically proved.
    #[must_use]
    pub fn runtime_checked_count(&self) -> usize {
        self.runtime_checked_details().count()
    }
}

/// tRust: Diagnostic detail for a single obligation. Cold path.
///
/// Contains solver identity, timing, and counterexample data.
/// Not HashStable — timings are non-deterministic.
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct TrustObligationDetail {
    /// tRust: Which solver produced this result. Interned Symbol (4 bytes, Copy).
    pub solver: Symbol,

    /// tRust: Wall-clock time in microseconds (not milliseconds — sub-ms precision matters).
    /// z4 frequently returns in 100-300us.
    pub time_us: u64,

    /// tRust: Counterexample as (variable_name, value) pairs.
    /// Variable names are interned Symbols. Values are i128 (sufficient for
    /// all integer types up to 128-bit; floats encoded as bits).
    ///
    /// Empty vec means no counterexample (proved or unknown).
    /// For arena-allocated query results, this becomes `&'tcx [(Symbol, i128)]`.
    pub counterexample: Vec<(Symbol, i128)>,

    /// tRust: Structured runtime fallback metadata, if the obligation was
    /// checked dynamically because the solver could not discharge it.
    pub runtime_fallback: Option<TrustRuntimeFallback>,
}

/// tRust: Runtime fallback metadata for a verification obligation.
#[derive(Clone, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
pub struct TrustRuntimeFallback {
    /// tRust: Why the compiler fell back to runtime checking.
    pub reason: TrustRuntimeFallbackReason,

    /// tRust: Human-readable note explaining the fallback decision.
    pub note: String,
}

/// tRust: Machine-readable reason for a runtime fallback.
#[derive(Copy, Clone, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
pub enum TrustRuntimeFallbackReason {
    /// tRust: The solver returned `Unknown` and the compiler retained a check.
    Unknown,

    /// tRust: The solver timed out and the compiler retained a check.
    Timeout,
}

impl TrustObligationDetail {
    /// tRust: Returns true when this obligation was runtime-checked.
    #[must_use]
    pub fn is_runtime_checked(&self) -> bool {
        self.runtime_fallback.is_some()
    }

    /// tRust: Runtime fallback metadata, if the obligation was not statically proved.
    #[must_use]
    pub fn runtime_fallback(&self) -> Option<&TrustRuntimeFallback> {
        self.runtime_fallback.as_ref()
    }
}

// ---------------------------------------------------------------------------
// tRust: Proof status and strength enums
// ---------------------------------------------------------------------------

/// tRust: What the verification system concluded about an obligation.
///
/// Two-level trust model:
/// - `Trusted`: Solver says proved. Safe for diagnostics and reporting.
/// - `Certified`: lean5 kernel verified the proof certificate. Safe for codegen check elision.
///
/// Only `Certified` permits codegen to elide overflow/bounds checks. This keeps the
/// compiler TCB minimal: rustc + lean5 kernel.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, HashStable)]
pub enum TrustStatus {
    /// tRust: Solver says proved. Trusted but not independently verified.
    /// Safe for diagnostics, reporting, and advisory optimization hints.
    Trusted,

    /// tRust: Proof certificate verified by lean5 kernel.
    /// Safe for UB-relevant check elision in codegen.
    Certified,

    /// tRust: Counterexample found. Property violated.
    Failed,

    /// tRust: Solver could not determine (incomplete or resource-limited).
    Unknown,

    /// tRust: Solver timed out.
    Timeout,

    /// tRust: Runtime check inserted (unproved, but monitored).
    RuntimeChecked,
}

/// tRust: How strong the proof is.
///
/// Ordered roughly by increasing strength. Determines which proofs can
/// contribute to lean5 certification.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, HashStable)]
pub enum TrustProofStrength {
    /// tRust: No proof attempted or possible.
    None,

    /// tRust: Bounded model checking to depth k (zani).
    /// Sound up to k steps; does not guarantee absence of deeper bugs.
    Bounded {
        /// Maximum unwinding/exploration depth.
        depth: u32,
    },

    /// tRust: SMT solver returned UNSAT (z4).
    /// Sound for the encoded formula; soundness depends on encoding correctness.
    SmtUnsat,

    /// tRust: Inductive invariant found (sunder).
    Inductive,

    /// tRust: Deductive verification with pre/post (sunder).
    Deductive,

    /// tRust: Ownership/lifetime proof (certus).
    Ownership,

    /// tRust: Temporal property verified (tla2).
    Temporal,

    /// tRust: Neural network robustness bound (gamma-crown).
    /// Epsilon is fixed-point representation (multiply by 1e-9 for actual value).
    NeuralBound {
        /// Fixed-point epsilon (1e-9 scale).
        epsilon: u64,
    },

    /// tRust: Constructive proof term exists, checkable by lean5.
    /// This is the only strength that can produce `Certified` status.
    Constructive,
}

// ---------------------------------------------------------------------------
// tRust: Obligation kinds (what property was verified)
// ---------------------------------------------------------------------------

/// tRust: What kind of property was verified at this obligation.
///
/// Mirrors the VC kinds from trust-vcgen but uses compiler-internal types
/// (Symbol, no serde, no heap strings).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, HashStable)]
pub enum TrustObligationKind {
    /// tRust: Arithmetic overflow on a binary operation.
    ArithmeticOverflow(TrustBinOp),
    /// tRust: Division by zero.
    DivisionByZero,
    /// tRust: Remainder by zero.
    RemainderByZero,
    /// tRust: Array/slice index out of bounds.
    IndexOutOfBounds,
    /// tRust: Signed negation overflow (e.g., -i32::MIN).
    NegationOverflow,
    /// tRust: Shift amount exceeds bit width.
    ShiftOverflow,
    /// tRust: Cast truncation.
    CastOverflow,
    /// tRust: User assertion (`assert!`, `debug_assert!`).
    Assertion,
    /// tRust: Function precondition (`#[requires(...)]`).
    Precondition,
    /// tRust: Function postcondition (`#[ensures(...)]`).
    Postcondition,
    /// tRust: Unreachable code reached.
    Unreachable,
    /// tRust: Deadlock freedom (concurrent code).
    Deadlock,
    /// tRust: Temporal property (distributed protocols).
    Temporal,
    /// tRust: Liveness property (something good eventually happens).
    Liveness,
    /// tRust: Taint tracking violation (untrusted data flows to sensitive sink).
    TaintViolation,
    /// tRust: Refinement violation (implementation doesn't refine spec).
    RefinementViolation,
    /// tRust: Resilience violation (missing error handling path).
    ResilienceViolation,
    /// tRust: Protocol violation (message sequence violates protocol spec).
    ProtocolViolation,
    /// tRust: Non-termination (loop may not terminate).
    NonTermination,
}

/// tRust: Binary operations for overflow checking.
///
/// Copy, 1 byte — no heap allocation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, HashStable)]
pub enum TrustBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
}

// ---------------------------------------------------------------------------
// tRust: Function-level summary
// ---------------------------------------------------------------------------

/// tRust: Function-level proof summary. Computed once, cached in results.
///
/// These counts are deterministic (derived from dispositions, not timings).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, HashStable)]
pub struct TrustFunctionSummary {
    /// tRust: Total number of proof obligations.
    pub total: u32,
    /// tRust: Number with `Trusted` status (solver-proved, not lean5-certified).
    pub trusted: u32,
    /// tRust: Number with `Certified` status (lean5-verified).
    pub certified: u32,
    /// tRust: Number with counterexamples.
    pub failed: u32,
    /// tRust: Number unknown or timed out.
    pub unknown: u32,
    /// tRust: Number with runtime checks inserted.
    pub runtime_checked: u32,
    /// tRust: Highest proof level achieved for this function.
    pub max_level: TrustProofLevel,
}

impl TrustFunctionSummary {
    /// tRust: Returns true when the function has any unresolved obligations.
    #[must_use]
    pub fn has_unresolved(&self) -> bool {
        self.failed > 0 || self.unknown > 0 || self.runtime_checked > 0
    }

    /// tRust: Returns true when every obligation was discharged statically.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.total > 0 && !self.has_unresolved()
    }
}

/// tRust: Verification level achieved for a function.
///
/// Ordered: None < L0Safety < L1Functional < L2Domain.
/// This ordering is meaningful — Ord derive produces the correct comparison.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(TyEncodable, TyDecodable, HashStable)]
pub enum TrustProofLevel {
    /// tRust: No verification performed.
    None,
    /// tRust: L0: Safety (overflow, bounds, div-by-zero).
    L0Safety,
    /// tRust: L1: Functional correctness (pre/postconditions).
    L1Functional,
    /// tRust: L2: Domain properties (temporal, distributed).
    L2Domain,
}

// ---------------------------------------------------------------------------
// tRust: Proof certificate for lean5 kernel verification
// ---------------------------------------------------------------------------

/// tRust: Proof certificate for lean5 kernel verification.
///
/// The certificate contains:
/// 1. A serialized lean5 proof term (opaque to the compiler)
/// 2. A fingerprint of the canonical VC (for staleness detection)
/// 3. The serialized canonical VC itself (for lean5 to check against)
///
/// Cross-crate: serialized into `.rmeta` for downstream consumption.
///
/// Note: `proof_term` and `canonical_vc` use `Vec<u8>` in the owned form.
/// When returned from an arena_cache query, these become `&'tcx [u8]`.
/// The query arena (typed arena path) handles Drop correctly for Vec.
#[derive(Clone, Debug, TyEncodable, TyDecodable, HashStable)]
pub struct TrustProofCertificate {
    /// tRust: Which prover generated this certificate.
    pub prover: Symbol,

    /// tRust: Serialized lean5 proof term. Opaque to the compiler.
    /// lean5 deserializes and type-checks this independently.
    pub proof_term: Vec<u8>,

    /// tRust: 128-bit Fingerprint of the canonical VC (logical formula).
    /// Computed structurally over the VC, not over MIR locations.
    /// Used to detect stale certificates after code changes.
    pub vc_fingerprint: Fingerprint,

    /// tRust: Serialized canonical VC for lean5 to check against.
    /// lean5 needs the exact theorem statement to verify — a hash alone is insufficient.
    pub canonical_vc: Vec<u8>,

    /// tRust: Prover version string for reproducibility.
    pub prover_version: Symbol,
}
