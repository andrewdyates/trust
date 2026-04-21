// trust-router/sunder_backend.rs: Sunder deductive verification backend
//
// tRust #632: Phase 1 native integration using sunder-core's PureExpr and
// SmtGenerator. Translates trust-types Formula to sunder-core PureExpr,
// generates SMT-LIB2 via sunder-core's encoder, and verifies via an SMT
// solver subprocess.
//
// tRust #798: The SunderBackend struct (subprocess-based) is feature-gated
// behind `not(pipeline-v2)` -- Pipeline v2 uses trust-sunder-lib for direct
// library calls. Classification logic (classify_for_sunder, sunder_affinity,
// is_deductive_vc_kind) is always available regardless of feature flags.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::classifier::{self, QueryClass};
#[cfg(not(feature = "pipeline-v2"))]
use crate::{BackendRole, VerificationBackend};

#[cfg(all(feature = "sunder-backend", not(feature = "pipeline-v2")))]
use trust_types::sunder_bridge::translate_formulas;

// ---------------------------------------------------------------------------
// tRust #632: Formula -> PureExpr translation (requires sunder-backend feature)
// tRust #798: Also gated behind not(pipeline-v2) -- Pipeline v2 uses
// trust-sunder-lib directly instead of translating through this module.
// ---------------------------------------------------------------------------

#[cfg(all(feature = "sunder-backend", not(feature = "pipeline-v2")))]
pub(crate) mod translate {
    use std::sync::Arc;

    use sunder_core::formula::{BinOp as SBinOp, ExprSort, PureExpr, UnOp as SUnOp};
    use trust_types::{Formula, Sort};

    /// Convert a trust-types Sort to a sunder-core ExprSort.
    ///
    /// Returns `None` for sorts that sunder cannot represent (BitVec, Array).
    pub fn sort_to_expr_sort(sort: &Sort) -> Option<ExprSort> {
        match sort {
            Sort::Bool => Some(ExprSort::Bool),
            Sort::Int => Some(ExprSort::Int),
            Sort::BitVec(_) => None,
            Sort::Array(_, _) => None,
            _ => None, // non-exhaustive future variants
        }
    }

    /// Convert a trust-types Formula to a sunder-core PureExpr.
    ///
    /// Returns `None` if the formula contains constructs that sunder cannot
    /// handle (bitvectors, array theory, integer constants exceeding i64 range).
    /// The caller should fall back to another backend.
    pub fn formula_to_pure_expr(formula: &Formula) -> Option<PureExpr> {
        match formula {
            Formula::Bool(b) => Some(PureExpr::Bool(*b)),

            Formula::Int(n) => {
                // tRust #632: sunder-core uses i64 for integer literals
                let val = i64::try_from(*n).ok()?;
                Some(PureExpr::Int(val))
            }

            Formula::UInt(n) => {
                // Convert to i64 with range check
                let val = i64::try_from(*n).ok()?;
                Some(PureExpr::Int(val))
            }

            Formula::Var(name, sort) => {
                let expr_sort = sort_to_expr_sort(sort);
                Some(PureExpr::Var(name.clone(), expr_sort))
            }

            // Boolean connectives
            Formula::Not(inner) => {
                let e = formula_to_pure_expr(inner)?;
                Some(PureExpr::UnOp(SUnOp::Not, Arc::new(e)))
            }

            Formula::And(terms) => {
                if terms.is_empty() {
                    return Some(PureExpr::Bool(true));
                }
                let mut result = formula_to_pure_expr(&terms[0])?;
                for term in &terms[1..] {
                    let right = formula_to_pure_expr(term)?;
                    result =
                        PureExpr::BinOp(Arc::new(result), SBinOp::And, Arc::new(right));
                }
                Some(result)
            }

            Formula::Or(terms) => {
                if terms.is_empty() {
                    return Some(PureExpr::Bool(false));
                }
                let mut result = formula_to_pure_expr(&terms[0])?;
                for term in &terms[1..] {
                    let right = formula_to_pure_expr(term)?;
                    result =
                        PureExpr::BinOp(Arc::new(result), SBinOp::Or, Arc::new(right));
                }
                Some(result)
            }

            Formula::Implies(a, b) => {
                let left = formula_to_pure_expr(a)?;
                let right = formula_to_pure_expr(b)?;
                Some(PureExpr::BinOp(
                    Arc::new(left),
                    SBinOp::Implies,
                    Arc::new(right),
                ))
            }

            // Comparisons
            Formula::Eq(a, b) => bin_op(a, b, SBinOp::Eq),
            Formula::Lt(a, b) => bin_op(a, b, SBinOp::Lt),
            Formula::Le(a, b) => bin_op(a, b, SBinOp::Le),
            Formula::Gt(a, b) => bin_op(a, b, SBinOp::Gt),
            Formula::Ge(a, b) => bin_op(a, b, SBinOp::Ge),

            // Arithmetic
            Formula::Add(a, b) => bin_op(a, b, SBinOp::Add),
            Formula::Sub(a, b) => bin_op(a, b, SBinOp::Sub),
            Formula::Mul(a, b) => bin_op(a, b, SBinOp::Mul),
            Formula::Div(a, b) => bin_op(a, b, SBinOp::Div),
            Formula::Rem(a, b) => bin_op(a, b, SBinOp::Mod),

            Formula::Neg(inner) => {
                let e = formula_to_pure_expr(inner)?;
                Some(PureExpr::UnOp(SUnOp::Neg, Arc::new(e)))
            }

            // Conditional
            Formula::Ite(cond, then, els) => {
                let c = formula_to_pure_expr(cond)?;
                let t = formula_to_pure_expr(then)?;
                let e = formula_to_pure_expr(els)?;
                Some(PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e)))
            }

            // Quantifiers
            Formula::Forall(bindings, body) => {
                let body_expr = formula_to_pure_expr(body)?;
                // tRust #632: Nest quantifiers — forall x, y. P => forall x. forall y. P
                let mut result = body_expr;
                for (name, sort) in bindings.iter().rev() {
                    let var_sort = sort_to_expr_sort(sort);
                    result = PureExpr::Forall {
                        var: name.clone(),
                        var_sort,
                        body: Arc::new(result),
                        triggers: Vec::new(),
                    };
                }
                Some(result)
            }

            Formula::Exists(bindings, body) => {
                let body_expr = formula_to_pure_expr(body)?;
                let mut result = body_expr;
                for (name, sort) in bindings.iter().rev() {
                    let var_sort = sort_to_expr_sort(sort);
                    result = PureExpr::Exists {
                        var: name.clone(),
                        var_sort,
                        body: Arc::new(result),
                        triggers: Vec::new(),
                    };
                }
                Some(result)
            }

            // Bitvector operations — not supported by sunder
            Formula::BitVec { .. }
            | Formula::BvAdd(..)
            | Formula::BvSub(..)
            | Formula::BvMul(..)
            | Formula::BvUDiv(..)
            | Formula::BvSDiv(..)
            | Formula::BvURem(..)
            | Formula::BvSRem(..)
            | Formula::BvAnd(..)
            | Formula::BvOr(..)
            | Formula::BvXor(..)
            | Formula::BvNot(..)
            | Formula::BvShl(..)
            | Formula::BvLShr(..)
            | Formula::BvAShr(..)
            | Formula::BvULt(..)
            | Formula::BvULe(..)
            | Formula::BvSLt(..)
            | Formula::BvSLe(..)
            | Formula::BvToInt(..)
            | Formula::IntToBv(..)
            | Formula::BvExtract { .. }
            | Formula::BvConcat(..)
            | Formula::BvZeroExt(..)
            | Formula::BvSignExt(..) => None,

            // Array theory — not supported initially
            Formula::Select(..) | Formula::Store(..) => None,

            // Non-exhaustive future variants
            _ => None,
        }
    }

    /// Helper: translate a binary operation.
    fn bin_op(a: &Formula, b: &Formula, op: SBinOp) -> Option<PureExpr> {
        let left = formula_to_pure_expr(a)?;
        let right = formula_to_pure_expr(b)?;
        Some(PureExpr::BinOp(Arc::new(left), op, Arc::new(right)))
    }

    /// Check if a formula is translatable to PureExpr without actually translating.
    ///
    /// tRust #652: Uses cheap structural checks instead of O(n) full translation.
    /// Walks the formula tree once checking for unsupported constructs (bitvectors,
    /// arrays, large integers) without allocating any PureExpr nodes.
    pub fn is_translatable(formula: &Formula) -> bool {
        // Cheap reject: bitvectors are never translatable
        if formula.has_bitvectors() {
            return false;
        }
        // Cheap reject: array theory not supported
        if formula.has_arrays() {
            return false;
        }
        // Cheap reject: integer literals outside i64 range
        if formula.has_large_integers() {
            return false;
        }
        // All known untranslatable constructs have been checked structurally.
        // Formulas containing only Bool, Int (i64-range), UInt (i64-range),
        // Var, boolean connectives, comparisons, arithmetic, Ite, and
        // quantifiers are translatable.
        true
    }
}

// ---------------------------------------------------------------------------
// tRust #632: SMT-LIB2 generation and subprocess execution (sunder-backend)
// ---------------------------------------------------------------------------

// tRust #798: smt_verify also gated behind not(pipeline-v2) since it's only
// used by SunderBackend's subprocess-based verify path.
#[cfg(all(feature = "sunder-backend", not(feature = "pipeline-v2")))]
mod smt_verify {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use sunder_core::formula::PureExpr;
    use sunder_core::smt::SmtGenerator;
    use trust_types::{ProofStrength, VerificationResult};

    /// Generate a complete SMT-LIB2 verification query from a PureExpr.
    ///
    /// Uses sunder-core's SmtGenerator for correct sort inference and encoding.
    /// Strategy: assert NOT(expr) and check-sat. UNSAT => property holds.
    pub(crate) fn generate_smt_query(function_name: &str, ensures: &[PureExpr]) -> String {
        let mut smt_gen = SmtGenerator::new();
        smt_gen.generate_vc(function_name, &[], ensures, None);
        smt_gen.into_output()
    }

    /// tRust #653: Generate a structured SMT-LIB2 query with separate requires/ensures.
    ///
    /// Unlike `generate_smt_query` which treats the entire formula as a single
    /// ensures clause, this passes preconditions as `requires` and postconditions
    /// as `ensures`. The SmtGenerator handles negation internally:
    /// - Asserts each requires clause positively
    /// - Asserts NOT(ensures) and checks satisfiability
    /// - UNSAT means postconditions hold given preconditions
    pub(crate) fn generate_smt_query_structured(
        function_name: &str,
        requires: &[PureExpr],
        ensures: &[PureExpr],
    ) -> String {
        let mut smt_gen = SmtGenerator::new();
        smt_gen.generate_vc(function_name, requires, ensures, None);
        smt_gen.into_output()
    }

    /// Run an SMT-LIB2 query via a z4 subprocess and return a VerificationResult.
    ///
    /// tRust #632: The sunder backend uses sunder-core for formula encoding but
    /// delegates satisfiability checking to z4 as a subprocess. This avoids
    /// the z4 crate dependency conflict while using sunder's superior encoding.
    pub(crate) fn run_smt_and_map(
        smt_query: &str,
        function_name: &str,
        timeout_ms: u64,
    ) -> VerificationResult {
        let start = std::time::Instant::now();

        // Try z4 first, fall back to z3
        let solver_path = std::env::var("SUNDER_SOLVER_PATH")
            .or_else(|_| std::env::var("Z4_PATH"))
            .unwrap_or_else(|_| "z4".to_string());

        let child = Command::new(&solver_path)
            .args(["-smt2", "-in"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn();

        let mut child = match child {
            Ok(c) => c,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "sunder".to_string(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: format!("failed to spawn solver {solver_path}: {e}"),
                };
            }
        };

        if let Some(mut stdin) = child.stdin.take() {
            let _ = stdin.write_all(smt_query.as_bytes());
        }

        let output = match child.wait_with_output() {
            Ok(o) => o,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "sunder".to_string(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: format!("solver process error: {e}"),
                };
            }
        };

        let elapsed = start.elapsed().as_millis() as u64;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let trimmed = stdout.trim();

        if trimmed.starts_with("unsat") {
            // tRust #632: Genuine deductive proof via sunder encoding
            VerificationResult::Proved {
                solver: "sunder".to_string(),
                time_ms: elapsed,
                strength: ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
            }
        } else if trimmed.starts_with("sat") {
            VerificationResult::Failed {
                solver: "sunder".to_string(),
                time_ms: elapsed,
                counterexample: None, // Counterexample parsing not yet implemented
            }
        } else if elapsed >= timeout_ms {
            VerificationResult::Timeout {
                solver: "sunder".to_string(),
                timeout_ms,
            }
        } else {
            VerificationResult::Unknown {
                solver: "sunder".to_string(),
                time_ms: elapsed,
                reason: format!("unexpected solver output: {}", &trimmed[..trimmed.len().min(200)]),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// tRust #358: QueryClass-aware sunder dispatch
// ---------------------------------------------------------------------------

/// tRust #358: Sunder affinity score for a given `QueryClass`.
///
/// Returns a score in [0, 100] indicating how well-suited sunder is for
/// formulas of the given class. The portfolio system uses this to decide
/// whether to include sunder's SP engine as a lane.
///
/// - **Quantified (80):** sunder's SP calculus handles universally quantified
///   postconditions directly without quantifier instantiation heuristics.
/// - **HardNonlinear (60):** SP can reason deductively about nonlinear
///   arithmetic, complementing z4's NIA solver.
/// - **ArrayTheory (70):** SP tracks array contents through store/select
///   operations as part of the strongest postcondition computation.
/// - **EasyLinear (40):** sunder can handle it but z4/zani are faster.
/// - **Mixed (50):** deductive reasoning is moderately useful.
/// - **BitVector (10):** sunder has minimal BV theory support.
/// - **Ownership (5):** certus handles ownership; sunder adds little value.
#[must_use]
pub fn sunder_affinity(class: QueryClass) -> u32 {
    match class {
        QueryClass::Quantified => 80,
        QueryClass::ArrayTheory => 70,
        QueryClass::HardNonlinear => 60,
        QueryClass::Mixed => 50,
        QueryClass::EasyLinear => 40,
        QueryClass::BitVector => 10,
        QueryClass::Ownership => 5,
    }
}

/// tRust #358: Classify a VC for sunder dispatch suitability.
///
/// Combines the structural `QueryClass` with the VC kind to produce a
/// dispatch recommendation. Returns `true` when sunder is a strong candidate
/// for this VC, meaning the portfolio should include an SP lane.
#[must_use]
pub fn classify_for_sunder(vc: &VerificationCondition) -> bool {
    // Sunder always handles its core VC kinds.
    if is_deductive_vc_kind(&vc.kind) {
        return true;
    }

    // For non-core kinds, check formula affinity.
    let class = classifier::classify_vc(vc);
    sunder_affinity(class) >= 50
}

/// tRust #358: Check if a VcKind is a core deductive verification target.
///
/// These are the VC kinds that sunder handles natively via SP calculus,
/// independent of formula structure.
#[must_use]
pub(crate) fn is_deductive_vc_kind(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::Postcondition
            | VcKind::Precondition { .. }
            | VcKind::NonTermination { .. }
            | VcKind::TranslationValidation { .. }
    )
}

/// tRust #358: Check if an Assertion VC represents a loop invariant.
///
/// Loop invariant assertions use a `[loop:invariant]` prefix convention
/// in their message. These are deductive proof targets suitable for sunder
/// because loop invariants require reasoning about program state transformations.
#[must_use]
pub(crate) fn is_loop_invariant_assertion(kind: &VcKind) -> bool {
    matches!(kind, VcKind::Assertion { message } if message.starts_with("[loop:invariant]"))
}

/// tRust #656: Check if a VcKind is a structured loop invariant verification target.
///
/// These are the typed loop invariant VcKinds (initiation, consecution,
/// sufficiency) that sunder handles via its dedicated `verify_loop_invariant()`
/// 5-phase pipeline. Unlike `is_loop_invariant_assertion` which matches
/// string-prefixed assertions, these carry structured metadata.
#[must_use]
pub(crate) fn is_loop_invariant_vc_kind(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
    )
}

// ---------------------------------------------------------------------------
// SunderBackend
// ---------------------------------------------------------------------------

/// tRust #632: Sunder deductive verification backend.
///
/// tRust #798: Feature-gated behind `not(pipeline-v2)`. Pipeline v2 uses
/// trust-sunder-lib for direct library calls instead of this subprocess backend.
#[cfg(not(feature = "pipeline-v2"))]
pub struct SunderBackend {
    /// tRust #358: Whether to accept loop invariant assertions.
    accept_loop_invariants: bool,
    /// tRust #358: Whether to accept TranslationValidation VCs.
    accept_translation_validation: bool,
    /// tRust #632: Timeout for SMT solver subprocess (milliseconds).
    timeout_ms: u64,
}

#[cfg(not(feature = "pipeline-v2"))]
impl SunderBackend {
    /// Create a new sunder backend.
    #[must_use]
    pub fn new() -> Self {
        SunderBackend {
            accept_loop_invariants: true,
            accept_translation_validation: true,
            timeout_ms: 30_000,
        }
    }

    /// Create a backend with an explicit solver path.
    ///
    /// tRust #632: The path is accepted for API compatibility but the backend
    /// uses sunder-core's in-process encoding rather than a subprocess path.
    #[must_use]
    pub fn with_solver_path(_path: impl Into<String>) -> Self {
        Self::new()
    }

    /// Set the timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// tRust #358: Configure whether to accept loop invariant assertions.
    #[must_use]
    pub fn with_loop_invariants(mut self, accept: bool) -> Self {
        self.accept_loop_invariants = accept;
        self
    }

    /// tRust #358: Configure whether to accept TranslationValidation VCs.
    #[must_use]
    pub fn with_translation_validation(mut self, accept: bool) -> Self {
        self.accept_translation_validation = accept;
        self
    }

    /// tRust #632: Check if this VC kind is accepted by the backend configuration.
    #[cfg(feature = "sunder-backend")]
    fn is_accepted_kind(&self, kind: &VcKind) -> bool {
        if is_deductive_vc_kind(kind) {
            // Check specific kind flags
            if matches!(kind, VcKind::TranslationValidation { .. })
                && !self.accept_translation_validation
            {
                return false;
            }
            return true;
        }
        if self.accept_loop_invariants && is_loop_invariant_assertion(kind) {
            return true;
        }
        false
    }

    /// tRust #653: Verify a VC using structured contract IR when available.
    ///
    /// When `contract_ir` is `Some` and contains non-empty preconditions or
    /// postconditions, translates them separately and passes structured
    /// `requires`/`ensures` to sunder's SMT generator. No manual polarity
    /// negation is needed because `SmtGenerator::generate_vc()` performs
    /// negation internally.
    ///
    /// Falls back to the monolithic approach when:
    /// - `contract_ir` is `None` or empty
    /// - Any formula in the contract IR fails to translate
    /// - The `sunder-backend` feature is not enabled
    pub fn verify_with_contract_ir(
        &self,
        vc: &VerificationCondition,
        contract_ir: Option<&SunderContractIr>,
    ) -> VerificationResult {
        #[cfg(feature = "sunder-backend")]
        {
            if let Some(ir) = contract_ir {
                if !ir.preconditions.is_empty() || !ir.postconditions.is_empty() {
                    if let Some(result) = self.verify_structured(vc, ir) {
                        return result;
                    }
                }
            }
        }
        #[cfg(not(feature = "sunder-backend"))]
        {
            let _ = contract_ir;
        }
        // Fallback to monolithic approach
        self.verify(vc)
    }

    /// tRust #653: Structured verification with decomposed requires/ensures.
    #[cfg(feature = "sunder-backend")]
    fn verify_structured(
        &self,
        vc: &VerificationCondition,
        ir: &SunderContractIr,
    ) -> Option<VerificationResult> {
        let start = std::time::Instant::now();

        let requires = translate_formulas(&ir.preconditions)?;
        let ensures = translate_formulas(&ir.postconditions)?;

        // Generate structured SMT query with separate requires/ensures
        let smt_query = smt_verify::generate_smt_query_structured(
            &vc.function,
            &requires,
            &ensures,
        );

        Some(smt_verify::run_smt_and_map(&smt_query, &vc.function, self.timeout_ms))
    }
}

#[cfg(not(feature = "pipeline-v2"))]
impl Default for SunderBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(not(feature = "pipeline-v2"))]
impl VerificationBackend for SunderBackend {
    fn name(&self) -> &str {
        "sunder"
    }

    fn role(&self) -> BackendRole {
        BackendRole::Deductive
    }

    /// tRust #632: Returns `true` for deductive VCs with translatable formulas
    /// when the `sunder-backend` feature is enabled.
    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        #[cfg(feature = "sunder-backend")]
        {
            if !self.is_accepted_kind(&vc.kind) {
                return false;
            }
            translate::is_translatable(&vc.formula)
        }
        #[cfg(not(feature = "sunder-backend"))]
        {
            let _ = vc;
            false
        }
    }

    /// tRust #632: Verifies a VC using sunder-core's formula encoding.
    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        #[cfg(feature = "sunder-backend")]
        {
            let start = std::time::Instant::now();

            // Step 1: Translate Formula -> PureExpr
            let expr = match translate::formula_to_pure_expr(&vc.formula) {
                Some(e) => e,
                None => {
                    return VerificationResult::Unknown {
                        solver: "sunder".to_string(),
                        time_ms: start.elapsed().as_millis() as u64,
                        reason: "formula contains unsupported constructs \
                                 (bitvectors or arrays)"
                            .to_string(),
                    };
                }
            };

            // Step 2: Generate SMT-LIB2 via sunder-core's SmtGenerator
            let smt_query = smt_verify::generate_smt_query(&vc.function, &[expr]);

            // Step 3: Run SMT query and map result
            smt_verify::run_smt_and_map(&smt_query, &vc.function, self.timeout_ms)
        }
        #[cfg(not(feature = "sunder-backend"))]
        {
            let _ = vc;
            VerificationResult::Unknown {
                solver: "sunder".to_string(),
                time_ms: 0,
                reason: "sunder-backend feature not enabled".to_string(),
            }
        }
    }
}

/// Re-attribute a verification result to the sunder solver.
///
/// tRust #556: Fixed proof strength — no longer misattributes SMT results
/// as deductive proofs. The strength is preserved as-is since the actual
/// proving was done by another backend. When native sunder integration
/// exists, this will correctly use `ProofStrength::deductive()`.
pub(crate) fn attribute_to_sunder(result: &mut VerificationResult) {
    match result {
        VerificationResult::Proved { solver, .. } => {
            *solver = "sunder".to_string();
            // tRust #556: Do NOT upgrade strength to deductive() — the proof
            // was done by an SMT solver, not sunder's SP calculus.
        }
        VerificationResult::Failed { solver, .. } => {
            *solver = "sunder".to_string();
        }
        VerificationResult::Unknown { solver, .. } => {
            *solver = "sunder".to_string();
        }
        VerificationResult::Timeout { solver, .. } => {
            *solver = "sunder".to_string();
        }
        // tRust #556: Handle future non-exhaustive variants gracefully
        _ => {}
    }
}

// tRust #798: Tests that depend on SunderBackend struct are gated behind
// not(pipeline-v2). Classification function tests (sunder_affinity, etc.)
// are included in the gate as well since they share the test module.
#[cfg(all(test, not(feature = "pipeline-v2")))]
mod tests {
    use super::*;
    use crate::mock_backend::MockBackend;
    use crate::portfolio::{
        DispatchMode, PortfolioLane, PortfolioRunner, PortfolioStrategy, SolverEntry,
        SolverPool, PortfolioConfig, RaceStrategy, race,
    };
    use crate::Router;
    use std::sync::Arc;

    // -----------------------------------------------------------------------
    // Helper to create VCs for testing
    // -----------------------------------------------------------------------

    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    // -----------------------------------------------------------------------
    // Basic backend identity and configuration
    // -----------------------------------------------------------------------

    #[test]
    fn test_sunder_backend_name_and_role() {
        let backend = SunderBackend::new();
        assert_eq!(backend.name(), "sunder");
        assert_eq!(backend.role(), BackendRole::Deductive);
    }

    // -----------------------------------------------------------------------
    // tRust #632: can_handle behavior (feature-gated tests)
    // -----------------------------------------------------------------------

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_enabled_for_postconditions() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        assert!(backend.can_handle(&vc), "sunder should handle postconditions (#632)");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_enabled_for_preconditions() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Precondition { callee: "callee".into() },
            Formula::Bool(true),
        );
        assert!(backend.can_handle(&vc), "sunder should handle preconditions (#632)");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_rejects_bitvector_formulas() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Postcondition,
            Formula::BitVec { value: 42, width: 32 },
        );
        assert!(!backend.can_handle(&vc), "sunder should reject bitvector formulas");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_rejects_l0_safety() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        assert!(!backend.can_handle(&vc), "sunder should not handle L0Safety VCs");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_enabled_for_loop_invariant() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Assertion {
                message: "[loop:invariant] counter decreases".into(),
            },
            Formula::Bool(true),
        );
        assert!(backend.can_handle(&vc), "sunder should handle loop invariants (#632)");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_rejects_loop_invariant_when_disabled() {
        let backend = SunderBackend::new().with_loop_invariants(false);
        let vc = make_vc(
            VcKind::Assertion {
                message: "[loop:invariant] counter decreases".into(),
            },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "loop invariants disabled");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_enabled_for_translation_validation() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::TranslationValidation {
                pass: "constant_folding".into(),
                check: "output_equivalence".into(),
            },
            Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(42)),
            ),
        );
        assert!(backend.can_handle(&vc), "sunder should handle translation validation (#632)");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_rejects_translation_validation_when_disabled() {
        let backend = SunderBackend::new().with_translation_validation(false);
        let vc = make_vc(
            VcKind::TranslationValidation {
                pass: "constant_folding".into(),
                check: "output_equivalence".into(),
            },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "translation validation disabled");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_handles_quantified_postcondition() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Postcondition,
            Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
        );
        assert!(backend.can_handle(&vc), "sunder should handle quantified postconditions");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_rejects_array_formulas() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Postcondition,
            Formula::Select(
                Box::new(Formula::Var(
                    "arr".into(),
                    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            ),
        );
        assert!(!backend.can_handle(&vc), "sunder should reject array formulas");
    }

    // Without sunder-backend feature: disabled behavior
    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_postconditions() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_preconditions() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Precondition { callee: "callee".into() },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_l0_safety() {
        let backend = SunderBackend::new();
        let cases = vec![
            VcKind::DivisionByZero,
            VcKind::IndexOutOfBounds,
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
        ];
        for kind in cases {
            let vc = make_vc(kind, Formula::Bool(true));
            assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
        }
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_temporal() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Temporal { property: "live".into() },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_loop_invariant() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::Assertion {
                message: "[loop:invariant] counter decreases".into(),
            },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_translation_validation() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::TranslationValidation {
                pass: "constant_folding".into(),
                check: "output_equivalence".into(),
            },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_disabled_for_non_termination() {
        let backend = SunderBackend::new();
        let vc = make_vc(
            VcKind::NonTermination {
                context: "while loop".into(),
                measure: "n".into(),
            },
            Formula::Bool(true),
        );
        assert!(!backend.can_handle(&vc), "sunder should be disabled without feature");
    }

    // -----------------------------------------------------------------------
    // tRust #632: Formula translation tests (requires sunder-backend)
    // -----------------------------------------------------------------------

    #[cfg(feature = "sunder-backend")]
    mod translation_tests {
        use super::super::translate::*;
        use sunder_core::formula::{BinOp as SBinOp, ExprSort, PureExpr, UnOp as SUnOp};
        use trust_types::{Formula, Sort};
        use std::sync::Arc;

        #[test]
        fn test_translate_bool_true() {
            assert_eq!(
                formula_to_pure_expr(&Formula::Bool(true)),
                Some(PureExpr::Bool(true))
            );
        }

        #[test]
        fn test_translate_bool_false() {
            assert_eq!(
                formula_to_pure_expr(&Formula::Bool(false)),
                Some(PureExpr::Bool(false))
            );
        }

        #[test]
        fn test_translate_int() {
            assert_eq!(
                formula_to_pure_expr(&Formula::Int(42)),
                Some(PureExpr::Int(42))
            );
        }

        #[test]
        fn test_translate_int_negative() {
            assert_eq!(
                formula_to_pure_expr(&Formula::Int(-100)),
                Some(PureExpr::Int(-100))
            );
        }

        #[test]
        fn test_translate_int_overflow() {
            // i128 value that exceeds i64 range
            let big = i128::from(i64::MAX) + 1;
            assert_eq!(formula_to_pure_expr(&Formula::Int(big)), None);
        }

        #[test]
        fn test_translate_uint() {
            assert_eq!(
                formula_to_pure_expr(&Formula::UInt(100)),
                Some(PureExpr::Int(100))
            );
        }

        #[test]
        fn test_translate_var_int() {
            assert_eq!(
                formula_to_pure_expr(&Formula::Var("x".into(), Sort::Int)),
                Some(PureExpr::Var("x".into(), Some(ExprSort::Int)))
            );
        }

        #[test]
        fn test_translate_var_bool() {
            assert_eq!(
                formula_to_pure_expr(&Formula::Var("p".into(), Sort::Bool)),
                Some(PureExpr::Var("p".into(), Some(ExprSort::Bool)))
            );
        }

        #[test]
        fn test_translate_var_bitvec_sort() {
            // BitVec sort translates to None (unsupported), but the Var itself
            // still translates — just with no sort annotation
            assert_eq!(
                formula_to_pure_expr(&Formula::Var("bv".into(), Sort::BitVec(32))),
                Some(PureExpr::Var("bv".into(), None))
            );
        }

        #[test]
        fn test_translate_not() {
            let f = Formula::Not(Box::new(Formula::Bool(true)));
            assert_eq!(
                formula_to_pure_expr(&f),
                Some(PureExpr::UnOp(SUnOp::Not, Arc::new(PureExpr::Bool(true))))
            );
        }

        #[test]
        fn test_translate_and() {
            let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
            let expected = PureExpr::BinOp(
                Arc::new(PureExpr::Bool(true)),
                SBinOp::And,
                Arc::new(PureExpr::Bool(false)),
            );
            assert_eq!(formula_to_pure_expr(&f), Some(expected));
        }

        #[test]
        fn test_translate_and_empty() {
            let f = Formula::And(vec![]);
            assert_eq!(formula_to_pure_expr(&f), Some(PureExpr::Bool(true)));
        }

        #[test]
        fn test_translate_or_empty() {
            let f = Formula::Or(vec![]);
            assert_eq!(formula_to_pure_expr(&f), Some(PureExpr::Bool(false)));
        }

        #[test]
        fn test_translate_eq() {
            let f = Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            );
            let expected = PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
                SBinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            );
            assert_eq!(formula_to_pure_expr(&f), Some(expected));
        }

        #[test]
        fn test_translate_arithmetic() {
            let f = Formula::Add(
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(2)),
            );
            let expected = PureExpr::BinOp(
                Arc::new(PureExpr::Int(1)),
                SBinOp::Add,
                Arc::new(PureExpr::Int(2)),
            );
            assert_eq!(formula_to_pure_expr(&f), Some(expected));
        }

        #[test]
        fn test_translate_ite() {
            let f = Formula::Ite(
                Box::new(Formula::Bool(true)),
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(0)),
            );
            let expected = PureExpr::Ite(
                Arc::new(PureExpr::Bool(true)),
                Arc::new(PureExpr::Int(1)),
                Arc::new(PureExpr::Int(0)),
            );
            assert_eq!(formula_to_pure_expr(&f), Some(expected));
        }

        #[test]
        fn test_translate_forall() {
            let f = Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            );
            let result = formula_to_pure_expr(&f);
            assert!(result.is_some());
            if let Some(PureExpr::Forall { var, var_sort, .. }) = &result {
                assert_eq!(var, "x");
                assert_eq!(*var_sort, Some(ExprSort::Int));
            } else {
                panic!("expected Forall");
            }
        }

        #[test]
        fn test_translate_bitvec_literal_fails() {
            let f = Formula::BitVec { value: 42, width: 32 };
            assert_eq!(formula_to_pure_expr(&f), None);
        }

        #[test]
        fn test_translate_bvadd_fails() {
            let f = Formula::BvAdd(
                Box::new(Formula::BitVec { value: 1, width: 32 }),
                Box::new(Formula::BitVec { value: 2, width: 32 }),
                32,
            );
            assert_eq!(formula_to_pure_expr(&f), None);
        }

        #[test]
        fn test_translate_select_fails() {
            let f = Formula::Select(
                Box::new(Formula::Var(
                    "arr".into(),
                    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            );
            assert_eq!(formula_to_pure_expr(&f), None);
        }

        #[test]
        fn test_sort_translation() {
            assert_eq!(sort_to_expr_sort(&Sort::Bool), Some(ExprSort::Bool));
            assert_eq!(sort_to_expr_sort(&Sort::Int), Some(ExprSort::Int));
            assert_eq!(sort_to_expr_sort(&Sort::BitVec(32)), None);
            assert_eq!(
                sort_to_expr_sort(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
                None
            );
        }

        #[test]
        fn test_is_translatable() {
            assert!(is_translatable(&Formula::Bool(true)));
            assert!(is_translatable(&Formula::Int(42)));
            assert!(!is_translatable(&Formula::BitVec { value: 0, width: 8 }));
        }

        /// tRust #652: is_translatable rejects array formulas without full translation
        #[test]
        fn test_is_translatable_rejects_arrays() {
            assert!(!is_translatable(&Formula::Select(
                Box::new(Formula::Var(
                    "arr".into(),
                    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            )));
        }

        /// tRust #652: is_translatable rejects large integers without full translation
        #[test]
        fn test_is_translatable_rejects_large_integers() {
            let big = i128::from(i64::MAX) + 1;
            assert!(!is_translatable(&Formula::Int(big)));
        }

        /// tRust #652: is_translatable accepts pure integer formulas cheaply
        #[test]
        fn test_is_translatable_accepts_pure_int_formula() {
            let f = Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            );
            assert!(is_translatable(&f));
        }
    }

    // -----------------------------------------------------------------------
    // tRust #632: SMT generation tests (requires sunder-backend)
    // -----------------------------------------------------------------------

    #[cfg(feature = "sunder-backend")]
    mod smt_tests {
        use super::super::{smt_verify, translate};
        use trust_types::Formula;

        #[test]
        fn test_smt_query_generation_bool_true() {
            let expr = translate::formula_to_pure_expr(&Formula::Bool(true)).unwrap();
            let query = smt_verify::generate_smt_query("test_fn", &[expr]);
            // The query should contain check-sat and assert NOT(true)
            assert!(query.contains("check-sat"), "query must contain check-sat");
            assert!(query.contains("assert"), "query must contain assert");
        }

        #[test]
        fn test_smt_query_generation_with_variables() {
            let formula = Formula::Gt(
                Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(0)),
            );
            let expr = translate::formula_to_pure_expr(&formula).unwrap();
            let query = smt_verify::generate_smt_query("test_fn", &[expr]);
            // Should declare the variable x
            assert!(query.contains("declare-const"), "query must declare variables");
            assert!(query.contains("x"), "query must reference variable x");
        }
    }

    // -----------------------------------------------------------------------
    // verify() tests
    // -----------------------------------------------------------------------

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_verify_returns_unknown() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "sunder");
    }

    #[test]
    fn test_sunder_verify_with_solver_path_returns_backend() {
        let backend = SunderBackend::with_solver_path("/nonexistent/path/sunder");
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));

        let result = backend.verify(&vc);
        assert_eq!(result.solver_name(), "sunder");
    }

    // -----------------------------------------------------------------------
    // Builder methods
    // -----------------------------------------------------------------------

    #[test]
    fn test_sunder_builder_methods() {
        let backend =
            SunderBackend::with_solver_path("/usr/local/bin/sunder").with_timeout(60_000);
        assert!(backend.accept_loop_invariants);
        assert!(backend.accept_translation_validation);
        assert_eq!(backend.timeout_ms, 60_000);
    }

    #[test]
    fn test_sunder_default_construction() {
        let backend = SunderBackend::default();
        assert!(backend.accept_loop_invariants);
        assert!(backend.accept_translation_validation);
    }

    #[test]
    fn test_sunder_loop_invariant_config() {
        let backend = SunderBackend::new().with_loop_invariants(false);
        assert!(!backend.accept_loop_invariants);
    }

    #[test]
    fn test_sunder_translation_validation_config() {
        let backend = SunderBackend::new().with_translation_validation(false);
        assert!(!backend.accept_translation_validation);
    }

    // -----------------------------------------------------------------------
    // Result attribution — #556: no proof strength misattribution
    // -----------------------------------------------------------------------

    #[test]
    fn test_attribute_to_sunder_proved_preserves_strength() {
        use crate::smtlib_backend::parse_solver_output;

        let mut result = VerificationResult::Proved {
            solver: "z4-smtlib".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
                solver_warnings: None,
        };
        attribute_to_sunder(&mut result);

        assert_eq!(result.solver_name(), "sunder");
        if let VerificationResult::Proved { strength, time_ms, .. } = &result {
            // tRust #556: strength should NOT be upgraded to deductive
            assert_eq!(*strength, ProofStrength::smt_unsat());
            assert_eq!(*time_ms, 42);
        } else {
            panic!("expected Proved");
        }
    }

    #[test]
    fn test_attribute_to_sunder_failed() {
        let cex = Counterexample::new(vec![("x".to_string(), CounterexampleValue::Uint(42))]);
        let mut result = VerificationResult::Failed {
            solver: "z4-smtlib".to_string(),
            time_ms: 10,
            counterexample: Some(cex),
        };
        attribute_to_sunder(&mut result);

        assert_eq!(result.solver_name(), "sunder");
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 1);
            assert_eq!(cex.assignments[0].0, "x");
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_attribute_to_sunder_unknown() {
        let mut result = VerificationResult::Unknown {
            solver: "z4-smtlib".to_string(),
            time_ms: 5,
            reason: "solver returned unknown".to_string(),
        };
        attribute_to_sunder(&mut result);

        assert_eq!(result.solver_name(), "sunder");
    }

    #[test]
    fn test_attribute_to_sunder_timeout() {
        let mut result = VerificationResult::Timeout {
            solver: "z4-smtlib".to_string(),
            timeout_ms: 30_000,
        };
        attribute_to_sunder(&mut result);

        assert_eq!(result.solver_name(), "sunder");
    }

    // -----------------------------------------------------------------------
    // tRust #358: QueryClass-aware dispatch classification
    // -----------------------------------------------------------------------

    #[test]
    fn test_sunder_affinity_quantified_high() {
        assert_eq!(sunder_affinity(QueryClass::Quantified), 80);
    }

    #[test]
    fn test_sunder_affinity_bitvector_low() {
        assert_eq!(sunder_affinity(QueryClass::BitVector), 10);
    }

    #[test]
    fn test_classify_for_sunder_postcondition_always_true() {
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        assert!(
            classify_for_sunder(&vc),
            "Postcondition is a core deductive VC kind"
        );
    }

    #[test]
    fn test_classify_for_sunder_precondition_always_true() {
        let vc = make_vc(
            VcKind::Precondition { callee: "foo".into() },
            Formula::Bool(true),
        );
        assert!(
            classify_for_sunder(&vc),
            "Precondition is a core deductive VC kind"
        );
    }

    #[test]
    fn test_classify_for_sunder_l0_safety_with_quantified_formula() {
        let vc = make_vc(
            VcKind::DivisionByZero,
            Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
        );
        assert!(
            classify_for_sunder(&vc),
            "quantified L0 formula should trigger sunder (affinity 80 >= 50)"
        );
    }

    #[test]
    fn test_classify_for_sunder_l0_safety_with_simple_formula() {
        let vc = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        );
        assert!(
            !classify_for_sunder(&vc),
            "simple linear L0 formula should not trigger sunder (affinity 40 < 50)"
        );
    }

    #[test]
    fn test_is_deductive_vc_kind_postcondition() {
        assert!(is_deductive_vc_kind(&VcKind::Postcondition));
    }

    #[test]
    fn test_is_deductive_vc_kind_precondition() {
        assert!(is_deductive_vc_kind(&VcKind::Precondition { callee: "f".into() }));
    }

    #[test]
    fn test_is_deductive_vc_kind_non_termination() {
        assert!(is_deductive_vc_kind(&VcKind::NonTermination {
            context: "loop".into(),
            measure: "n".into(),
        }));
    }

    #[test]
    fn test_is_deductive_vc_kind_translation_validation() {
        assert!(is_deductive_vc_kind(&VcKind::TranslationValidation {
            pass: "dce".into(),
            check: "equiv".into(),
        }));
    }

    #[test]
    fn test_is_deductive_vc_kind_division_by_zero_false() {
        assert!(!is_deductive_vc_kind(&VcKind::DivisionByZero));
    }

    #[test]
    fn test_is_loop_invariant_assertion_positive() {
        assert!(is_loop_invariant_assertion(&VcKind::Assertion {
            message: "[loop:invariant] x > 0".into(),
        }));
    }

    #[test]
    fn test_is_loop_invariant_assertion_negative() {
        assert!(!is_loop_invariant_assertion(&VcKind::Assertion {
            message: "x must be positive".into(),
        }));
        assert!(!is_loop_invariant_assertion(&VcKind::DivisionByZero));
    }

    // -----------------------------------------------------------------------
    // Portfolio integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_sunder_portfolio_integration() {
        let sunder: Arc<dyn VerificationBackend> =
            Arc::new(SunderBackend::new());

        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));

        let lanes = vec![PortfolioLane {
            strategy: PortfolioStrategy::StrongestPostcondition,
            backend: sunder,
        }];

        let result = race(&vc, lanes).expect("should get a result");
        assert_eq!(result.winning_strategy, PortfolioStrategy::StrongestPostcondition);
        assert_eq!(result.result.solver_name(), "sunder");
    }

    #[test]
    fn test_sunder_portfolio_multi_lane_race_with_mock() {
        let sunder: Arc<dyn VerificationBackend> = Arc::new(SunderBackend::new());
        let mock: Arc<dyn VerificationBackend> = Arc::new(MockBackend);

        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));

        let lanes = vec![
            PortfolioLane {
                strategy: PortfolioStrategy::StrongestPostcondition,
                backend: sunder,
            },
            PortfolioLane {
                strategy: PortfolioStrategy::Bmc,
                backend: mock,
            },
        ];

        let result = race(&vc, lanes).expect("should get a result");
        assert!(result.result.is_proved(), "mock should prove the trivial VC");
        assert_eq!(result.winning_strategy, PortfolioStrategy::Bmc);
        assert_eq!(result.total_lanes, 2);
    }

    #[test]
    fn test_sunder_portfolio_runner_cascade_mode() {
        let sunder: Arc<dyn VerificationBackend> = Arc::new(SunderBackend::new());
        let mock: Arc<dyn VerificationBackend> = Arc::new(MockBackend);

        let runner = PortfolioRunner::new(vec![sunder, mock], DispatchMode::Cascade);

        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));

        let result = runner.verify(&vc);
        assert!(result.is_proved(), "cascade should produce a proof");
    }

    #[test]
    fn test_sunder_portfolio_runner_selective_mode() {
        let sunder: Arc<dyn VerificationBackend> = Arc::new(SunderBackend::new());
        let mock: Arc<dyn VerificationBackend> = Arc::new(MockBackend);

        let runner = PortfolioRunner::new(vec![mock, sunder], DispatchMode::Selective);

        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));

        let result = runner.verify(&vc);
        assert!(result.is_proved() || matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_sunder_solver_pool_integration() {
        let sunder: Arc<dyn VerificationBackend> = Arc::new(SunderBackend::new());
        let mock: Arc<dyn VerificationBackend> = Arc::new(MockBackend);

        let pool = SolverPool::with_defaults(vec![
            SolverEntry { name: "sunder".into(), backend: sunder },
            SolverEntry { name: "mock".into(), backend: mock },
        ]);

        assert_eq!(pool.solver_count(), 2);
        let names = pool.solver_names();
        assert!(names.contains(&"sunder"));
        assert!(names.contains(&"mock"));

        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));
        let race_result = pool.race(&vc);
        assert!(
            race_result.is_definitive()
                || matches!(race_result.winner_result, VerificationResult::Unknown { .. }),
            "pool race should produce some result"
        );
    }

    #[test]
    fn test_sunder_sp_strategy_has_deductive_proof_strength() {
        let strength = PortfolioStrategy::StrongestPostcondition.proof_strength();
        assert_eq!(
            strength,
            ProofStrength::deductive(),
            "SP strategy should produce deductive proof strength"
        );
    }

    #[test]
    fn test_sunder_sp_strategy_name() {
        assert_eq!(
            PortfolioStrategy::StrongestPostcondition.name(),
            "sp",
            "SP strategy should have name 'sp'"
        );
    }

    #[test]
    fn test_sunder_in_query_class_strategy_selection() {
        use crate::portfolio::select_strategies_for_query;

        let strategies = select_strategies_for_query(QueryClass::Quantified);
        assert!(
            strategies.contains(&PortfolioStrategy::StrongestPostcondition),
            "Quantified class should include StrongestPostcondition strategy"
        );
    }

    #[test]
    fn test_sunder_not_in_bitvector_strategy_selection() {
        use crate::portfolio::select_strategies_for_query;

        let strategies = select_strategies_for_query(QueryClass::BitVector);
        assert!(
            !strategies.contains(&PortfolioStrategy::StrongestPostcondition),
            "BitVector class should not include StrongestPostcondition strategy"
        );
    }

    #[test]
    fn test_sunder_solver_pool_best_strength_race() {
        let sunder: Arc<dyn VerificationBackend> = Arc::new(SunderBackend::new());
        let mock: Arc<dyn VerificationBackend> = Arc::new(MockBackend);

        let config = PortfolioConfig {
            strategy: RaceStrategy::BestStrength,
            solver_timeout_ms: 5_000,
            max_parallel: 4,
        };
        let pool = SolverPool::new(
            vec![
                SolverEntry { name: "sunder".into(), backend: sunder },
                SolverEntry { name: "mock".into(), backend: mock },
            ],
            config,
        );

        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));
        let race_result = pool.race(&vc);
        assert!(race_result.is_definitive());
    }

    // -----------------------------------------------------------------------
    // tRust #653: verify_with_contract_ir tests
    // -----------------------------------------------------------------------

    fn make_contract_ir(
        preconditions: Vec<Formula>,
        postconditions: Vec<Formula>,
    ) -> SunderContractIr {
        SunderContractIr {
            preconditions,
            postconditions,
            loop_invariants: vec![],
            type_refinements: vec![],
            modifies_set: vec![],
        }
    }

    #[test]
    fn test_sunder_verify_with_contract_ir_none_falls_back() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        // None => fallback to monolithic
        let result = backend.verify_with_contract_ir(&vc, None);
        assert_eq!(result.solver_name(), "sunder");
    }

    #[test]
    fn test_sunder_verify_with_contract_ir_empty_falls_back() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        let ir = make_contract_ir(vec![], vec![]);
        let result = backend.verify_with_contract_ir(&vc, Some(&ir));
        assert_eq!(result.solver_name(), "sunder");
    }

    #[cfg(feature = "sunder-backend")]
    #[test]
    fn test_sunder_verify_with_contract_ir_structured() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        let ir = make_contract_ir(
            vec![Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )],
            vec![Formula::Gt(
                Box::new(Formula::Var("result".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )],
        );
        // Structured path: uses generate_smt_query_structured
        let result = backend.verify_with_contract_ir(&vc, Some(&ir));
        // May succeed or fail depending on solver availability, but should
        // be attributed to "sunder"
        assert_eq!(result.solver_name(), "sunder");
    }

    #[cfg(not(feature = "sunder-backend"))]
    #[test]
    fn test_sunder_verify_with_contract_ir_disabled_falls_back() {
        let backend = SunderBackend::new();
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        let ir = make_contract_ir(
            vec![Formula::Bool(true)],
            vec![Formula::Bool(true)],
        );
        // Without feature, structured path is unavailable => falls back
        let result = backend.verify_with_contract_ir(&vc, Some(&ir));
        assert_eq!(result.solver_name(), "sunder");
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }
}
