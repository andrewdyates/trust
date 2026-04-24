// trust-router/sunder_backend.rs: Sunder deductive verification backend
//
// tRust #632: Phase 1 native integration using sunder-core's PureExpr and
// SmtGenerator. Translates trust-types Formula to sunder-core PureExpr,
// generates SMT-LIB2 via sunder-core's encoder, and verifies via an SMT
// solver subprocess.
//
// tRust #798: The SunderBackend struct (subprocess-based) is feature-gated
// behind `not(pipeline-v2)` -- Pipeline v2 uses trust-sunder-lib for direct
// library calls. Classification logic (is_deductive_vc_kind) is always
// available regardless of feature flags.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(any(not(feature = "pipeline-v2"), feature = "sunder-backend"))]
use trust_types::*;

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
                    result = PureExpr::BinOp(Arc::new(result), SBinOp::And, Arc::new(right));
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
                    result = PureExpr::BinOp(Arc::new(result), SBinOp::Or, Arc::new(right));
                }
                Some(result)
            }

            Formula::Implies(a, b) => {
                let left = formula_to_pure_expr(a)?;
                let right = formula_to_pure_expr(b)?;
                Some(PureExpr::BinOp(Arc::new(left), SBinOp::Implies, Arc::new(right)))
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
                    solver: "sunder".into(),
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
                    solver: "sunder".into(),
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
                solver: "sunder".into(),
                time_ms: elapsed,
                strength: ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
            }
        } else if trimmed.starts_with("sat") {
            VerificationResult::Failed {
                solver: "sunder".into(),
                time_ms: elapsed,
                counterexample: None, // Counterexample parsing not yet implemented
            }
        } else if elapsed >= timeout_ms {
            VerificationResult::Timeout { solver: "sunder".into(), timeout_ms }
        } else {
            VerificationResult::Unknown {
                solver: "sunder".into(),
                time_ms: elapsed,
                reason: format!("unexpected solver output: {}", &trimmed[..trimmed.len().min(200)]),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// tRust #358: Deductive VC classification helpers
// tRust #970: sunder_affinity, classify_for_sunder removed — dead code
// (only called from deleted portfolio/classifier modules)
// ---------------------------------------------------------------------------

/// tRust #358: Check if a VcKind is a core deductive verification target.
///
/// These are the VC kinds that sunder handles natively via SP calculus,
/// independent of formula structure.
#[cfg(feature = "sunder-backend")]
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
        let smt_query =
            smt_verify::generate_smt_query_structured(&vc.function, &requires, &ensures);

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
                        solver: "sunder".into(),
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
                solver: "sunder".into(),
                time_ms: 0,
                reason: "sunder-backend feature not enabled".to_string(),
            }
        }
    }
}

// tRust #970: Tests removed — depended on deleted portfolio and classifier modules.
// SunderBackend struct and its tests are dead under pipeline-v2 (default feature).
// The entire test module is deleted to avoid stale references to removed modules.
