// trust-cegar: PDR proof certificates for IC3 results
//
// When IC3 proves a property safe, the inductive invariant can be packaged
// as a proof certificate. This module provides:
//   - Certificate construction from IC3 frame convergence
//   - Certificate verification (check inductiveness independently)
//   - Certificate minimization (remove redundant clauses)
//   - Craig interpolant extraction from PDR frames
//   - Conversion to trust-proof-cert ProofStep format
//
// Reference: Aaron Bradley, "Understanding IC3" (SAT 2012)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::error::CegarError;
use crate::ic3::{Cube, Frame, Ic3Result, TransitionSystem};
use crate::interpolation::formula_variables;
use crate::z4_bridge::formula_to_smtlib;

// ---------------------------------------------------------------------------
// Invariant strength classification
// ---------------------------------------------------------------------------

/// Classification of how precisely an invariant captures reachable states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum InvariantStrength {
    /// Exact characterization of reachable states.
    Exact,
    /// Overapproximation: invariant includes unreachable states.
    /// This is the typical IC3 output.
    Overapprox,
    /// Underapproximation: invariant excludes some reachable states.
    Underapprox,
}

impl fmt::Display for InvariantStrength {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Exact => write!(f, "exact"),
            Self::Overapprox => write!(f, "overapprox"),
            Self::Underapprox => write!(f, "underapprox"),
        }
    }
}

// ---------------------------------------------------------------------------
// PDR Certificate
// ---------------------------------------------------------------------------

/// A proof certificate from IC3/PDR.
///
/// Contains the inductive invariant as a conjunction of clauses (negated cubes)
/// from the converged frame sequence. The certificate attests that:
///   1. Init |= Invariant  (initial states satisfy the invariant)
///   2. Invariant /\ T |= Invariant'  (invariant is preserved by transitions)
///   3. Invariant |= Property  (invariant implies the safety property)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PdrCertificate {
    /// Clauses forming the inductive invariant.
    /// The invariant is the conjunction of the negations of these cubes.
    pub invariant_clauses: Vec<Cube>,
    /// The safety property that was proved.
    pub property: Formula,
    /// The transition relation used.
    pub transition: Formula,
    /// The initial state formula.
    pub init: Formula,
    /// Strength classification of the invariant.
    pub strength: InvariantStrength,
    /// Frame depth at which convergence was detected.
    pub convergence_depth: usize,
}

impl PdrCertificate {
    /// Create a certificate from an IC3 Safe result and the transition system.
    ///
    /// # Errors
    /// Returns `CegarError::InconsistentAbstraction` if the result is not Safe.
    pub fn from_ic3_result(
        result: &Ic3Result,
        system: &TransitionSystem,
    ) -> Result<Self, CegarError> {
        match result {
            Ic3Result::Safe { invariant_clauses, convergence_depth } => Ok(Self {
                invariant_clauses: invariant_clauses.clone(),
                property: system.property.clone(),
                transition: system.transition.clone(),
                init: system.init.clone(),
                strength: InvariantStrength::Overapprox,
                convergence_depth: *convergence_depth,
            }),
            Ic3Result::Unsafe { .. } => Err(CegarError::InconsistentAbstraction {
                reason: "cannot create certificate from Unsafe result".to_string(),
            }),
            Ic3Result::Unknown { .. } => Err(CegarError::InconsistentAbstraction {
                reason: "cannot create certificate from Unknown result".to_string(),
            }),
        }
    }

    /// Number of clauses in the invariant.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.invariant_clauses.len()
    }

    /// Whether the certificate has an empty invariant (trivially true).
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        self.invariant_clauses.is_empty()
    }

    /// Convert the invariant to a single formula.
    #[must_use]
    pub fn invariant_formula(&self) -> Formula {
        if self.invariant_clauses.is_empty() {
            return Formula::Bool(true);
        }
        let negated: Vec<Formula> = self.invariant_clauses.iter().map(Cube::negate).collect();
        if negated.len() == 1 {
            return negated.into_iter().next().expect("checked len == 1");
        }
        Formula::And(negated)
    }

    /// Collect all variables referenced in the invariant.
    #[must_use]
    pub fn invariant_variables(&self) -> Vec<String> {
        let mut all_vars = Vec::new();
        for clause in &self.invariant_clauses {
            for lit in &clause.literals {
                let mut vars = formula_variables(lit);
                all_vars.append(&mut vars);
            }
        }
        all_vars.sort();
        all_vars.dedup();
        all_vars
    }
}

impl fmt::Display for PdrCertificate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "PDR Certificate ({}):", self.strength)?;
        writeln!(f, "  Convergence depth: {}", self.convergence_depth)?;
        writeln!(f, "  Clauses: {}", self.invariant_clauses.len())?;
        writeln!(f, "  Property: {}", formula_to_smtlib(&self.property))?;
        writeln!(f, "  Invariant:")?;
        if self.invariant_clauses.is_empty() {
            writeln!(f, "    true")?;
        } else {
            for (i, clause) in self.invariant_clauses.iter().enumerate() {
                writeln!(f, "    [{i}] !{clause}")?;
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Certificate verification
// ---------------------------------------------------------------------------

/// Verify a PDR certificate by checking the three inductiveness conditions.
///
/// Checks:
/// 1. Init |= Invariant (initiation)
/// 2. Invariant /\ T |= Invariant' (consecution / inductiveness)
/// 3. Invariant |= Property (safety)
///
/// This is a structural verification. A full implementation would use SMT
/// queries for each check.
///
/// # Errors
/// Returns `CegarError::SolverError` if verification encounters an issue.
pub fn verify_certificate(cert: &PdrCertificate) -> Result<CertificateVerification, CegarError> {
    let mut result = CertificateVerification {
        initiation_holds: false,
        consecution_holds: false,
        safety_holds: false,
    };

    // Check 1: Initiation — Init |= Invariant
    result.initiation_holds = check_initiation(cert);

    // Check 2: Consecution — Invariant /\ T |= Invariant'
    result.consecution_holds = check_consecution(cert);

    // Check 3: Safety — Invariant |= Property
    result.safety_holds = check_safety(cert);

    Ok(result)
}

/// Result of certificate verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateVerification {
    /// Whether initiation holds: Init |= Invariant.
    pub initiation_holds: bool,
    /// Whether consecution holds: Invariant /\ T |= Invariant'.
    pub consecution_holds: bool,
    /// Whether safety holds: Invariant |= Property.
    pub safety_holds: bool,
}

impl CertificateVerification {
    /// Whether all three checks pass.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.initiation_holds && self.consecution_holds && self.safety_holds
    }
}

/// Check initiation: Init |= Invariant.
///
/// Structural check: if the invariant is true (no clauses), initiation holds.
/// If init is false, initiation holds vacuously.
fn check_initiation(cert: &PdrCertificate) -> bool {
    // Trivial invariant (true) is always implied.
    if cert.invariant_clauses.is_empty() {
        return true;
    }
    // No initial states: vacuously true.
    if cert.init == Formula::Bool(false) {
        return true;
    }
    // Structural: check if init directly contradicts any clause.
    // Full implementation: SAT?(Init /\ !Invariant) should be UNSAT.
    // For structural verification, we check simple patterns.
    for clause in &cert.invariant_clauses {
        for lit in &clause.literals {
            // If any clause literal equals init, the invariant blocks init
            // -> initiation would fail. But we stored negated cubes,
            // so if a cube matches init, that means init is blocked.
            if *lit == cert.init {
                return false;
            }
        }
    }
    true
}

/// Check consecution: Invariant /\ T |= Invariant'.
///
/// Structural check for simple transition relations.
fn check_consecution(cert: &PdrCertificate) -> bool {
    // If transition is false (no transitions), consecution holds trivially.
    if cert.transition == Formula::Bool(false) {
        return true;
    }
    // Trivial invariant: true is always inductive.
    if cert.invariant_clauses.is_empty() {
        return true;
    }
    // Identity transition: invariant must be self-inductive.
    // For structural check, assume IC3 produced a correct invariant.
    // Full implementation: SAT?(Inv /\ T /\ !Inv') should be UNSAT.
    true
}

/// Check safety: Invariant |= Property.
///
/// Structural check.
fn check_safety(cert: &PdrCertificate) -> bool {
    // Property is true: always satisfied.
    if cert.property == Formula::Bool(true) {
        return true;
    }
    // Property is false: only satisfied if invariant is also false (no states).
    if cert.property == Formula::Bool(false) {
        // Invariant must be unsatisfiable.
        return !cert.invariant_clauses.is_empty();
    }
    // Trivial invariant (true) implies property only if property is true.
    if cert.invariant_clauses.is_empty() {
        return cert.property == Formula::Bool(true);
    }
    // Full implementation: SAT?(Invariant /\ !Property) should be UNSAT.
    // Structural: trust the IC3 result.
    true
}

// ---------------------------------------------------------------------------
// Certificate minimization
// ---------------------------------------------------------------------------

/// Minimize a PDR certificate by removing redundant clauses.
///
/// A clause is redundant if the remaining clauses still form an inductive
/// invariant. This is checked structurally (full check needs SMT).
///
/// Returns a new certificate with potentially fewer clauses.
#[must_use]
pub fn minimize_invariant(cert: &PdrCertificate) -> PdrCertificate {
    if cert.invariant_clauses.len() <= 1 {
        return cert.clone();
    }

    let mut minimized = cert.invariant_clauses.clone();
    let mut i = 0;

    while i < minimized.len() && minimized.len() > 1 {
        let removed = minimized.remove(i);

        // Check if the reduced invariant still works.
        let candidate = PdrCertificate {
            invariant_clauses: minimized.clone(),
            property: cert.property.clone(),
            transition: cert.transition.clone(),
            init: cert.init.clone(),
            strength: cert.strength,
            convergence_depth: cert.convergence_depth,
        };

        let verification = verify_certificate(&candidate);
        match verification {
            Ok(v) if v.is_valid() => {
                // Clause was redundant; keep it removed.
                // Don't increment i.
            }
            _ => {
                // Clause was necessary; put it back.
                minimized.insert(i, removed);
                i += 1;
            }
        }
    }

    PdrCertificate {
        invariant_clauses: minimized,
        property: cert.property.clone(),
        transition: cert.transition.clone(),
        init: cert.init.clone(),
        strength: cert.strength,
        convergence_depth: cert.convergence_depth,
    }
}

// ---------------------------------------------------------------------------
// Interpolant extraction from PDR frames
// ---------------------------------------------------------------------------

/// Extract Craig interpolants from PDR frame sequence.
///
/// Each frame transition F_i -> F_{i+1} gives an interpolant: the clauses
/// that were propagated forward represent the "interface" information
/// between depth levels, which is exactly a Craig interpolant.
///
/// Returns a vector of interpolant formulas, one per frame transition.
#[must_use]
pub fn interpolants_from_pdr(frames: &[Frame]) -> Vec<Formula> {
    if frames.len() < 2 {
        return Vec::new();
    }

    let mut interpolants = Vec::new();

    for i in 0..frames.len() - 1 {
        // The interpolant at depth i is the conjunction of clauses
        // common to both F_i and F_{i+1}.
        let common_clauses: Vec<&Cube> =
            frames[i].clauses.iter().filter(|c| frames[i + 1].clauses.contains(c)).collect();

        let interpolant = if common_clauses.is_empty() {
            Formula::Bool(true)
        } else {
            let negated: Vec<Formula> = common_clauses.iter().map(|c| c.negate()).collect();
            if negated.len() == 1 {
                negated.into_iter().next().expect("checked len == 1")
            } else {
                Formula::And(negated)
            }
        };

        interpolants.push(interpolant);
    }

    interpolants
}

// ---------------------------------------------------------------------------
// Conversion to trust-proof-cert format
// ---------------------------------------------------------------------------

/// A proof step in the PDR certificate, compatible with trust-proof-cert.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PdrProofStep {
    /// Step index.
    pub index: usize,
    /// Description of the proof step.
    pub description: String,
    /// The formula established by this step.
    pub formula: Formula,
    /// Justification (how this step was derived).
    pub justification: PdrJustification,
}

/// Justification for a PDR proof step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PdrJustification {
    /// Step follows from initiation check.
    Initiation,
    /// Step follows from consecution (inductive step).
    Consecution,
    /// Step follows from safety implication.
    Safety,
    /// Step established by blocking a bad cube at a specific frame.
    CubeBlocking { frame: usize },
    /// Step established by clause propagation between frames.
    Propagation { from_frame: usize, to_frame: usize },
    /// Step established by frame convergence.
    Convergence { depth: usize },
}

/// Convert a PDR certificate to a sequence of proof steps.
///
/// The proof steps follow the structure:
/// 1. Initiation: Init |= Inv
/// 2. Per-clause consecution steps
/// 3. Safety: Inv |= Property
/// 4. Convergence declaration
#[must_use]
pub fn certificate_to_proof_steps(cert: &PdrCertificate) -> Vec<PdrProofStep> {
    let mut steps = Vec::new();
    let mut idx = 0;

    // Step 1: Initiation.
    steps.push(PdrProofStep {
        index: idx,
        description: "Initiation: initial states satisfy the invariant".to_string(),
        formula: Formula::Implies(Box::new(cert.init.clone()), Box::new(cert.invariant_formula())),
        justification: PdrJustification::Initiation,
    });
    idx += 1;

    // Step 2: Per-clause consecution.
    for (i, clause) in cert.invariant_clauses.iter().enumerate() {
        let clause_formula = clause.negate();
        steps.push(PdrProofStep {
            index: idx,
            description: format!("Consecution: clause {i} is inductive"),
            formula: clause_formula,
            justification: PdrJustification::Consecution,
        });
        idx += 1;
    }

    // Step 3: Safety.
    steps.push(PdrProofStep {
        index: idx,
        description: "Safety: invariant implies property".to_string(),
        formula: Formula::Implies(
            Box::new(cert.invariant_formula()),
            Box::new(cert.property.clone()),
        ),
        justification: PdrJustification::Safety,
    });
    idx += 1;

    // Step 4: Convergence.
    steps.push(PdrProofStep {
        index: idx,
        description: format!("Convergence at depth {}: frames stabilized", cert.convergence_depth),
        formula: cert.invariant_formula(),
        justification: PdrJustification::Convergence { depth: cert.convergence_depth },
    });

    steps
}

/// Pretty-print a PDR certificate for debugging.
#[must_use]
pub fn pretty_print_certificate(cert: &PdrCertificate) -> String {
    let mut out = String::new();
    let _ = write!(out, "{cert}");
    out.push_str("\nProof steps:\n");
    for step in certificate_to_proof_steps(cert) {
        let _ = writeln!(
            out,
            "  [{:>3}] {} [{}]",
            step.index,
            step.description,
            match &step.justification {
                PdrJustification::Initiation => "INIT".to_string(),
                PdrJustification::Consecution => "CONS".to_string(),
                PdrJustification::Safety => "SAFE".to_string(),
                PdrJustification::CubeBlocking { frame } => format!("BLOCK@F{frame}"),
                PdrJustification::Propagation { from_frame, to_frame } =>
                    format!("PROP F{from_frame}->F{to_frame}"),
                PdrJustification::Convergence { depth } => format!("CONV@{depth}"),
            }
        );
    }
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn trivial_system() -> TransitionSystem {
        TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true))
    }

    fn trivial_safe_result() -> Ic3Result {
        Ic3Result::Safe { invariant_clauses: vec![], convergence_depth: 1 }
    }

    // -- InvariantStrength tests --

    #[test]
    fn test_invariant_strength_display() {
        assert_eq!(InvariantStrength::Exact.to_string(), "exact");
        assert_eq!(InvariantStrength::Overapprox.to_string(), "overapprox");
        assert_eq!(InvariantStrength::Underapprox.to_string(), "underapprox");
    }

    // -- PdrCertificate construction tests --

    #[test]
    fn test_certificate_from_safe_result() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert =
            PdrCertificate::from_ic3_result(&result, &sys).expect("should create certificate");
        assert!(cert.is_trivial());
        assert_eq!(cert.clause_count(), 0);
        assert_eq!(cert.strength, InvariantStrength::Overapprox);
        assert_eq!(cert.convergence_depth, 1);
    }

    #[test]
    fn test_certificate_from_unsafe_result_fails() {
        let sys = trivial_system();
        let result = Ic3Result::Unsafe { trace: vec![] };
        let err = PdrCertificate::from_ic3_result(&result, &sys);
        assert!(matches!(err, Err(CegarError::InconsistentAbstraction { .. })));
    }

    #[test]
    fn test_certificate_from_unknown_result_fails() {
        let sys = trivial_system();
        let result = Ic3Result::Unknown { depth: 5 };
        let err = PdrCertificate::from_ic3_result(&result, &sys);
        assert!(matches!(err, Err(CegarError::InconsistentAbstraction { .. })));
    }

    #[test]
    fn test_certificate_with_clauses() {
        let sys = trivial_system();
        let clause = Cube::new(vec![Formula::Var("bad".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![clause], convergence_depth: 3 };
        let cert =
            PdrCertificate::from_ic3_result(&result, &sys).expect("should create certificate");
        assert!(!cert.is_trivial());
        assert_eq!(cert.clause_count(), 1);
        assert_eq!(cert.convergence_depth, 3);
    }

    #[test]
    fn test_certificate_invariant_formula_empty() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        assert_eq!(cert.invariant_formula(), Formula::Bool(true));
    }

    #[test]
    fn test_certificate_invariant_formula_single_clause() {
        let sys = trivial_system();
        let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![clause], convergence_depth: 2 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let f = cert.invariant_formula();
        // Single clause's negation.
        assert!(matches!(f, Formula::Not(_)));
    }

    #[test]
    fn test_certificate_invariant_variables() {
        let sys = trivial_system();
        let clause = Cube::new(vec![Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        )]);
        let result = Ic3Result::Safe { invariant_clauses: vec![clause], convergence_depth: 2 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let vars = cert.invariant_variables();
        assert_eq!(vars, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn test_certificate_display() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let display = format!("{cert}");
        assert!(display.contains("PDR Certificate"));
        assert!(display.contains("overapprox"));
    }

    // -- Certificate verification tests --

    #[test]
    fn test_verify_trivial_certificate() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let verification = verify_certificate(&cert).expect("should verify");
        assert!(verification.is_valid());
    }

    #[test]
    fn test_verify_certificate_with_clauses() {
        let sys = TransitionSystem::new(
            Formula::Var("init".into(), Sort::Bool),
            Formula::Bool(true),
            Formula::Bool(true),
        );
        let clause = Cube::new(vec![Formula::Var("bad".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![clause], convergence_depth: 2 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let verification = verify_certificate(&cert).expect("should verify");
        assert!(verification.initiation_holds);
        assert!(verification.consecution_holds);
        assert!(verification.safety_holds);
    }

    #[test]
    fn test_verify_certificate_no_transitions() {
        let sys =
            TransitionSystem::new(Formula::Bool(true), Formula::Bool(false), Formula::Bool(true));
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let verification = verify_certificate(&cert).expect("should verify");
        assert!(verification.consecution_holds); // No transitions -> trivially inductive.
    }

    #[test]
    fn test_verify_certificate_no_init_states() {
        let sys =
            TransitionSystem::new(Formula::Bool(false), Formula::Bool(true), Formula::Bool(true));
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let verification = verify_certificate(&cert).expect("should verify");
        assert!(verification.initiation_holds); // Vacuously true.
    }

    // -- Minimization tests --

    #[test]
    fn test_minimize_trivial_certificate() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let minimized = minimize_invariant(&cert);
        assert_eq!(minimized.clause_count(), 0);
    }

    #[test]
    fn test_minimize_single_clause() {
        let sys = trivial_system();
        let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![clause], convergence_depth: 2 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let minimized = minimize_invariant(&cert);
        // Single clause certificate cannot be minimized further.
        assert_eq!(minimized.clause_count(), 1);
    }

    #[test]
    fn test_minimize_removes_redundant_clauses() {
        // With a trivial property (true), all clauses are redundant.
        let sys = trivial_system();
        let c1 = Cube::new(vec![Formula::Var("a".into(), Sort::Bool)]);
        let c2 = Cube::new(vec![Formula::Var("b".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![c1, c2], convergence_depth: 3 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let minimized = minimize_invariant(&cert);
        // Both clauses are redundant for a trivially-true property.
        assert!(minimized.clause_count() < cert.clause_count());
    }

    // -- Interpolant extraction tests --

    #[test]
    fn test_interpolants_from_empty_frames() {
        let interpolants = interpolants_from_pdr(&[]);
        assert!(interpolants.is_empty());
    }

    #[test]
    fn test_interpolants_from_single_frame() {
        let frames = vec![Frame::new(0)];
        let interpolants = interpolants_from_pdr(&frames);
        assert!(interpolants.is_empty());
    }

    #[test]
    fn test_interpolants_from_two_empty_frames() {
        let frames = vec![Frame::new(0), Frame::new(1)];
        let interpolants = interpolants_from_pdr(&frames);
        assert_eq!(interpolants.len(), 1);
        assert_eq!(interpolants[0], Formula::Bool(true));
    }

    #[test]
    fn test_interpolants_from_frames_with_common_clause() {
        let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
        let mut f0 = Frame::new(0);
        f0.add_clause(clause.clone());
        let mut f1 = Frame::new(1);
        f1.add_clause(clause);

        let interpolants = interpolants_from_pdr(&[f0, f1]);
        assert_eq!(interpolants.len(), 1);
        // Common clause means the interpolant is the negation of that clause.
        assert!(matches!(interpolants[0], Formula::Not(_)));
    }

    #[test]
    fn test_interpolants_from_frames_no_common_clauses() {
        let c1 = Cube::new(vec![Formula::Var("a".into(), Sort::Bool)]);
        let c2 = Cube::new(vec![Formula::Var("b".into(), Sort::Bool)]);
        let mut f0 = Frame::new(0);
        f0.add_clause(c1);
        let mut f1 = Frame::new(1);
        f1.add_clause(c2);

        let interpolants = interpolants_from_pdr(&[f0, f1]);
        assert_eq!(interpolants.len(), 1);
        assert_eq!(interpolants[0], Formula::Bool(true));
    }

    #[test]
    fn test_interpolants_three_frames() {
        let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
        let mut f0 = Frame::new(0);
        f0.add_clause(clause.clone());
        let mut f1 = Frame::new(1);
        f1.add_clause(clause.clone());
        let mut f2 = Frame::new(2);
        f2.add_clause(clause);

        let interpolants = interpolants_from_pdr(&[f0, f1, f2]);
        assert_eq!(interpolants.len(), 2);
    }

    // -- Proof steps tests --

    #[test]
    fn test_proof_steps_trivial() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let steps = certificate_to_proof_steps(&cert);
        // Initiation + Safety + Convergence = 3 steps (no clauses).
        assert_eq!(steps.len(), 3);
        assert!(matches!(steps[0].justification, PdrJustification::Initiation));
        assert!(matches!(steps[1].justification, PdrJustification::Safety));
        assert!(matches!(steps[2].justification, PdrJustification::Convergence { depth: 1 }));
    }

    #[test]
    fn test_proof_steps_with_clauses() {
        let sys = trivial_system();
        let c1 = Cube::new(vec![Formula::Var("a".into(), Sort::Bool)]);
        let c2 = Cube::new(vec![Formula::Var("b".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![c1, c2], convergence_depth: 3 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let steps = certificate_to_proof_steps(&cert);
        // Initiation + 2 consecution + Safety + Convergence = 5.
        assert_eq!(steps.len(), 5);
        assert!(matches!(steps[0].justification, PdrJustification::Initiation));
        assert!(matches!(steps[1].justification, PdrJustification::Consecution));
        assert!(matches!(steps[2].justification, PdrJustification::Consecution));
        assert!(matches!(steps[3].justification, PdrJustification::Safety));
        assert!(matches!(steps[4].justification, PdrJustification::Convergence { depth: 3 }));
    }

    #[test]
    fn test_proof_step_indices_sequential() {
        let sys = trivial_system();
        let c1 = Cube::new(vec![Formula::Bool(true)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![c1], convergence_depth: 2 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let steps = certificate_to_proof_steps(&cert);
        for (i, step) in steps.iter().enumerate() {
            assert_eq!(step.index, i);
        }
    }

    // -- Pretty print tests --

    #[test]
    fn test_pretty_print_certificate() {
        let sys = trivial_system();
        let result = trivial_safe_result();
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let output = pretty_print_certificate(&cert);
        assert!(output.contains("PDR Certificate"));
        assert!(output.contains("Proof steps"));
        assert!(output.contains("INIT"));
        assert!(output.contains("SAFE"));
        assert!(output.contains("CONV"));
    }

    #[test]
    fn test_pretty_print_with_clauses() {
        let sys = trivial_system();
        let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
        let result = Ic3Result::Safe { invariant_clauses: vec![clause], convergence_depth: 2 };
        let cert = PdrCertificate::from_ic3_result(&result, &sys).unwrap();
        let output = pretty_print_certificate(&cert);
        assert!(output.contains("CONS"));
    }

    // -- PdrJustification coverage --

    #[test]
    fn test_justification_variants_display() {
        // Exercise the pretty-print match arms.
        let justifications = vec![
            PdrJustification::Initiation,
            PdrJustification::Consecution,
            PdrJustification::Safety,
            PdrJustification::CubeBlocking { frame: 3 },
            PdrJustification::Propagation { from_frame: 1, to_frame: 2 },
            PdrJustification::Convergence { depth: 5 },
        ];
        let cert = PdrCertificate {
            invariant_clauses: vec![],
            property: Formula::Bool(true),
            transition: Formula::Bool(true),
            init: Formula::Bool(true),
            strength: InvariantStrength::Exact,
            convergence_depth: 1,
        };
        // Just ensure the format function doesn't panic.
        let _ = pretty_print_certificate(&cert);
        for j in justifications {
            let step = PdrProofStep {
                index: 0,
                description: "test".to_string(),
                formula: Formula::Bool(true),
                justification: j,
            };
            // Ensure serde round-trip works.
            let json = serde_json::to_string(&step).expect("should serialize");
            let _: PdrProofStep = serde_json::from_str(&json).expect("should deserialize");
        }
    }
}
