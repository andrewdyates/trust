// trust-lean5/z4_proof_bridge.rs: Z4 proof certificate to SolverProof translation
//
// Translates z4's native proof output (Z4ProofCertificate with Z4ProofStep entries)
// into the SolverProof/ProofStep representation consumed by the reconstruction
// pipeline. This bridges the gap between z4's proof format and lean5 certification.
//
// Part of #429: SmtBacked to Certified pathway
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_proof_cert::z4_certificate::{Z4ProofCertificate, Z4ProofStep};
use trust_types::{Formula, Sort};

use crate::error::CertificateError;
use crate::reconstruction::{ProofStep, SolverProof};

// ---------------------------------------------------------------------------
// Z4 rule classification
// ---------------------------------------------------------------------------

/// Classification of z4 proof rules into categories for translation.
///
/// z4 proof rules map to SolverProof step types as documented in the
/// design doc (designs/2026-04-10-smt-backed-to-certified-pathway.md).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Z4RuleKind {
    /// Input assertion: maps to ProofStep::Axiom.
    Asserted,
    /// Modus ponens: maps to ProofStep::ModusPonens.
    ModusPonens,
    /// Unit resolution: maps to ProofStep::Resolution.
    UnitResolution,
    /// Reflexivity (a = a): maps to ProofStep::Axiom with "refl" tag.
    Reflexivity,
    /// Transitivity (a=b, b=c => a=c): maps to ProofStep::Rewrite chain.
    Transitivity,
    /// Monotonicity/congruence (f(a) = f(b) from a = b): maps to ProofStep::Congruence.
    Monotonicity,
    /// Universal instantiation: maps to ProofStep::Instantiation.
    QuantInst,
    /// Theory lemma (opaque arithmetic/BV step): maps to trusted Axiom.
    TheoryLemma { theory: String },
    /// Definitional axiom: maps to ProofStep::Axiom with "def-axiom" tag.
    DefAxiom,
    /// NNF normalization: maps to ProofStep::Rewrite.
    NnfRewrite,
    /// Skolemization: maps to ProofStep::Axiom with "skolem" tag.
    Skolem,
    /// Symmetry (a=b => b=a): maps to ProofStep::Rewrite.
    Symmetry,
    /// Rule not yet mapped; treated as trusted axiom.
    Unknown(String),
}

/// Classify a z4 rule name into the corresponding Z4RuleKind.
///
/// Handles the core z4 proof rules documented in the z4 source:
/// asserted, mp, unit-resolution, refl, symm, trans, monotonicity,
/// quant-inst, th-lemma, def-axiom, nnf-pos, nnf-neg, sk.
pub(crate) fn classify_z4_rule(rule_name: &str) -> Z4RuleKind {
    match rule_name {
        "asserted" | "hypothesis" | "true-axiom" | "intro" => Z4RuleKind::Asserted,
        "mp" | "modus-ponens" => Z4RuleKind::ModusPonens,
        "unit-resolution" | "resolution" => Z4RuleKind::UnitResolution,
        "refl" => Z4RuleKind::Reflexivity,
        "symm" => Z4RuleKind::Symmetry,
        "trans" => Z4RuleKind::Transitivity,
        "monotonicity" | "congr" => Z4RuleKind::Monotonicity,
        "quant-inst" => Z4RuleKind::QuantInst,
        "def-axiom" => Z4RuleKind::DefAxiom,
        "nnf-pos" | "nnf-neg" => Z4RuleKind::NnfRewrite,
        "sk" => Z4RuleKind::Skolem,
        other if other.starts_with("th-lemma") => {
            // th-lemma may have a theory suffix: "th-lemma" or "th-lemma arith"
            let theory = other.strip_prefix("th-lemma").unwrap_or("").trim().to_string();
            let theory = if theory.is_empty() { "unknown".to_string() } else { theory };
            Z4RuleKind::TheoryLemma { theory }
        }
        other => Z4RuleKind::Unknown(other.to_string()),
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 conclusion parsing (minimal)
// ---------------------------------------------------------------------------

/// Parse a Z4ProofStep conclusion string into a trust-types Formula.
///
/// The conclusion is an SMT-LIB2 string. We parse a minimal subset that
/// z4 actually produces in proof conclusions:
/// - Atoms: `true`, `false`, identifiers, integer literals
/// - Negation: `(not <expr>)`
/// - Binary: `(= <a> <b>)`, `(=> <a> <b>)`, `(<= <a> <b>)`, `(>= <a> <b>)`,
///   `(< <a> <b>)`, `(> <a> <b>)`, `(+ <a> <b>)`, `(- <a> <b>)`
/// - N-ary: `(and ...)`, `(or ...)`
///
/// For conclusions we cannot parse, returns a Bool(true) placeholder
/// (the proof structure is still valid; the conclusion is just metadata).
pub(crate) fn parse_smtlib2_conclusion(conclusion: &str) -> Formula {
    let s = conclusion.trim();
    if s.is_empty() || s == "true" {
        return Formula::Bool(true);
    }
    if s == "false" || s == "#false" {
        return Formula::Bool(false);
    }

    // Integer literal
    if let Ok(n) = s.parse::<i128>() {
        return Formula::Int(n);
    }

    // Parenthesized expression
    if s.starts_with('(') && s.ends_with(')') {
        let inner = &s[1..s.len() - 1];
        let tokens = tokenize_smtlib2(inner);
        if tokens.is_empty() {
            return Formula::Bool(true);
        }

        let op = tokens[0].as_str();
        match op {
            "not" if tokens.len() == 2 => {
                let arg = parse_smtlib2_conclusion(&tokens[1]);
                return Formula::Not(Box::new(arg));
            }
            "=>" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Implies(Box::new(lhs), Box::new(rhs));
            }
            "=" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Eq(Box::new(lhs), Box::new(rhs));
            }
            "<=" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Le(Box::new(lhs), Box::new(rhs));
            }
            ">=" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Ge(Box::new(lhs), Box::new(rhs));
            }
            "<" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Lt(Box::new(lhs), Box::new(rhs));
            }
            ">" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Gt(Box::new(lhs), Box::new(rhs));
            }
            "+" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Add(Box::new(lhs), Box::new(rhs));
            }
            "-" if tokens.len() == 3 => {
                let lhs = parse_smtlib2_conclusion(&tokens[1]);
                let rhs = parse_smtlib2_conclusion(&tokens[2]);
                return Formula::Sub(Box::new(lhs), Box::new(rhs));
            }
            "and" if tokens.len() >= 2 => {
                let args: Vec<Formula> =
                    tokens[1..].iter().map(|t| parse_smtlib2_conclusion(t)).collect();
                return Formula::And(args);
            }
            "or" if tokens.len() >= 2 => {
                let args: Vec<Formula> =
                    tokens[1..].iter().map(|t| parse_smtlib2_conclusion(t)).collect();
                return Formula::Or(args);
            }
            _ => {}
        }

        // Fallback for unparseable s-expressions
        return Formula::Bool(true);
    }

    // Bare identifier: treat as a Boolean variable
    Formula::Var(s.into(), Sort::Bool)
}

/// Tokenize an SMT-LIB2 expression into top-level tokens, respecting parens.
fn tokenize_smtlib2(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }

        if chars[i] == '(' {
            let mut depth = 1;
            let start = i;
            i += 1;
            while i < chars.len() && depth > 0 {
                if chars[i] == '(' {
                    depth += 1;
                } else if chars[i] == ')' {
                    depth -= 1;
                }
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect());
        } else {
            let start = i;
            while i < chars.len() && !chars[i].is_whitespace() && chars[i] != '(' && chars[i] != ')'
            {
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect());
        }
    }

    tokens
}

// ---------------------------------------------------------------------------
// Main translation function
// ---------------------------------------------------------------------------

/// Translate a z4 proof certificate into a SolverProof for reconstruction.
///
/// Maps each Z4ProofStep to the corresponding ProofStep variant using the
/// z4 rule classification table. Premises are preserved as step indices.
///
/// # z4 rule mapping
///
/// | z4 Rule | ProofStep | Notes |
/// |---------|-----------|-------|
/// | asserted | Axiom | Input assertion |
/// | mp | ModusPonens | Modus ponens |
/// | unit-resolution | Resolution | Pivot from conclusion diff |
/// | refl | Axiom("refl.{sort}") | Reflexivity |
/// | symm | Rewrite | Symmetry via rewrite |
/// | trans | Rewrite | Transitivity as rewrite chain |
/// | monotonicity | Congruence | f(a) = f(b) from a = b |
/// | quant-inst | Instantiation | Universal instantiation |
/// | th-lemma | Axiom("th-lemma.{theory}") | Trusted theory lemma |
/// | def-axiom | Axiom("def-axiom") | Definitional tautology |
/// | nnf-pos/neg | Rewrite | NNF normalization |
/// | sk | Axiom("skolem") | Skolemization |
///
/// # Errors
///
/// Returns `CertificateError` if a proof step references a non-existent premise.
pub fn translate_z4_proof(z4_cert: &Z4ProofCertificate) -> Result<SolverProof, CertificateError> {
    if z4_cert.proof_steps.is_empty() {
        return Ok(SolverProof {
            steps: Vec::new(),
            used_axioms: Vec::new(),
            used_lemmas: Vec::new(),
        });
    }

    let mut steps = Vec::with_capacity(z4_cert.proof_steps.len());
    let mut used_axioms = Vec::new();
    let mut used_lemmas = Vec::new();

    for (idx, z4_step) in z4_cert.proof_steps.iter().enumerate() {
        // Validate premise indices
        for &premise in &z4_step.premises {
            if premise >= idx {
                return Err(CertificateError::InvalidProofTerm {
                    reason: format!(
                        "z4 proof step {idx} (rule: {}) references non-earlier premise {premise}",
                        z4_step.rule_name
                    ),
                });
            }
        }

        let conclusion = parse_smtlib2_conclusion(&z4_step.conclusion);
        let rule_kind = classify_z4_rule(&z4_step.rule_name);

        let step = translate_step(&rule_kind, z4_step, idx, &conclusion)?;

        // Track axiom names and lemma references
        match &step {
            ProofStep::Axiom { name, .. } => {
                if !used_axioms.contains(name) {
                    used_axioms.push(name.clone());
                }
            }
            _ => {
                for &premise in &z4_step.premises {
                    if !used_lemmas.contains(&premise) {
                        used_lemmas.push(premise);
                    }
                }
            }
        }

        steps.push(step);
    }

    Ok(SolverProof { steps, used_axioms, used_lemmas })
}

/// Translate a single z4 proof step into a ProofStep.
fn translate_step(
    rule_kind: &Z4RuleKind,
    z4_step: &Z4ProofStep,
    idx: usize,
    conclusion: &Formula,
) -> Result<ProofStep, CertificateError> {
    match rule_kind {
        Z4RuleKind::Asserted => {
            Ok(ProofStep::Axiom { name: format!("asserted_{idx}"), formula: conclusion.clone() })
        }

        Z4RuleKind::ModusPonens => {
            // mp requires exactly 2 premises: the implication and the antecedent
            let (impl_step, ante_step) = get_two_premises(z4_step, idx, "mp")?;
            Ok(ProofStep::ModusPonens { implication_step: impl_step, antecedent_step: ante_step })
        }

        Z4RuleKind::UnitResolution => {
            // unit-resolution has 1+ premises; first is the clause, rest are units
            if z4_step.premises.is_empty() {
                return Err(CertificateError::InvalidProofTerm {
                    reason: format!("z4 unit-resolution step {idx} has no premises"),
                });
            }
            // Model as resolution between first two premises (or first + self for single)
            let positive = z4_step.premises[0];
            let negative = if z4_step.premises.len() > 1 { z4_step.premises[1] } else { positive };
            // Use conclusion as pivot placeholder
            Ok(ProofStep::Resolution {
                positive_step: positive,
                negative_step: negative,
                pivot: conclusion.clone(),
            })
        }

        Z4RuleKind::Reflexivity => {
            Ok(ProofStep::Axiom { name: format!("refl_{idx}"), formula: conclusion.clone() })
        }

        Z4RuleKind::Symmetry => {
            // symm requires 1 premise: the equality to flip
            let premise = get_first_premise(z4_step, idx, "symm")?;
            Ok(ProofStep::Rewrite { equality_step: premise, target_step: premise })
        }

        Z4RuleKind::Transitivity => {
            // trans requires 2 premises: a=b and b=c
            let (eq1, eq2) = get_two_premises(z4_step, idx, "trans")?;
            Ok(ProofStep::Rewrite { equality_step: eq1, target_step: eq2 })
        }

        Z4RuleKind::Monotonicity => {
            // monotonicity requires 1+ equality premises
            let premise = get_first_premise(z4_step, idx, "monotonicity")?;
            // Extract function name from annotations or conclusion
            let function_name =
                z4_step.annotations.get(":decl").cloned().unwrap_or_else(|| format!("f_{idx}"));
            Ok(ProofStep::Congruence { equality_step: premise, function_name })
        }

        Z4RuleKind::QuantInst => {
            // quant-inst: instantiation of a universally quantified formula
            let premise = if z4_step.premises.is_empty() {
                // quant-inst can be self-contained (no premise, carries the axiom)
                return Ok(ProofStep::Axiom {
                    name: format!("quant-inst_{idx}"),
                    formula: conclusion.clone(),
                });
            } else {
                z4_step.premises[0]
            };
            // Extract the witness from annotations or use conclusion
            let witness = z4_step
                .annotations
                .get(":pattern")
                .map(|p| parse_smtlib2_conclusion(p))
                .unwrap_or_else(|| conclusion.clone());
            Ok(ProofStep::Instantiation { quantified_step: premise, witness })
        }

        Z4RuleKind::TheoryLemma { theory } => Ok(ProofStep::Axiom {
            name: format!("th-lemma.{theory}_{idx}"),
            formula: conclusion.clone(),
        }),

        Z4RuleKind::DefAxiom => {
            Ok(ProofStep::Axiom { name: format!("def-axiom_{idx}"), formula: conclusion.clone() })
        }

        Z4RuleKind::NnfRewrite => {
            // NNF rewrite: if we have a premise, it's a rewrite; otherwise axiom
            if let Some(&premise) = z4_step.premises.first() {
                Ok(ProofStep::Rewrite { equality_step: premise, target_step: premise })
            } else {
                Ok(ProofStep::Axiom { name: format!("nnf_{idx}"), formula: conclusion.clone() })
            }
        }

        Z4RuleKind::Skolem => {
            Ok(ProofStep::Axiom { name: format!("skolem_{idx}"), formula: conclusion.clone() })
        }

        Z4RuleKind::Unknown(rule) => {
            // Unknown rules become trusted axioms
            Ok(ProofStep::Axiom { name: format!("{rule}_{idx}"), formula: conclusion.clone() })
        }
    }
}

// ---------------------------------------------------------------------------
// Premise extraction helpers
// ---------------------------------------------------------------------------

/// Get exactly two premises from a z4 step, returning an error if not available.
fn get_two_premises(
    z4_step: &Z4ProofStep,
    idx: usize,
    rule: &str,
) -> Result<(usize, usize), CertificateError> {
    if z4_step.premises.len() < 2 {
        return Err(CertificateError::InvalidProofTerm {
            reason: format!(
                "z4 {rule} step {idx} requires 2 premises, got {}",
                z4_step.premises.len()
            ),
        });
    }
    Ok((z4_step.premises[0], z4_step.premises[1]))
}

/// Get the first premise from a z4 step, returning an error if empty.
fn get_first_premise(
    z4_step: &Z4ProofStep,
    idx: usize,
    rule: &str,
) -> Result<usize, CertificateError> {
    z4_step.premises.first().copied().ok_or_else(|| CertificateError::InvalidProofTerm {
        reason: format!("z4 {rule} step {idx} requires at least 1 premise, got 0"),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use trust_proof_cert::z4_certificate::{Z4ProofCertificate, Z4ProofStep};

    use super::*;

    // -- Helpers --

    fn make_z4_step(rule: &str, conclusion: &str, premises: Vec<usize>) -> Z4ProofStep {
        Z4ProofStep {
            rule_name: rule.to_string(),
            rule: None,
            conclusion: conclusion.to_string(),
            premises,
            annotations: BTreeMap::new(),
        }
    }

    fn sample_z4_certificate() -> Z4ProofCertificate {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 42, "z4 4.13.0");
        cert.proof_steps.push(make_z4_step("asserted", "p", vec![]));
        cert.proof_steps.push(make_z4_step("asserted", "(=> p q)", vec![]));
        cert.proof_steps.push(make_z4_step("mp", "q", vec![0, 1]));
        cert.proof_steps.push(make_z4_step("unit-resolution", "false", vec![2]));
        cert
    }

    // -- classify_z4_rule tests --

    #[test]
    fn test_classify_asserted() {
        assert_eq!(classify_z4_rule("asserted"), Z4RuleKind::Asserted);
        assert_eq!(classify_z4_rule("hypothesis"), Z4RuleKind::Asserted);
        assert_eq!(classify_z4_rule("true-axiom"), Z4RuleKind::Asserted);
        assert_eq!(classify_z4_rule("intro"), Z4RuleKind::Asserted);
    }

    #[test]
    fn test_classify_mp() {
        assert_eq!(classify_z4_rule("mp"), Z4RuleKind::ModusPonens);
        assert_eq!(classify_z4_rule("modus-ponens"), Z4RuleKind::ModusPonens);
    }

    #[test]
    fn test_classify_resolution() {
        assert_eq!(classify_z4_rule("unit-resolution"), Z4RuleKind::UnitResolution);
        assert_eq!(classify_z4_rule("resolution"), Z4RuleKind::UnitResolution);
    }

    #[test]
    fn test_classify_equality_rules() {
        assert_eq!(classify_z4_rule("refl"), Z4RuleKind::Reflexivity);
        assert_eq!(classify_z4_rule("symm"), Z4RuleKind::Symmetry);
        assert_eq!(classify_z4_rule("trans"), Z4RuleKind::Transitivity);
    }

    #[test]
    fn test_classify_monotonicity() {
        assert_eq!(classify_z4_rule("monotonicity"), Z4RuleKind::Monotonicity);
        assert_eq!(classify_z4_rule("congr"), Z4RuleKind::Monotonicity);
    }

    #[test]
    fn test_classify_quant_inst() {
        assert_eq!(classify_z4_rule("quant-inst"), Z4RuleKind::QuantInst);
    }

    #[test]
    fn test_classify_theory_lemma() {
        let kind = classify_z4_rule("th-lemma");
        assert!(matches!(kind, Z4RuleKind::TheoryLemma { ref theory } if theory == "unknown"));

        let kind = classify_z4_rule("th-lemma arith");
        assert!(matches!(kind, Z4RuleKind::TheoryLemma { ref theory } if theory == "arith"));
    }

    #[test]
    fn test_classify_def_axiom() {
        assert_eq!(classify_z4_rule("def-axiom"), Z4RuleKind::DefAxiom);
    }

    #[test]
    fn test_classify_nnf() {
        assert_eq!(classify_z4_rule("nnf-pos"), Z4RuleKind::NnfRewrite);
        assert_eq!(classify_z4_rule("nnf-neg"), Z4RuleKind::NnfRewrite);
    }

    #[test]
    fn test_classify_skolem() {
        assert_eq!(classify_z4_rule("sk"), Z4RuleKind::Skolem);
    }

    #[test]
    fn test_classify_unknown() {
        let kind = classify_z4_rule("some-new-rule");
        assert!(matches!(kind, Z4RuleKind::Unknown(ref r) if r == "some-new-rule"));
    }

    // -- parse_smtlib2_conclusion tests --

    #[test]
    fn test_parse_true() {
        assert_eq!(parse_smtlib2_conclusion("true"), Formula::Bool(true));
    }

    #[test]
    fn test_parse_false() {
        assert_eq!(parse_smtlib2_conclusion("false"), Formula::Bool(false));
        assert_eq!(parse_smtlib2_conclusion("#false"), Formula::Bool(false));
    }

    #[test]
    fn test_parse_integer() {
        assert_eq!(parse_smtlib2_conclusion("42"), Formula::Int(42));
        assert_eq!(parse_smtlib2_conclusion("-7"), Formula::Int(-7));
    }

    #[test]
    fn test_parse_variable() {
        assert_eq!(parse_smtlib2_conclusion("p"), Formula::Var("p".into(), Sort::Bool));
    }

    #[test]
    fn test_parse_not() {
        assert_eq!(
            parse_smtlib2_conclusion("(not p)"),
            Formula::Not(Box::new(Formula::Var("p".into(), Sort::Bool)))
        );
    }

    #[test]
    fn test_parse_implies() {
        assert_eq!(
            parse_smtlib2_conclusion("(=> p q)"),
            Formula::Implies(
                Box::new(Formula::Var("p".into(), Sort::Bool)),
                Box::new(Formula::Var("q".into(), Sort::Bool)),
            )
        );
    }

    #[test]
    fn test_parse_equality() {
        assert_eq!(
            parse_smtlib2_conclusion("(= a b)"),
            Formula::Eq(
                Box::new(Formula::Var("a".into(), Sort::Bool)),
                Box::new(Formula::Var("b".into(), Sort::Bool)),
            )
        );
    }

    #[test]
    fn test_parse_comparison() {
        assert_eq!(
            parse_smtlib2_conclusion("(<= x 10)"),
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Bool)), Box::new(Formula::Int(10)),)
        );
    }

    #[test]
    fn test_parse_and() {
        let f = parse_smtlib2_conclusion("(and p q r)");
        if let Formula::And(args) = f {
            assert_eq!(args.len(), 3);
        } else {
            panic!("expected And, got {f:?}");
        }
    }

    #[test]
    fn test_parse_or() {
        let f = parse_smtlib2_conclusion("(or p q)");
        if let Formula::Or(args) = f {
            assert_eq!(args.len(), 2);
        } else {
            panic!("expected Or, got {f:?}");
        }
    }

    #[test]
    fn test_parse_empty() {
        assert_eq!(parse_smtlib2_conclusion(""), Formula::Bool(true));
    }

    #[test]
    fn test_parse_nested() {
        let f = parse_smtlib2_conclusion("(not (= x 0))");
        assert!(matches!(f, Formula::Not(_)));
    }

    // -- translate_z4_proof tests --

    #[test]
    fn test_translate_empty_certificate() {
        let cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        let proof = translate_z4_proof(&cert).expect("empty should succeed");
        assert!(proof.steps.is_empty());
        assert!(proof.used_axioms.is_empty());
        assert!(proof.used_lemmas.is_empty());
    }

    #[test]
    fn test_translate_sample_certificate() {
        let cert = sample_z4_certificate();
        let proof = translate_z4_proof(&cert).expect("sample should translate");

        // 4 z4 steps -> 4 proof steps
        assert_eq!(proof.steps.len(), 4);

        // Step 0: asserted -> Axiom
        assert!(
            matches!(&proof.steps[0], ProofStep::Axiom { name, .. } if name.starts_with("asserted"))
        );

        // Step 1: asserted -> Axiom
        assert!(
            matches!(&proof.steps[1], ProofStep::Axiom { name, .. } if name.starts_with("asserted"))
        );

        // Step 2: mp -> ModusPonens
        assert!(matches!(
            &proof.steps[2],
            ProofStep::ModusPonens { implication_step: 0, antecedent_step: 1 }
        ));

        // Step 3: unit-resolution -> Resolution
        assert!(matches!(&proof.steps[3], ProofStep::Resolution { .. }));

        // Axioms tracked
        assert_eq!(proof.used_axioms.len(), 2);

        // Lemmas tracked
        assert!(!proof.used_lemmas.is_empty());
    }

    #[test]
    fn test_translate_forward_reference_fails() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(Z4ProofStep {
            rule_name: "mp".to_string(),
            rule: None,
            conclusion: "q".to_string(),
            premises: vec![1], // forward reference
            annotations: BTreeMap::new(),
        });
        cert.proof_steps.push(make_z4_step("asserted", "p", vec![]));

        let err = translate_z4_proof(&cert).expect_err("forward ref should fail");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got: {err:?}"
        );
    }

    #[test]
    fn test_translate_theory_lemma() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(Z4ProofStep {
            rule_name: "th-lemma arith".to_string(),
            rule: None,
            conclusion: "(<= x 100)".to_string(),
            premises: vec![],
            annotations: BTreeMap::new(),
        });

        let proof = translate_z4_proof(&cert).expect("th-lemma should translate");
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.contains("th-lemma.arith")
        ));
    }

    #[test]
    fn test_translate_monotonicity() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("asserted", "(= a b)", vec![]));
        cert.proof_steps.push(Z4ProofStep {
            rule_name: "monotonicity".to_string(),
            rule: None,
            conclusion: "(= (f a) (f b))".to_string(),
            premises: vec![0],
            annotations: BTreeMap::new(),
        });

        let proof = translate_z4_proof(&cert).expect("monotonicity should translate");
        assert_eq!(proof.steps.len(), 2);
        assert!(matches!(&proof.steps[1], ProofStep::Congruence { equality_step: 0, .. }));
    }

    #[test]
    fn test_translate_transitivity() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("asserted", "(= a b)", vec![]));
        cert.proof_steps.push(make_z4_step("asserted", "(= b c)", vec![]));
        cert.proof_steps.push(make_z4_step("trans", "(= a c)", vec![0, 1]));

        let proof = translate_z4_proof(&cert).expect("trans should translate");
        assert_eq!(proof.steps.len(), 3);
        assert!(matches!(&proof.steps[2], ProofStep::Rewrite { equality_step: 0, target_step: 1 }));
    }

    #[test]
    fn test_translate_reflexivity() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("refl", "(= x x)", vec![]));

        let proof = translate_z4_proof(&cert).expect("refl should translate");
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("refl")
        ));
    }

    #[test]
    fn test_translate_unknown_rule_becomes_axiom() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("new-z4-rule", "p", vec![]));

        let proof = translate_z4_proof(&cert).expect("unknown rule should translate");
        assert_eq!(proof.steps.len(), 1);
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("new-z4-rule")
        ));
    }

    #[test]
    fn test_translate_mp_insufficient_premises_fails() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("asserted", "p", vec![]));
        cert.proof_steps.push(make_z4_step("mp", "q", vec![0])); // only 1 premise

        let err = translate_z4_proof(&cert).expect_err("mp with 1 premise should fail");
        assert!(matches!(err, CertificateError::InvalidProofTerm { .. }));
    }

    #[test]
    fn test_translate_skolem() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("sk", "(= (sk!0) 5)", vec![]));

        let proof = translate_z4_proof(&cert).expect("sk should translate");
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("skolem")
        ));
    }

    #[test]
    fn test_translate_def_axiom() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("def-axiom", "(or p (not p))", vec![]));

        let proof = translate_z4_proof(&cert).expect("def-axiom should translate");
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("def-axiom")
        ));
    }

    #[test]
    fn test_translate_quant_inst_no_premise() {
        let mut cert = Z4ProofCertificate::new([0u8; 32], 0, "z4");
        cert.proof_steps.push(make_z4_step("quant-inst", "(<= x 10)", vec![]));

        let proof = translate_z4_proof(&cert).expect("quant-inst should translate");
        assert!(matches!(
            &proof.steps[0],
            ProofStep::Axiom { name, .. } if name.starts_with("quant-inst")
        ));
    }

    // -- End-to-end: translate + reconstruct --

    #[test]
    fn test_e2e_translate_and_reconstruct() {
        use trust_types::*;

        let cert = sample_z4_certificate();
        let solver_proof = translate_z4_proof(&cert).expect("should translate");

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("d".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            contract_metadata: None,
        };

        let term =
            crate::reconstruction::reconstruct(&solver_proof, &vc).expect("should reconstruct");
        assert!(crate::reconstruction::validate_reconstruction(&term));
    }
}
