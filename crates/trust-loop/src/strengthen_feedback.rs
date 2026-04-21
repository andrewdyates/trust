// trust-loop/strengthen_feedback.rs: Strengthening feedback correlation (#470)
//
// Correlates spec proposals to proof outcomes, determining which proposals
// actually led to successful proofs. Feeds results back into the strategy
// selector to improve future proposal quality.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::{VerificationCondition, VerificationResult};

use crate::vc_tracker::{VcStatus, vc_slot_key};

/// Outcome of a single proposal after re-verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProposalEffect {
    /// The proposal's target VC improved (went from non-proved to proved).
    Effective,
    /// The proposal was applied but the target VC did not improve.
    Ineffective,
    /// The proposal's target VC actually got worse (regression).
    Regressive,
    /// Cannot determine the effect (e.g., target VC not found in results).
    Inconclusive,
}

/// Result of correlating a proposal to its verification outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProposalCorrelation {
    /// The function targeted by the proposal.
    pub function_name: String,
    /// The effect of the proposal on its target VC.
    pub effect: ProposalEffect,
    /// VC key that was targeted, if identifiable.
    pub target_vc_key: Option<String>,
}

/// Summary of proposal effectiveness across an iteration.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StrengthenEffectiveness {
    /// Total proposals applied this iteration.
    pub proposals_applied: usize,
    /// Proposals that led to a proof (Effective).
    pub proposals_effective: usize,
    /// Proposals that had no effect (Ineffective).
    pub proposals_ineffective: usize,
    /// Proposals that caused regression (Regressive).
    pub proposals_regressive: usize,
    /// Proposals whose effect is unknown (Inconclusive).
    pub proposals_inconclusive: usize,
}

impl StrengthenEffectiveness {
    /// Effectiveness rate: effective / applied.
    #[must_use]
    pub fn effectiveness_rate(&self) -> f64 {
        if self.proposals_applied == 0 {
            return 0.0;
        }
        self.proposals_effective as f64 / self.proposals_applied as f64
    }

    /// Whether any proposals caused regressions.
    #[must_use]
    pub fn has_regressions(&self) -> bool {
        self.proposals_regressive > 0
    }
}

/// Correlate proposals to their proof outcomes.
///
/// Compares the pre-strengthening results with post-strengthening results
/// to determine which proposals were effective.
///
/// # Arguments
/// * `pre_results` - Verification results from BEFORE strengthening was applied.
/// * `post_results` - Verification results from AFTER strengthening was applied.
/// * `proposal_functions` - Function names that had proposals applied.
#[must_use]
pub fn correlate_proposals(
    pre_results: &[(VerificationCondition, VerificationResult)],
    post_results: &[(VerificationCondition, VerificationResult)],
    proposal_functions: &[String],
) -> Vec<ProposalCorrelation> {
    // Build lookup maps: vc_key -> status
    let pre_statuses: BTreeMap<String, VcStatus> = pre_results
        .iter()
        .map(|(vc, result)| (vc_slot_key(vc), VcStatus::from_result(result)))
        .collect();

    let post_statuses: BTreeMap<String, VcStatus> = post_results
        .iter()
        .map(|(vc, result)| (vc_slot_key(vc), VcStatus::from_result(result)))
        .collect();

    let mut correlations = Vec::new();

    for function in proposal_functions {
        // Find VCs belonging to this function in post-results.
        let function_vcs: Vec<&String> = post_statuses
            .keys()
            .filter(|key| key.starts_with(&format!("{function}|")))
            .collect();

        if function_vcs.is_empty() {
            correlations.push(ProposalCorrelation {
                function_name: function.clone(),
                effect: ProposalEffect::Inconclusive,
                target_vc_key: None,
            });
            continue;
        }

        // Check each VC for this function.
        let mut any_effective = false;
        let mut any_regressive = false;
        let mut best_key = None;

        for vc_key in &function_vcs {
            let pre = pre_statuses.get(*vc_key);
            let post = post_statuses.get(*vc_key);

            match (pre, post) {
                (Some(pre_status), Some(post_status)) => {
                    if !pre_status.is_proved() && post_status.is_proved() {
                        any_effective = true;
                        best_key = Some((*vc_key).clone());
                    } else if pre_status.is_proved() && !post_status.is_proved() {
                        any_regressive = true;
                        best_key = Some((*vc_key).clone());
                    }
                }
                (None, Some(post_status)) if post_status.is_proved() => {
                    // New VC that is proved — could be from the proposal.
                    any_effective = true;
                    best_key = Some((*vc_key).clone());
                }
                _ => {}
            }
        }

        let effect = if any_regressive {
            ProposalEffect::Regressive
        } else if any_effective {
            ProposalEffect::Effective
        } else {
            ProposalEffect::Ineffective
        };

        correlations.push(ProposalCorrelation {
            function_name: function.clone(),
            effect,
            target_vc_key: best_key,
        });
    }

    correlations
}

/// Summarize the effectiveness of a set of correlations.
#[must_use]
pub fn summarize_effectiveness(correlations: &[ProposalCorrelation]) -> StrengthenEffectiveness {
    let mut summary = StrengthenEffectiveness {
        proposals_applied: correlations.len(),
        ..Default::default()
    };

    for corr in correlations {
        match corr.effect {
            ProposalEffect::Effective => summary.proposals_effective += 1,
            ProposalEffect::Ineffective => summary.proposals_ineffective += 1,
            ProposalEffect::Regressive => summary.proposals_regressive += 1,
            ProposalEffect::Inconclusive => summary.proposals_inconclusive += 1,
        }
    }

    summary
}

/// Compute strategy weight updates based on proposal effectiveness.
///
/// Returns a map of function_name -> reward in [0.0, 1.0].
/// Effective proposals get 1.0, Ineffective get 0.0, Regressive get -0.5
/// (clamped to 0.0 for non-negative reward systems).
#[must_use]
pub fn compute_strategy_rewards(
    correlations: &[ProposalCorrelation],
) -> BTreeMap<String, f64> {
    let mut rewards = BTreeMap::new();

    for corr in correlations {
        let reward = match corr.effect {
            ProposalEffect::Effective => 1.0,
            ProposalEffect::Ineffective => 0.0,
            ProposalEffect::Regressive => 0.0,
            ProposalEffect::Inconclusive => 0.25,
        };
        rewards.insert(corr.function_name.clone(), reward);
    }

    rewards
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, ProofStrength, Sort, SourceSpan, VcKind};

    fn make_vc(function: &str, kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            function: function.to_string(),
            kind,
            location: SourceSpan::default(),
            formula: Formula::Var("x".to_string(), Sort::Bool),
            contract_metadata: None,
        }
    }

    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".to_string(),
            strength: ProofStrength::smt_unsat(),
            time_ms: 1,
        proof_certificate: None,
                solver_warnings: None,
        }
    }

    fn failed() -> VerificationResult {
        VerificationResult::Failed {
            solver: "z4".to_string(),
            counterexample: None,
            time_ms: 1,
        }
    }

    // --- correlate_proposals ---

    #[test]
    fn test_correlate_effective_proposal() {
        let vc_a = make_vc("crate::f", VcKind::DivisionByZero);
        let pre = vec![(vc_a.clone(), failed())];
        let post = vec![(vc_a, proved())];
        let functions = vec!["crate::f".to_string()];

        let correlations = correlate_proposals(&pre, &post, &functions);
        assert_eq!(correlations.len(), 1);
        assert_eq!(correlations[0].effect, ProposalEffect::Effective);
        assert!(correlations[0].target_vc_key.is_some());
    }

    #[test]
    fn test_correlate_ineffective_proposal() {
        let vc_a = make_vc("crate::f", VcKind::DivisionByZero);
        let pre = vec![(vc_a.clone(), failed())];
        let post = vec![(vc_a, failed())];
        let functions = vec!["crate::f".to_string()];

        let correlations = correlate_proposals(&pre, &post, &functions);
        assert_eq!(correlations.len(), 1);
        assert_eq!(correlations[0].effect, ProposalEffect::Ineffective);
    }

    #[test]
    fn test_correlate_regressive_proposal() {
        let vc_a = make_vc("crate::f", VcKind::DivisionByZero);
        let pre = vec![(vc_a.clone(), proved())];
        let post = vec![(vc_a, failed())];
        let functions = vec!["crate::f".to_string()];

        let correlations = correlate_proposals(&pre, &post, &functions);
        assert_eq!(correlations.len(), 1);
        assert_eq!(correlations[0].effect, ProposalEffect::Regressive);
    }

    #[test]
    fn test_correlate_inconclusive_missing_function() {
        let pre: Vec<(VerificationCondition, VerificationResult)> = vec![];
        let post: Vec<(VerificationCondition, VerificationResult)> = vec![];
        let functions = vec!["crate::missing".to_string()];

        let correlations = correlate_proposals(&pre, &post, &functions);
        assert_eq!(correlations.len(), 1);
        assert_eq!(correlations[0].effect, ProposalEffect::Inconclusive);
    }

    #[test]
    fn test_correlate_multiple_functions() {
        let vc_a = make_vc("crate::f", VcKind::DivisionByZero);
        let vc_b = make_vc("crate::g", VcKind::DivisionByZero);

        let pre = vec![(vc_a.clone(), failed()), (vc_b.clone(), failed())];
        let post = vec![(vc_a, proved()), (vc_b, failed())];
        let functions = vec!["crate::f".to_string(), "crate::g".to_string()];

        let correlations = correlate_proposals(&pre, &post, &functions);
        assert_eq!(correlations.len(), 2);
        assert_eq!(correlations[0].effect, ProposalEffect::Effective);
        assert_eq!(correlations[1].effect, ProposalEffect::Ineffective);
    }

    // --- summarize_effectiveness ---

    #[test]
    fn test_summarize_effectiveness() {
        let correlations = vec![
            ProposalCorrelation {
                function_name: "f".to_string(),
                effect: ProposalEffect::Effective,
                target_vc_key: None,
            },
            ProposalCorrelation {
                function_name: "g".to_string(),
                effect: ProposalEffect::Ineffective,
                target_vc_key: None,
            },
            ProposalCorrelation {
                function_name: "h".to_string(),
                effect: ProposalEffect::Effective,
                target_vc_key: None,
            },
            ProposalCorrelation {
                function_name: "i".to_string(),
                effect: ProposalEffect::Regressive,
                target_vc_key: None,
            },
        ];

        let summary = summarize_effectiveness(&correlations);
        assert_eq!(summary.proposals_applied, 4);
        assert_eq!(summary.proposals_effective, 2);
        assert_eq!(summary.proposals_ineffective, 1);
        assert_eq!(summary.proposals_regressive, 1);
        assert_eq!(summary.proposals_inconclusive, 0);
        assert!((summary.effectiveness_rate() - 0.5).abs() < 1e-10);
        assert!(summary.has_regressions());
    }

    #[test]
    fn test_summarize_empty() {
        let summary = summarize_effectiveness(&[]);
        assert_eq!(summary.proposals_applied, 0);
        assert!(!summary.has_regressions());
        assert!(summary.effectiveness_rate().abs() < 1e-10);
    }

    // --- compute_strategy_rewards ---

    #[test]
    fn test_compute_strategy_rewards() {
        let correlations = vec![
            ProposalCorrelation {
                function_name: "f".to_string(),
                effect: ProposalEffect::Effective,
                target_vc_key: None,
            },
            ProposalCorrelation {
                function_name: "g".to_string(),
                effect: ProposalEffect::Ineffective,
                target_vc_key: None,
            },
        ];

        let rewards = compute_strategy_rewards(&correlations);
        assert!((rewards["f"] - 1.0).abs() < 1e-10);
        assert!(rewards["g"].abs() < 1e-10);
    }

    // --- StrengthenEffectiveness ---

    #[test]
    fn test_effectiveness_rate_all_effective() {
        let eff = StrengthenEffectiveness {
            proposals_applied: 3,
            proposals_effective: 3,
            ..Default::default()
        };
        assert!((eff.effectiveness_rate() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_effectiveness_rate_none_applied() {
        let eff = StrengthenEffectiveness::default();
        assert!(eff.effectiveness_rate().abs() < 1e-10);
    }
}
