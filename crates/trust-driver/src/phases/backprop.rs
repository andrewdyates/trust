// trust-driver/phases/backprop.rs: Production BackpropPhase bridging to trust-backprop.
//
// Converts strengthen proposals into source rewrites via trust_backprop::apply_plan(),
// then applies them to files via trust_backprop::apply_plan_to_files().
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use trust_backprop::GovernancePolicy;
use trust_strengthen::Proposal;

use crate::{BackpropOutput, BackpropPhase};

/// Production backprop phase that bridges to `trust_backprop`.
///
/// Converts proposals from the strengthen phase into source rewrites
/// and applies them to files on disk. Uses a `GovernancePolicy` to
/// filter proposals (default: permissive, non-strict).
#[derive(Debug, Clone)]
pub struct ProductionBackpropPhase {
    policy: GovernancePolicy,
}

impl ProductionBackpropPhase {
    /// Create a new production backprop phase with the given governance policy.
    #[must_use]
    pub fn new(policy: GovernancePolicy) -> Self {
        Self { policy }
    }
}

impl Default for ProductionBackpropPhase {
    fn default() -> Self {
        Self::new(GovernancePolicy::default())
    }
}

impl BackpropPhase for ProductionBackpropPhase {
    fn backpropagate(&self, _source_path: &Path, proposals: &[Proposal]) -> BackpropOutput {
        if proposals.is_empty() {
            return BackpropOutput {
                applied: 0,
                skipped: 0,
            };
        }

        // Step 1: Convert proposals to a rewrite plan via governance-checked apply_plan
        let plan = match trust_backprop::apply_plan(proposals, &self.policy) {
            Ok(plan) => plan,
            Err(_) => {
                // Governance or conversion error — skip all proposals gracefully
                return BackpropOutput {
                    applied: 0,
                    skipped: proposals.len(),
                };
            }
        };

        if plan.is_empty() {
            // All proposals were filtered by governance
            return BackpropOutput {
                applied: 0,
                skipped: proposals.len(),
            };
        }

        let rewrite_count = plan.len();

        // Step 2: Apply the rewrite plan to source files on disk
        match trust_backprop::apply_plan_to_files(&plan) {
            Ok(results) => {
                let files_modified = results.len();
                // applied = number of rewrites successfully written
                // We use rewrite_count since apply_plan_to_files succeeds atomically per file
                let applied = if files_modified > 0 { rewrite_count } else { 0 };
                BackpropOutput {
                    applied,
                    skipped: proposals.len().saturating_sub(applied),
                }
            }
            Err(_) => {
                // File I/O error — report all as skipped
                BackpropOutput {
                    applied: 0,
                    skipped: proposals.len(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_strengthen::ProposalKind;

    fn make_proposal(func: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: format!("test::{func}"),
            function_name: func.into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: spec.into(),
            },
            confidence: 0.9,
            rationale: "test proposal".into(),
        }
    }

    #[test]
    fn test_production_backprop_empty_proposals() {
        let phase = ProductionBackpropPhase::default();
        let path = Path::new("/tmp/test.rs");
        let output = phase.backpropagate(path, &[]);
        assert_eq!(output.applied, 0);
        assert_eq!(output.skipped, 0);
    }

    #[test]
    fn test_production_backprop_governance_filters_protected() {
        let policy = GovernancePolicy {
            strict: false,
            protected_functions: vec!["critical_fn".into()],
            ..Default::default()
        };
        let phase = ProductionBackpropPhase::new(policy);
        let proposals = vec![make_proposal("critical_fn", "x > 0")];
        let path = Path::new("/tmp/test.rs");
        let output = phase.backpropagate(path, &proposals);
        // Governance filters the proposal in non-strict mode -> empty plan -> all skipped
        assert_eq!(output.applied, 0);
        assert_eq!(output.skipped, 1);
    }

    #[test]
    fn test_production_backprop_governance_strict_error() {
        let policy = GovernancePolicy {
            strict: true,
            protected_functions: vec!["locked_fn".into()],
            ..Default::default()
        };
        let phase = ProductionBackpropPhase::new(policy);
        let proposals = vec![make_proposal("locked_fn", "x > 0")];
        let path = Path::new("/tmp/test.rs");
        let output = phase.backpropagate(path, &proposals);
        // Strict mode returns error from apply_plan -> gracefully returns all skipped
        assert_eq!(output.applied, 0);
        assert_eq!(output.skipped, 1);
    }

    #[test]
    fn test_production_backprop_default_is_permissive() {
        let phase = ProductionBackpropPhase::default();
        assert!(!phase.policy.strict);
        assert!(phase.policy.protected_functions.is_empty());
    }

    #[test]
    fn test_production_backprop_file_io_error_graceful() {
        // Proposals that pass governance but point to nonexistent files
        // will fail at apply_plan_to_files -> gracefully skipped
        let phase = ProductionBackpropPhase::default();
        let proposals = vec![make_proposal("some_fn", "x > 0")];
        let path = Path::new("/nonexistent/test.rs");
        let output = phase.backpropagate(path, &proposals);
        // apply_plan succeeds (governance OK), but the rewrite plan has
        // file_path = "test::some_fn" which doesn't exist on disk ->
        // apply_plan_to_files fails -> all skipped
        assert_eq!(output.applied, 0);
        assert_eq!(output.skipped, 1);
    }
}
