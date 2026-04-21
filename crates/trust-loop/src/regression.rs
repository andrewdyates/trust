// trust-loop/regression.rs: Regression response strategies (#470)
//
// When a regression is detected (previously-proved VC becomes non-proved),
// this module provides strategies for responding based on severity:
// - SingleVc: likely a spec conflict, try removing the newest spec
// - MultipleVc: bad batch of proposals, rollback all proposals
// - Cascading: one spec change affected many callers, isolate root cause
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::vc_tracker::RegressionEvent;

/// Classification of a regression based on severity and scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegressionSeverity {
    /// A single VC regressed. Likely a spec conflict.
    SingleVc {
        /// The regressed VC key.
        vc_key: String,
    },
    /// Multiple VCs regressed. Likely a bad batch of proposals.
    MultipleVc {
        /// Number of VCs that regressed.
        count: usize,
        /// The regressed VC keys.
        vc_keys: Vec<String>,
    },
    /// Many VCs regressed, possibly across multiple functions.
    /// Indicates a cascading failure from one spec change.
    Cascading {
        /// Number of affected VCs.
        count: usize,
        /// Unique functions affected.
        affected_functions: Vec<String>,
    },
}

/// Recommended response to a regression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RegressionResponse {
    /// Remove the newest spec for the affected function and re-verify.
    RollbackLatestSpec {
        /// Function whose spec should be rolled back.
        function: String,
    },
    /// Rollback ALL proposals from the current iteration and re-verify.
    RollbackAllProposals {
        /// Number of proposals to rollback.
        proposal_count: usize,
    },
    /// Isolate the root cause by identifying which proposal caused the cascade.
    IsolateRootCause {
        /// Functions to investigate for the root cause.
        candidate_functions: Vec<String>,
    },
    /// The regression is too severe; stop the loop immediately.
    StopLoop {
        /// Explanation of why we're stopping.
        reason: String,
    },
}

/// Threshold configuration for classifying regression severity.
#[derive(Debug, Clone)]
pub struct RegressionConfig {
    /// Number of regressed VCs above which it's classified as MultipleVc.
    pub multiple_vc_threshold: usize,
    /// Number of affected functions above which it's classified as Cascading.
    pub cascading_function_threshold: usize,
    /// Maximum number of regressions before forcing a loop stop.
    pub max_regressions_before_stop: usize,
}

impl Default for RegressionConfig {
    fn default() -> Self {
        Self {
            multiple_vc_threshold: 2,
            cascading_function_threshold: 3,
            max_regressions_before_stop: 10,
        }
    }
}

/// Classify regression events by severity.
#[must_use]
pub fn classify_regression(
    events: &[RegressionEvent],
    config: &RegressionConfig,
) -> RegressionSeverity {
    if events.is_empty() {
        // No regression events -- shouldn't happen but handle gracefully.
        return RegressionSeverity::SingleVc {
            vc_key: String::new(),
        };
    }

    // Extract unique functions from VC keys (function is the part before first '|').
    let functions: Vec<String> = events
        .iter()
        .filter_map(|e| e.vc_key.split('|').next().map(String::from))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();

    if functions.len() >= config.cascading_function_threshold {
        RegressionSeverity::Cascading {
            count: events.len(),
            affected_functions: functions,
        }
    } else if events.len() >= config.multiple_vc_threshold {
        RegressionSeverity::MultipleVc {
            count: events.len(),
            vc_keys: events.iter().map(|e| e.vc_key.clone()).collect(),
        }
    } else {
        RegressionSeverity::SingleVc {
            vc_key: events[0].vc_key.clone(),
        }
    }
}

/// Choose a response based on regression severity.
#[must_use]
pub fn choose_response(
    severity: &RegressionSeverity,
    config: &RegressionConfig,
    proposals_this_iteration: usize,
) -> RegressionResponse {
    match severity {
        RegressionSeverity::SingleVc { vc_key } => {
            // Extract function name from vc_key (part before first '|').
            let function = vc_key
                .split('|')
                .next()
                .unwrap_or(vc_key)
                .to_string();
            RegressionResponse::RollbackLatestSpec { function }
        }
        RegressionSeverity::MultipleVc { count, .. } => {
            if *count >= config.max_regressions_before_stop {
                RegressionResponse::StopLoop {
                    reason: format!(
                        "{count} VCs regressed, exceeding threshold of {}",
                        config.max_regressions_before_stop
                    ),
                }
            } else {
                RegressionResponse::RollbackAllProposals {
                    proposal_count: proposals_this_iteration,
                }
            }
        }
        RegressionSeverity::Cascading {
            count,
            affected_functions,
        } => {
            if *count >= config.max_regressions_before_stop {
                RegressionResponse::StopLoop {
                    reason: format!(
                        "cascading regression across {} functions ({count} VCs)",
                        affected_functions.len()
                    ),
                }
            } else {
                RegressionResponse::IsolateRootCause {
                    candidate_functions: affected_functions.clone(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc_tracker::VcStatus;

    fn event(vc_key: &str) -> RegressionEvent {
        RegressionEvent {
            vc_key: vc_key.to_string(),
            iteration: 2,
            previous_status: VcStatus::Proved,
            current_status: VcStatus::Failed,
        }
    }

    // --- classify_regression ---

    #[test]
    fn test_classify_single_vc() {
        let events = vec![event("crate::f|0:0:0:0:0|div_by_zero")];
        let config = RegressionConfig::default();

        let severity = classify_regression(&events, &config);
        assert!(matches!(severity, RegressionSeverity::SingleVc { .. }));
    }

    #[test]
    fn test_classify_multiple_vc() {
        let events = vec![
            event("crate::f|0:0:0:0:0|div_by_zero"),
            event("crate::f|1:0:0:0:0|overflow"),
        ];
        let config = RegressionConfig::default();

        let severity = classify_regression(&events, &config);
        match severity {
            RegressionSeverity::MultipleVc { count, .. } => {
                assert_eq!(count, 2);
            }
            other => panic!("expected MultipleVc, got {other:?}"),
        }
    }

    #[test]
    fn test_classify_cascading() {
        let events = vec![
            event("crate::f|0:0:0:0:0|div_by_zero"),
            event("crate::g|0:0:0:0:0|div_by_zero"),
            event("crate::h|0:0:0:0:0|div_by_zero"),
        ];
        let config = RegressionConfig::default();

        let severity = classify_regression(&events, &config);
        match severity {
            RegressionSeverity::Cascading {
                count,
                affected_functions,
            } => {
                assert_eq!(count, 3);
                assert_eq!(affected_functions.len(), 3);
            }
            other => panic!("expected Cascading, got {other:?}"),
        }
    }

    #[test]
    fn test_classify_empty_events() {
        let config = RegressionConfig::default();
        let severity = classify_regression(&[], &config);
        assert!(matches!(severity, RegressionSeverity::SingleVc { .. }));
    }

    // --- choose_response ---

    #[test]
    fn test_response_single_vc_rollback_spec() {
        let severity = RegressionSeverity::SingleVc {
            vc_key: "crate::f|0:0:0:0:0|div_by_zero".to_string(),
        };
        let config = RegressionConfig::default();

        let response = choose_response(&severity, &config, 3);
        match response {
            RegressionResponse::RollbackLatestSpec { function } => {
                assert_eq!(function, "crate::f");
            }
            other => panic!("expected RollbackLatestSpec, got {other:?}"),
        }
    }

    #[test]
    fn test_response_multiple_vc_rollback_all() {
        let severity = RegressionSeverity::MultipleVc {
            count: 3,
            vc_keys: vec!["a".to_string(), "b".to_string(), "c".to_string()],
        };
        let config = RegressionConfig::default();

        let response = choose_response(&severity, &config, 5);
        match response {
            RegressionResponse::RollbackAllProposals { proposal_count } => {
                assert_eq!(proposal_count, 5);
            }
            other => panic!("expected RollbackAllProposals, got {other:?}"),
        }
    }

    #[test]
    fn test_response_multiple_vc_stop_loop() {
        let severity = RegressionSeverity::MultipleVc {
            count: 15,
            vc_keys: vec![],
        };
        let config = RegressionConfig {
            max_regressions_before_stop: 10,
            ..Default::default()
        };

        let response = choose_response(&severity, &config, 5);
        assert!(matches!(response, RegressionResponse::StopLoop { .. }));
    }

    #[test]
    fn test_response_cascading_isolate() {
        let severity = RegressionSeverity::Cascading {
            count: 5,
            affected_functions: vec!["f".to_string(), "g".to_string(), "h".to_string()],
        };
        let config = RegressionConfig::default();

        let response = choose_response(&severity, &config, 3);
        match response {
            RegressionResponse::IsolateRootCause {
                candidate_functions,
            } => {
                assert_eq!(candidate_functions.len(), 3);
            }
            other => panic!("expected IsolateRootCause, got {other:?}"),
        }
    }

    #[test]
    fn test_response_cascading_stop() {
        let severity = RegressionSeverity::Cascading {
            count: 20,
            affected_functions: vec!["f".to_string(), "g".to_string(), "h".to_string()],
        };
        let config = RegressionConfig {
            max_regressions_before_stop: 10,
            ..Default::default()
        };

        let response = choose_response(&severity, &config, 3);
        assert!(matches!(response, RegressionResponse::StopLoop { .. }));
    }

    // --- RegressionConfig defaults ---

    #[test]
    fn test_regression_config_defaults() {
        let config = RegressionConfig::default();
        assert_eq!(config.multiple_vc_threshold, 2);
        assert_eq!(config.cascading_function_threshold, 3);
        assert_eq!(config.max_regressions_before_stop, 10);
    }
}
