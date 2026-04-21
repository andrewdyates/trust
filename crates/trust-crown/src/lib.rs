#![allow(dead_code)]
//! trust-crown: Neural network verification via gamma-crown
//!
//! Integrates the gamma-crown verification tool as a VerificationBackend for
//! the trust-router dispatch system. Handles NeuralRobustness, NeuralOutputRange,
//! NeuralLipschitz, and NeuralMonotonicity VcKinds.
//!
//! The gamma-crown binary is detected at runtime. When absent, the backend
//! returns Unknown results so the router can fall through to other backends.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod error;
pub mod types;

use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;
use std::time::Instant;

use trust_router::{BackendRole, VerificationBackend};
use trust_types::*;

use crate::error::CrownError;
use crate::types::{
    CrownResult, CrownStatus, NetworkDescription, NeuralNetProperty, PerturbationNorm,
    VerificationQuery,
};

/// Cached result of gamma-crown binary detection.
static GAMMA_CROWN_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();

/// Detect whether the gamma-crown binary is available on PATH.
fn detect_gamma_crown() -> Option<PathBuf> {
    // Try common binary names in order of preference.
    for name in &["gamma-crown", "gamma_crown"] {
        if let Ok(output) = Command::new("which").arg(name).output()
            && output.status.success() {
                let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
                if !path.is_empty() {
                    return Some(PathBuf::from(path));
                }
            }
    }
    None
}

/// Check if gamma-crown is available (cached).
pub(crate) fn is_gamma_crown_available() -> bool {
    GAMMA_CROWN_PATH
        .get_or_init(detect_gamma_crown)
        .is_some()
}

/// Neural network verification backend using gamma-crown.
///
/// Dispatches verification queries to the gamma-crown subprocess and maps
/// results back to the trust-types `VerificationResult` enum. Falls back
/// to `Unknown` when gamma-crown is not installed.
pub(crate) struct GammaCrownBackend {
    /// Override path for the gamma-crown binary (None = auto-detect).
    binary_path: Option<PathBuf>,
    /// Default timeout in milliseconds for verification queries.
    default_timeout_ms: u64,
}

impl GammaCrownBackend {
    /// Create a new backend with auto-detected gamma-crown binary.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            binary_path: None,
            default_timeout_ms: 60_000,
        }
    }

    /// Create a backend with an explicit binary path.
    #[must_use]
    pub(crate) fn with_binary(path: PathBuf) -> Self {
        Self {
            binary_path: Some(path),
            default_timeout_ms: 60_000,
        }
    }

    /// Set the default timeout for verification queries.
    #[must_use]
    pub(crate) fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.default_timeout_ms = timeout_ms;
        self
    }

    /// Get the path to the gamma-crown binary, if available.
    fn binary_path(&self) -> Option<&PathBuf> {
        if let Some(ref path) = self.binary_path {
            return Some(path);
        }
        GAMMA_CROWN_PATH.get_or_init(detect_gamma_crown).as_ref()
    }

    /// Convert a VcKind into a NeuralNetProperty for gamma-crown dispatch.
    ///
    /// Returns None for non-neural VcKinds.
    pub(crate) fn vc_to_property(kind: &VcKind) -> Option<NeuralNetProperty> {
        match kind {
            VcKind::NeuralRobustness { epsilon } => {
                let eps: f64 = epsilon.parse().unwrap_or(0.0);
                Some(NeuralNetProperty::Robustness {
                    epsilon: eps,
                    norm: PerturbationNorm::LInf,
                    reference_input: Vec::new(),
                    expected_class: 0,
                })
            }
            VcKind::NeuralOutputRange { lower, upper } => {
                let lo: f64 = lower.parse().unwrap_or(0.0);
                let hi: f64 = upper.parse().unwrap_or(0.0);
                Some(NeuralNetProperty::OutputRange {
                    lower_bounds: vec![lo],
                    upper_bounds: vec![hi],
                    input_lower: Vec::new(),
                    input_upper: Vec::new(),
                })
            }
            VcKind::NeuralLipschitz { constant } => {
                let c: f64 = constant.parse().unwrap_or(0.0);
                Some(NeuralNetProperty::Lipschitz {
                    constant: c,
                    norm: PerturbationNorm::LInf,
                    input_lower: Vec::new(),
                    input_upper: Vec::new(),
                })
            }
            VcKind::NeuralMonotonicity { input_dim } => Some(NeuralNetProperty::Monotonicity {
                input_dim: *input_dim,
                output_dim: 0,
                input_lower: Vec::new(),
                input_upper: Vec::new(),
            }),
            _ => None,
        }
    }

    /// Execute a verification query against the gamma-crown subprocess.
    ///
    /// Serializes the query to JSON, invokes the binary, and parses the result.
    pub(crate) fn execute_query(&self, query: &VerificationQuery) -> Result<CrownResult, CrownError> {
        let binary = self
            .binary_path()
            .ok_or_else(|| CrownError::BinaryNotFound {
                message: "gamma-crown not found on PATH; install from andrewdyates/gamma-crown".to_string(),
            })?;

        let query_json = serde_json::to_string(query)?;

        let output = Command::new(binary)
            .arg("--verify")
            .arg("--json")
            .arg("--timeout")
            .arg(query.timeout_ms.to_string())
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                use std::io::Write;
                if let Some(ref mut stdin) = child.stdin {
                    stdin.write_all(query_json.as_bytes())?;
                }
                child.wait_with_output()
            })?;

        if !output.status.success() {
            return Err(CrownError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            });
        }

        let result: CrownResult = serde_json::from_slice(&output.stdout).map_err(|_| {
            CrownError::OutputParse {
                message: format!(
                    "invalid JSON output: {}",
                    String::from_utf8_lossy(&output.stdout)
                ),
            }
        })?;

        Ok(result)
    }

    /// Map a CrownResult to a trust-types VerificationResult.
    pub(crate) fn map_result(crown_result: &CrownResult) -> VerificationResult {
        match &crown_result.status {
            CrownStatus::Verified => VerificationResult::Proved {
                solver: "gamma-crown".to_string(),
                time_ms: crown_result.time_ms,
                strength: ProofStrength {
                    reasoning: ReasoningKind::NeuralBounding,
                    assurance: AssuranceLevel::Sound,
                },
                proof_certificate: None,
                solver_warnings: None,
            },
            CrownStatus::Violated {
                counterexample_input,
                counterexample_output,
            } => {
                let cex = Counterexample {
                    assignments: counterexample_input
                        .iter()
                        .enumerate()
                        .map(|(i, v)| {
                            (format!("input_{i}"), CounterexampleValue::Float(*v))
                        })
                        .chain(counterexample_output.iter().enumerate().map(|(i, v)| {
                            (format!("output_{i}"), CounterexampleValue::Float(*v))
                        }))
                        .collect(),
                    trace: None,
                };
                VerificationResult::Failed {
                    solver: "gamma-crown".to_string(),
                    time_ms: crown_result.time_ms,
                    counterexample: Some(cex),
                }
            }
            CrownStatus::Unknown { reason } => VerificationResult::Unknown {
                solver: "gamma-crown".to_string(),
                time_ms: crown_result.time_ms,
                reason: reason.clone(),
            },
            CrownStatus::Timeout { elapsed_ms } => VerificationResult::Timeout {
                solver: "gamma-crown".to_string(),
                timeout_ms: *elapsed_ms,
            },
        }
    }
}

impl Default for GammaCrownBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for GammaCrownBackend {
    fn name(&self) -> &str {
        "gamma-crown"
    }

    fn role(&self) -> BackendRole {
        BackendRole::Neural
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        Self::vc_to_property(&vc.kind).is_some()
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = Instant::now();

        // Convert VC to neural property. If it's not a neural VC, return Unknown.
        let property = match Self::vc_to_property(&vc.kind) {
            Some(p) => p,
            None => {
                return VerificationResult::Unknown {
                    solver: "gamma-crown".to_string(),
                    time_ms: 0,
                    reason: format!(
                        "gamma-crown cannot handle non-neural VcKind: {}",
                        vc.kind.description()
                    ),
                };
            }
        };

        // If gamma-crown binary is not available, return Unknown so the router
        // can fall through to another backend.
        if self.binary_path().is_none() {
            return VerificationResult::Unknown {
                solver: "gamma-crown".to_string(),
                time_ms: start.elapsed().as_millis() as u64,
                reason: "gamma-crown binary not available".to_string(),
            };
        }

        // Build a query with a placeholder network (real usage would extract
        // the network from the VC's metadata or a model registry).
        let query = VerificationQuery {
            network: NetworkDescription {
                name: vc.function.clone(),
                model_path: String::new(),
                layers: Vec::new(),
                input_dim: 0,
                output_dim: 0,
            },
            property,
            timeout_ms: self.default_timeout_ms,
        };

        match self.execute_query(&query) {
            Ok(result) => Self::map_result(&result),
            Err(e) => VerificationResult::Unknown {
                solver: "gamma-crown".to_string(),
                time_ms: start.elapsed().as_millis() as u64,
                reason: format!("gamma-crown error: {e}"),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backend_name_and_role() {
        let backend = GammaCrownBackend::new();
        assert_eq!(backend.name(), "gamma-crown");
        assert_eq!(backend.role(), BackendRole::Neural);
    }

    #[test]
    fn test_can_handle_neural_robustness() {
        let backend = GammaCrownBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::NeuralRobustness { epsilon: "0.01".to_string() },
            function: "classify".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&vc));
    }

    #[test]
    fn test_can_handle_neural_output_range() {
        let backend = GammaCrownBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::NeuralOutputRange {
                lower: "-1.0".to_string(),
                upper: "1.0".to_string(),
            },
            function: "predict".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&vc));
    }

    #[test]
    fn test_can_handle_neural_lipschitz() {
        let backend = GammaCrownBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::NeuralLipschitz { constant: "1.5".to_string() },
            function: "transform".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&vc));
    }

    #[test]
    fn test_can_handle_neural_monotonicity() {
        let backend = GammaCrownBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::NeuralMonotonicity { input_dim: 0 },
            function: "score".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&vc));
    }

    #[test]
    fn test_cannot_handle_non_neural_vc() {
        let backend = GammaCrownBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "div_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(!backend.can_handle(&vc));
    }

    #[test]
    fn test_verify_returns_unknown_when_binary_absent() {
        // Without gamma-crown installed, verify should return Unknown.
        let backend = GammaCrownBackend::with_binary(PathBuf::from("/nonexistent/gamma-crown"));
        let vc = VerificationCondition {
            kind: VcKind::NeuralRobustness { epsilon: "0.01".to_string() },
            function: "classify".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = backend.verify(&vc);
        // Should fail to execute the binary and return Unknown.
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "gamma-crown");
    }

    #[test]
    fn test_verify_non_neural_vc_returns_unknown() {
        let backend = GammaCrownBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "div_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_map_result_verified() {
        let crown_result = CrownResult {
            status: CrownStatus::Verified,
            time_ms: 42,
            output_lower_bounds: Some(vec![0.1, 0.9]),
            output_upper_bounds: Some(vec![0.2, 1.0]),
        };
        let vr = GammaCrownBackend::map_result(&crown_result);
        assert!(vr.is_proved());
        assert_eq!(vr.solver_name(), "gamma-crown");
        assert_eq!(vr.time_ms(), 42);
    }

    #[test]
    fn test_map_result_violated() {
        let crown_result = CrownResult {
            status: CrownStatus::Violated {
                counterexample_input: vec![0.5, 0.3],
                counterexample_output: vec![0.1, 0.9],
            },
            time_ms: 100,
            output_lower_bounds: None,
            output_upper_bounds: None,
        };
        let vr = GammaCrownBackend::map_result(&crown_result);
        assert!(vr.is_failed());
        assert_eq!(vr.solver_name(), "gamma-crown");
        if let VerificationResult::Failed {
            counterexample: Some(cex),
            ..
        } = &vr
        {
            // 2 input + 2 output assignments
            assert_eq!(cex.assignments.len(), 4);
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_map_result_unknown() {
        let crown_result = CrownResult {
            status: CrownStatus::Unknown {
                reason: "bounds too loose".to_string(),
            },
            time_ms: 500,
            output_lower_bounds: None,
            output_upper_bounds: None,
        };
        let vr = GammaCrownBackend::map_result(&crown_result);
        assert!(matches!(vr, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_map_result_timeout() {
        let crown_result = CrownResult {
            status: CrownStatus::Timeout { elapsed_ms: 60_000 },
            time_ms: 60_000,
            output_lower_bounds: None,
            output_upper_bounds: None,
        };
        let vr = GammaCrownBackend::map_result(&crown_result);
        assert!(matches!(vr, VerificationResult::Timeout { .. }));
        assert_eq!(vr.time_ms(), 60_000);
    }

    #[test]
    fn test_vc_to_property_robustness() {
        let kind = VcKind::NeuralRobustness { epsilon: "0.05".to_string() };
        let prop = GammaCrownBackend::vc_to_property(&kind);
        assert!(prop.is_some());
        if let Some(NeuralNetProperty::Robustness { epsilon, norm, .. }) = prop {
            assert!((epsilon - 0.05).abs() < f64::EPSILON);
            assert_eq!(norm, PerturbationNorm::LInf);
        } else {
            panic!("expected Robustness property");
        }
    }

    #[test]
    fn test_vc_to_property_output_range() {
        let kind = VcKind::NeuralOutputRange {
            lower: "-2.0".to_string(),
            upper: "2.0".to_string(),
        };
        let prop = GammaCrownBackend::vc_to_property(&kind);
        assert!(prop.is_some());
        if let Some(NeuralNetProperty::OutputRange {
            lower_bounds,
            upper_bounds,
            ..
        }) = prop
        {
            assert_eq!(lower_bounds, vec![-2.0]);
            assert_eq!(upper_bounds, vec![2.0]);
        } else {
            panic!("expected OutputRange property");
        }
    }

    #[test]
    fn test_vc_to_property_lipschitz() {
        let kind = VcKind::NeuralLipschitz { constant: "3.125".to_string() };
        let prop = GammaCrownBackend::vc_to_property(&kind);
        assert!(prop.is_some());
        if let Some(NeuralNetProperty::Lipschitz { constant, .. }) = prop {
            assert!((constant - 3.125).abs() < f64::EPSILON);
        } else {
            panic!("expected Lipschitz property");
        }
    }

    #[test]
    fn test_vc_to_property_monotonicity() {
        let kind = VcKind::NeuralMonotonicity { input_dim: 5 };
        let prop = GammaCrownBackend::vc_to_property(&kind);
        assert!(prop.is_some());
        if let Some(NeuralNetProperty::Monotonicity { input_dim, .. }) = prop {
            assert_eq!(input_dim, 5);
        } else {
            panic!("expected Monotonicity property");
        }
    }

    #[test]
    fn test_vc_to_property_non_neural_returns_none() {
        let kind = VcKind::DivisionByZero;
        assert!(GammaCrownBackend::vc_to_property(&kind).is_none());

        let kind = VcKind::Postcondition;
        assert!(GammaCrownBackend::vc_to_property(&kind).is_none());
    }

    #[test]
    fn test_default_timeout() {
        let backend = GammaCrownBackend::new();
        assert_eq!(backend.default_timeout_ms, 60_000);
    }

    #[test]
    fn test_with_timeout_builder() {
        let backend = GammaCrownBackend::new().with_timeout(30_000);
        assert_eq!(backend.default_timeout_ms, 30_000);
    }

    #[test]
    fn test_query_serialization_roundtrip() {
        use crate::types::{Activation, NetworkLayer};

        let query = VerificationQuery {
            network: NetworkDescription {
                name: "test_net".to_string(),
                model_path: "/tmp/model.onnx".to_string(),
                layers: vec![
                    NetworkLayer {
                        input_dim: 784,
                        output_dim: 128,
                        activation: Activation::ReLU,
                    },
                    NetworkLayer {
                        input_dim: 128,
                        output_dim: 10,
                        activation: Activation::Softmax,
                    },
                ],
                input_dim: 784,
                output_dim: 10,
            },
            property: NeuralNetProperty::Robustness {
                epsilon: 0.03,
                norm: PerturbationNorm::LInf,
                reference_input: vec![0.0; 784],
                expected_class: 7,
            },
            timeout_ms: 30_000,
        };

        let json = serde_json::to_string(&query).expect("serialization should succeed");
        let deserialized: VerificationQuery =
            serde_json::from_str(&json).expect("deserialization should succeed");
        assert_eq!(query, deserialized);
    }

    #[test]
    fn test_crown_result_serialization_roundtrip() {
        let result = CrownResult {
            status: CrownStatus::Violated {
                counterexample_input: vec![0.1, 0.2, 0.3],
                counterexample_output: vec![0.8, 0.2],
            },
            time_ms: 150,
            output_lower_bounds: Some(vec![-0.5, 0.1]),
            output_upper_bounds: Some(vec![1.0, 0.9]),
        };

        let json = serde_json::to_string(&result).expect("serialization should succeed");
        let deserialized: CrownResult =
            serde_json::from_str(&json).expect("deserialization should succeed");
        assert_eq!(result, deserialized);
    }

    #[test]
    fn test_router_integration_backend_dispatch() {
        // Verify that GammaCrownBackend integrates with the Router correctly.
        use trust_router::Router;

        let router = Router::with_backends(vec![
            Box::new(GammaCrownBackend::new()),
            Box::new(trust_router::mock_backend::MockBackend),
        ]);

        // Neural VC should be handled by gamma-crown (though it returns Unknown
        // since the binary isn't installed in test environments).
        let neural_vc = VerificationCondition {
            kind: VcKind::NeuralRobustness { epsilon: "0.01".to_string() },
            function: "classify".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let plan = router.backend_plan(&neural_vc);
        assert!(!plan.is_empty());
        // gamma-crown should be first since it can handle neural VCs.
        let first = &plan[0];
        assert_eq!(first.name, "gamma-crown");
        assert!(first.can_handle);
        assert_eq!(first.role, BackendRole::Neural);

        // Non-neural VC should fall through to mock.
        let safety_vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "div_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let plan = router.backend_plan(&safety_vc);
        let first_handler = plan.iter().find(|e| e.can_handle);
        assert!(first_handler.is_some());
        assert_eq!(first_handler.unwrap().name, "mock");
    }
}
