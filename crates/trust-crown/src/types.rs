// trust-crown/types.rs: Neural network verification domain types
//
// Defines the property specifications, network descriptions, and query
// structures that the GammaCrownBackend operates on.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// Activation function type for a neural network layer.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum Activation {
    ReLU,
    Sigmoid,
    Tanh,
    Linear,
    Softmax,
    GeLU,
}

/// A single layer in a feedforward neural network.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct NetworkLayer {
    pub input_dim: usize,
    pub output_dim: usize,
    pub activation: Activation,
}

/// Description of a neural network architecture for verification.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct NetworkDescription {
    /// Human-readable name or identifier.
    pub name: String,
    /// Path to the model file (e.g., .onnx or .safetensors).
    pub model_path: String,
    /// Layer descriptions (in order from input to output).
    pub layers: Vec<NetworkLayer>,
    /// Total number of input dimensions.
    pub input_dim: usize,
    /// Total number of output dimensions.
    pub output_dim: usize,
}

/// Norm type for perturbation bounds.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum PerturbationNorm {
    /// L-infinity norm (max absolute deviation per dimension).
    LInf,
    /// L2 norm (Euclidean distance).
    L2,
    /// L1 norm (sum of absolute deviations).
    L1,
}

/// Properties that can be verified about a neural network.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum NeuralNetProperty {
    /// Local robustness: for all inputs within epsilon-ball of a reference
    /// input, the network produces the same classification.
    Robustness {
        /// Perturbation budget (epsilon).
        epsilon: f64,
        /// Norm type for the perturbation ball.
        norm: PerturbationNorm,
        /// Reference input point (flattened).
        reference_input: Vec<f64>,
        /// Expected output class index.
        expected_class: usize,
    },

    /// Output range: for all inputs in a region, the output stays within
    /// specified bounds.
    OutputRange {
        /// Per-dimension lower bounds on the output.
        lower_bounds: Vec<f64>,
        /// Per-dimension upper bounds on the output.
        upper_bounds: Vec<f64>,
        /// Input region lower bounds.
        input_lower: Vec<f64>,
        /// Input region upper bounds.
        input_upper: Vec<f64>,
    },

    /// Monotonicity: increasing the specified input dimension never decreases
    /// the specified output dimension.
    Monotonicity {
        /// Input dimension that is increasing.
        input_dim: usize,
        /// Output dimension that should not decrease.
        output_dim: usize,
        /// Input region lower bounds.
        input_lower: Vec<f64>,
        /// Input region upper bounds.
        input_upper: Vec<f64>,
    },

    /// Lipschitz continuity: the network's output change is bounded by a
    /// constant times the input change.
    Lipschitz {
        /// Maximum allowed Lipschitz constant.
        constant: f64,
        /// Norm used for measuring input/output distances.
        norm: PerturbationNorm,
        /// Input region lower bounds.
        input_lower: Vec<f64>,
        /// Input region upper bounds.
        input_upper: Vec<f64>,
    },

    /// Individual fairness: for two inputs differing only in protected
    /// attributes, the outputs should be similar.
    Fairness {
        /// Indices of protected attribute dimensions.
        protected_dims: Vec<usize>,
        /// Maximum allowed output difference.
        max_output_diff: f64,
        /// Input region lower bounds.
        input_lower: Vec<f64>,
        /// Input region upper bounds.
        input_upper: Vec<f64>,
    },

    /// Reachability: whether a specific output region is reachable from a
    /// given input region.
    Reachability {
        /// Input region lower bounds.
        input_lower: Vec<f64>,
        /// Input region upper bounds.
        input_upper: Vec<f64>,
        /// Target output region lower bounds.
        target_lower: Vec<f64>,
        /// Target output region upper bounds.
        target_upper: Vec<f64>,
    },
}

/// A complete verification query for the gamma-crown backend.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct VerificationQuery {
    /// The neural network to verify.
    pub network: NetworkDescription,
    /// The property to check.
    pub property: NeuralNetProperty,
    /// Timeout in milliseconds (0 = no timeout).
    pub timeout_ms: u64,
}

/// Result status from gamma-crown verification.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum CrownStatus {
    /// Property verified (all bounds hold).
    Verified,
    /// Property violated with a concrete counterexample.
    Violated {
        /// Counterexample input that violates the property.
        counterexample_input: Vec<f64>,
        /// Network output at the counterexample.
        counterexample_output: Vec<f64>,
    },
    /// Verification was inconclusive (bounds too loose).
    Unknown { reason: String },
    /// Verification timed out.
    Timeout { elapsed_ms: u64 },
}

/// Full result from a gamma-crown verification run.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct CrownResult {
    /// Verification status.
    pub status: CrownStatus,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
    /// Lower bounds computed on the output (if available).
    pub output_lower_bounds: Option<Vec<f64>>,
    /// Upper bounds computed on the output (if available).
    pub output_upper_bounds: Option<Vec<f64>>,
}
