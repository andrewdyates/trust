// trust-strengthen/invariant_feedback.rs: Loop invariant feedback from sunder
//
// tRust #793: Pipeline v2 Phase 4 — accepts loop invariants discovered by
// sunder (via trust-sunder-lib) and converts them into strengthen spec
// candidates that can be fed back into the verification pipeline.
//
// When the MIR router's `dispatch_bmc_with_invariant_hints` path discovers
// loop invariants via sunder, those invariants are passed here to generate
// `#[loop_invariant]` annotation candidates for the strengthen pass.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// A loop invariant hint received from sunder via the MIR router.
///
/// This is a simplified representation that does not depend on sunder-lib
/// types directly, enabling the strengthen crate to process invariant hints
/// without a direct sunder dependency.
#[derive(Debug, Clone)]
pub struct InvariantHint {
    /// The function containing the loop.
    pub function_name: String,
    /// The invariant expression as a string (sunder syntax).
    pub expression: String,
    /// Confidence level from sunder (0.0 = guess, 1.0 = proven).
    pub confidence: f64,
    /// Loop identifier (basic block index or source location).
    pub loop_id: String,
}

/// Convert sunder loop invariants into strengthen spec candidates.
///
/// Each invariant is formatted as a `#[loop_invariant]` annotation string
/// that can be applied to the source code by the backprop pass.
///
/// # Arguments
///
/// * `function_name` - Fully qualified name of the function containing loops.
/// * `invariants` - Loop invariants discovered by sunder.
///
/// # Returns
///
/// A list of annotation strings suitable for source-level insertion.
#[must_use]
pub fn apply_invariant_hints(_function_name: &str, invariants: &[InvariantHint]) -> Vec<String> {
    invariants
        .iter()
        .filter(|inv| inv.confidence > 0.0)
        .map(|inv| {
            format!(
                "#[loop_invariant(loop = \"{}\", confidence = {:.2})] {}",
                inv.loop_id, inv.confidence, inv.expression,
            )
        })
        .collect()
}

/// Convert sunder-lib `LoopInvariant` values into `InvariantHint`s.
///
/// This bridges the trust-sunder-lib result type into the strengthen crate's
/// internal representation without creating a compile-time dependency between
/// the two crates beyond trust-types.
#[must_use]
pub fn from_sunder_invariants(
    invariants: &[trust_sunder_lib::LoopInvariant],
) -> Vec<InvariantHint> {
    invariants
        .iter()
        .map(|inv| InvariantHint {
            function_name: inv.function_name.clone(),
            expression: inv.expression.clone(),
            confidence: inv.confidence,
            loop_id: inv.loop_id.clone(),
        })
        .collect()
}

/// Rank invariant hints by confidence, filtering below a minimum threshold.
///
/// # Arguments
///
/// * `hints` - Unranked invariant hints.
/// * `min_confidence` - Minimum confidence threshold (0.0 to 1.0).
///
/// # Returns
///
/// Filtered and sorted hints (highest confidence first).
#[must_use]
pub fn rank_invariant_hints(hints: &[InvariantHint], min_confidence: f64) -> Vec<InvariantHint> {
    let mut ranked: Vec<InvariantHint> =
        hints.iter().filter(|h| h.confidence >= min_confidence).cloned().collect();
    ranked.sort_by(|a, b| {
        b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
    });
    ranked
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_hints() -> Vec<InvariantHint> {
        vec![
            InvariantHint {
                function_name: "crate::sum_array".to_string(),
                expression: "i < n".to_string(),
                confidence: 0.95,
                loop_id: "bb3".to_string(),
            },
            InvariantHint {
                function_name: "crate::sum_array".to_string(),
                expression: "acc >= 0".to_string(),
                confidence: 0.7,
                loop_id: "bb3".to_string(),
            },
            InvariantHint {
                function_name: "crate::sum_array".to_string(),
                expression: "i >= 0".to_string(),
                confidence: 0.0,
                loop_id: "bb3".to_string(),
            },
        ]
    }

    #[test]
    fn test_apply_invariant_hints_basic() {
        let hints = sample_hints();
        let annotations = apply_invariant_hints("crate::sum_array", &hints);

        // Zero-confidence hint should be filtered out.
        assert_eq!(annotations.len(), 2);
        assert!(annotations[0].contains("i < n"));
        assert!(annotations[0].contains("loop_invariant"));
        assert!(annotations[0].contains("bb3"));
        assert!(annotations[1].contains("acc >= 0"));
    }

    #[test]
    fn test_apply_invariant_hints_empty() {
        let annotations = apply_invariant_hints("crate::f", &[]);
        assert!(annotations.is_empty());
    }

    #[test]
    fn test_rank_invariant_hints_filters_low_confidence() {
        let hints = sample_hints();
        let ranked = rank_invariant_hints(&hints, 0.8);

        assert_eq!(ranked.len(), 1);
        assert_eq!(ranked[0].expression, "i < n");
    }

    #[test]
    fn test_rank_invariant_hints_sorts_by_confidence() {
        let hints = sample_hints();
        let ranked = rank_invariant_hints(&hints, 0.5);

        assert_eq!(ranked.len(), 2);
        assert!(ranked[0].confidence >= ranked[1].confidence);
        assert_eq!(ranked[0].expression, "i < n");
        assert_eq!(ranked[1].expression, "acc >= 0");
    }

    #[test]
    fn test_rank_invariant_hints_zero_threshold() {
        let hints = sample_hints();
        let ranked = rank_invariant_hints(&hints, 0.0);

        // All three hints pass with threshold 0.0 (including the 0.0 confidence one).
        assert_eq!(ranked.len(), 3);
    }

    #[test]
    fn test_from_sunder_invariants() {
        let sunder_invs = vec![trust_sunder_lib::LoopInvariant {
            function_name: "crate::foo".to_string(),
            loop_id: "bb2".to_string(),
            expression: "x > 0".to_string(),
            confidence: 0.9,
            verified: false,
        }];

        let hints = from_sunder_invariants(&sunder_invs);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].function_name, "crate::foo");
        assert_eq!(hints[0].expression, "x > 0");
        assert_eq!(hints[0].loop_id, "bb2");
        assert!((hints[0].confidence - 0.9).abs() < f64::EPSILON);
    }
}
