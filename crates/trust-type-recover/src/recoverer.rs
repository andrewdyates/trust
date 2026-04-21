// trust-type-recover: multi-strategy type recoverer
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::TypeRecoveryError;
use crate::evidence::{EvidenceSource, TypeEvidence};
use crate::return_type::{CalleeReturnTypeStrategy, ReturnTypeStrategy};
use crate::strategy::{
    AccessPatternStrategy, ArrayRecoveryStrategy, DwarfStrategy, PointerRecoveryStrategy,
    RecoveryContext, SignatureMatchStrategy, StructRecoveryStrategy, TypeRecoveryStrategy,
    ValueRangeStrategy,
};
use crate::types::RecoveredType;

/// Combines multiple type recovery strategies and resolves conflicts
/// using confidence-weighted scoring.
pub struct TypeRecoverer {
    strategies: Vec<Box<dyn TypeRecoveryStrategy>>,
}

impl Default for TypeRecoverer {
    fn default() -> Self {
        Self {
            strategies: vec![
                Box::new(DwarfStrategy),
                Box::new(AccessPatternStrategy),
                Box::new(StructRecoveryStrategy),
                Box::new(ArrayRecoveryStrategy),
                Box::new(PointerRecoveryStrategy),
                Box::new(SignatureMatchStrategy),
                Box::new(ReturnTypeStrategy),
                Box::new(CalleeReturnTypeStrategy),
                Box::new(ValueRangeStrategy),
            ],
        }
    }
}

impl TypeRecoverer {
    /// Create a recoverer with the default strategy set (all 9 strategies).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a recoverer with a custom set of strategies.
    #[must_use]
    pub fn with_strategies(strategies: Vec<Box<dyn TypeRecoveryStrategy>>) -> Self {
        Self { strategies }
    }

    /// Run all strategies and return the best-supported recovered type.
    ///
    /// Returns the type with the highest confidence score. If multiple
    /// strategies agree, confidence is boosted. If no evidence is found,
    /// returns [`TypeRecoveryError::NoEvidence`].
    pub fn recover_type(
        &self,
        ctx: &RecoveryContext,
        address: u64,
    ) -> Result<TypeEvidence, TypeRecoveryError> {
        let all_evidence = self.collect_evidence(ctx)?;

        if all_evidence.is_empty() {
            return Err(TypeRecoveryError::NoEvidence(address));
        }

        // Find the highest-confidence evidence, boosting when strategies agree
        let best = select_best_evidence(all_evidence, address)?;
        Ok(best)
    }

    /// Run all strategies and return all collected evidence (unsorted).
    pub fn collect_evidence(
        &self,
        ctx: &RecoveryContext,
    ) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut all_evidence = Vec::new();

        for strategy in &self.strategies {
            match strategy.recover(ctx) {
                Ok(evidence) => all_evidence.extend(evidence),
                Err(TypeRecoveryError::DwarfParse(_)) => {
                    // Non-fatal: DWARF might be partial or stripped
                    continue;
                }
                Err(e) => return Err(e),
            }
        }

        Ok(all_evidence)
    }
}

/// Select the best evidence from a collection, boosting confidence
/// when multiple independent sources agree on the same type.
fn select_best_evidence(
    evidence: Vec<TypeEvidence>,
    address: u64,
) -> Result<TypeEvidence, TypeRecoveryError> {
    if evidence.is_empty() {
        return Err(TypeRecoveryError::NoEvidence(address));
    }

    if evidence.len() == 1 {
        return Ok(evidence.into_iter().next().expect("checked non-empty"));
    }

    // Group evidence by structural type similarity and boost confidence
    // for agreement. Simple approach: pick highest confidence, then check
    // if others agree to boost.
    let best = evidence
        .iter()
        .enumerate()
        .max_by(|(_, a), (_, b)| {
            a.confidence
                .partial_cmp(&b.confidence)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .map(|(i, _)| i)
        .expect("non-empty evidence");

    let best_type = &evidence[best].recovered_type;

    // Count how many other sources agree (same RecoveredType variant)
    let agreement_count = evidence
        .iter()
        .enumerate()
        .filter(|(i, e)| *i != best && types_agree(best_type, &e.recovered_type))
        .count();

    // Boost: each agreeing source adds 0.1, capped at 1.0
    let boost = (agreement_count as f64) * 0.1;
    let boosted_confidence = (evidence[best].confidence + boost).min(1.0);

    // Collect all sources for the combined evidence
    let sources: Vec<EvidenceSource> = evidence.iter().map(|e| e.source.clone()).collect();

    Ok(TypeEvidence {
        recovered_type: evidence.into_iter().nth(best).expect("valid index").recovered_type,
        confidence: boosted_confidence,
        source: EvidenceSource::Combined { sources },
    })
}

/// Check if two recovered types agree on their high-level structure.
///
/// Agreement means: same variant, and for primitives, same underlying type.
/// For structs/arrays, we check element/field count match.
fn types_agree(a: &RecoveredType, b: &RecoveredType) -> bool {
    match (a, b) {
        (RecoveredType::Primitive(ta), RecoveredType::Primitive(tb)) => ta == tb,
        (
            RecoveredType::Pointer {
                mutable: ma,
                pointee: pa,
            },
            RecoveredType::Pointer {
                mutable: mb,
                pointee: pb,
            },
        ) => ma == mb && types_agree(pa, pb),
        (
            RecoveredType::Array {
                element: ea,
                length: la,
            },
            RecoveredType::Array {
                element: eb,
                length: lb,
            },
        ) => la == lb && types_agree(ea, eb),
        (
            RecoveredType::Struct { fields: fa, .. },
            RecoveredType::Struct { fields: fb, .. },
        ) => fa.len() == fb.len(),
        (RecoveredType::Opaque { size: sa }, RecoveredType::Opaque { size: sb }) => sa == sb,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::strategy::{
        AccessObservation, DwarfEntry, DwarfTag, RecoveryContext, ValueRangeObservation,
    };
    use trust_types::Ty;

    #[test]
    fn test_recoverer_default_strategies() {
        let recoverer = TypeRecoverer::new();
        assert_eq!(recoverer.strategies.len(), 9);
    }

    #[test]
    fn test_recoverer_no_evidence_error() {
        let recoverer = TypeRecoverer::new();
        let ctx = RecoveryContext::default();
        let result = recoverer.recover_type(&ctx, 0x1000);
        assert!(matches!(result, Err(TypeRecoveryError::NoEvidence(0x1000))));
    }

    #[test]
    fn test_recoverer_dwarf_only() {
        let recoverer = TypeRecoverer::new();
        let ctx = RecoveryContext {
            dwarf_entries: vec![DwarfEntry {
                die_offset: 0x100,
                tag: DwarfTag::BaseType,
                name: Some("unsigned int".to_string()),
                byte_size: Some(4),
                encoding: Some(0x07), // DW_ATE_unsigned
                type_ref: None,
                members: vec![],
            }],
            ..Default::default()
        };

        let result = recoverer.recover_type(&ctx, 0x1000).expect("should recover");
        assert_eq!(
            result.recovered_type,
            RecoveredType::Primitive(Ty::Int {
                width: 32,
                signed: false
            })
        );
        assert!(result.confidence > 0.9);
    }

    #[test]
    fn test_recoverer_agreement_boosts_confidence() {
        let recoverer = TypeRecoverer::new();
        // Both DWARF and value range agree on u8
        let ctx = RecoveryContext {
            dwarf_entries: vec![DwarfEntry {
                die_offset: 0x100,
                tag: DwarfTag::BaseType,
                name: Some("unsigned char".to_string()),
                byte_size: Some(1),
                encoding: Some(0x08), // DW_ATE_unsigned_char
                type_ref: None,
                members: vec![],
            }],
            value_ranges: vec![ValueRangeObservation {
                address: 0x1000,
                min: 0,
                max: 200,
            }],
            ..Default::default()
        };

        let result = recoverer.recover_type(&ctx, 0x1000).expect("should recover");
        // DWARF confidence (0.95) + agreement boost (0.1) = 1.0 (capped)
        assert!(result.confidence > 0.95);
    }

    #[test]
    fn test_recoverer_collect_evidence() {
        let recoverer = TypeRecoverer::new();
        let ctx = RecoveryContext {
            dwarf_entries: vec![DwarfEntry {
                die_offset: 0x100,
                tag: DwarfTag::BaseType,
                name: Some("int".to_string()),
                byte_size: Some(4),
                encoding: Some(0x05),
                type_ref: None,
                members: vec![],
            }],
            access_observations: vec![
                AccessObservation {
                    instruction_addr: 0x1000,
                    access_offset: 0,
                    access_size: 4,
                },
                AccessObservation {
                    instruction_addr: 0x1004,
                    access_offset: 4,
                    access_size: 4,
                },
                AccessObservation {
                    instruction_addr: 0x1008,
                    access_offset: 8,
                    access_size: 4,
                },
            ],
            value_ranges: vec![ValueRangeObservation {
                address: 0x2000,
                min: -100,
                max: 100,
            }],
            ..Default::default()
        };

        let evidence = recoverer.collect_evidence(&ctx).expect("should collect");
        // At least DWARF (1) + access pattern + value range (1)
        assert!(evidence.len() >= 2);
    }

    #[test]
    fn test_types_agree_primitives() {
        let a = RecoveredType::Primitive(Ty::Int {
            width: 32,
            signed: true,
        });
        let b = RecoveredType::Primitive(Ty::Int {
            width: 32,
            signed: true,
        });
        let c = RecoveredType::Primitive(Ty::Int {
            width: 64,
            signed: true,
        });
        assert!(types_agree(&a, &b));
        assert!(!types_agree(&a, &c));
    }

    #[test]
    fn test_types_agree_different_variants() {
        let a = RecoveredType::Primitive(Ty::Bool);
        let b = RecoveredType::Opaque { size: 1 };
        assert!(!types_agree(&a, &b));
    }
}
