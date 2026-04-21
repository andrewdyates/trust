// trust-vcgen/rvalue_safety.rs: Safety VCs for Rvalue::Discriminant, Aggregate, Ref, and Len
//
// tRust #438: The forward VC generation pass previously skipped several Rvalue
// variants. This module generates verification conditions for:
//
// - Rvalue::Discriminant(place): Verifies the place holds an enum/ADT type.
//   Reading a discriminant from a non-enum is undefined behavior.
//
// - Rvalue::Aggregate(AggregateKind::Array, operands): Verifies the operand
//   count matches the declared array length when the assignment target has
//   an Array type.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AggregateKind, BasicBlock, Formula, Rvalue, Sort, SourceSpan, Ty,
    VcKind, VerifiableFunction, VerificationCondition,
};

use crate::{operand_ty, place_to_var_name};

/// Check an rvalue for Discriminant and Aggregate safety violations.
///
/// Called from `generate_vcs()` for each `Statement::Assign` in the forward pass.
pub(crate) fn check_rvalue_safety(
    func: &VerifiableFunction,
    _block: &BasicBlock,
    rvalue: &Rvalue,
    place_ty: Option<&Ty>,
    stmt_span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    match rvalue {
        // tRust #438: Discriminant read — place must hold an enum/ADT type.
        Rvalue::Discriminant(place) => {
            let place_name = place_to_var_name(func, place);
            let resolved_ty = func
                .body
                .locals
                .get(place.local)
                .map(|d| &d.ty);

            // If the type is not an ADT (which models enums), the discriminant
            // read is invalid. Generate a VC whose formula is unsatisfiable
            // (Bool(false)) when the type IS an ADT (no violation), or
            // Bool(true) when the type is NOT an ADT (definite violation).
            let is_adt = resolved_ty.is_some_and(|t| matches!(t, Ty::Adt { .. }));
            if !is_adt {
                // The discriminant is read on a type that is not an ADT/enum.
                // Formula: the place's "type tag" != ADT_TAG, which is trivially
                // satisfiable, meaning a solver will confirm the violation.
                let type_tag_var = Formula::Var(
                    format!("{place_name}__type_tag"),
                    Sort::Int,
                );
                // ADT_TAG sentinel: we use -1 as a sentinel for "is an ADT"
                let adt_sentinel = Formula::Int(-1);
                let not_adt = Formula::Not(Box::new(Formula::Eq(
                    Box::new(type_tag_var),
                    Box::new(adt_sentinel),
                )));
                vcs.push(VerificationCondition {
                    kind: VcKind::InvalidDiscriminant { place_name },
                    function: func.name.clone(),
                    location: stmt_span.clone(),
                    formula: not_adt,
                    contract_metadata: None,
                });
            }
        }

        // tRust #438: Array aggregate — operand count must match array length.
        Rvalue::Aggregate(AggregateKind::Array, operands) => {
            if let Some(Ty::Array { len, .. }) = place_ty {
                let expected = *len as usize;
                let actual = operands.len();
                if expected != actual {
                    // Formula: expected_len != actual_len (trivially SAT = definite violation)
                    let expected_f = Formula::Int(expected as i128);
                    let actual_f = Formula::Int(actual as i128);
                    let mismatch = Formula::Not(Box::new(Formula::Eq(
                        Box::new(expected_f),
                        Box::new(actual_f),
                    )));
                    vcs.push(VerificationCondition {
                        kind: VcKind::AggregateArrayLengthMismatch { expected, actual },
                        function: func.name.clone(),
                        location: stmt_span.clone(),
                        formula: mismatch,
                        contract_metadata: None,
                    });
                }
            }
        }

        _ => {}
    }
}

/// Resolve the type of a Place from the function's local declarations.
///
/// Used to get the destination type for aggregate assignments.
pub(crate) fn place_ty(func: &VerifiableFunction, place: &trust_types::Place) -> Option<Ty> {
    // Delegate to the same logic as operand_ty but for a raw Place.
    let op = trust_types::Operand::Copy(place.clone());
    operand_ty(func, &op)
}

#[cfg(all(test, not(feature = "pipeline-v2")))]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, VerifiableBody, VerifiableFunction,
    };

    /// Helper: build a function with a Discriminant rvalue on a non-ADT local.
    fn discriminant_on_non_enum() -> VerifiableFunction {
        VerifiableFunction {
            name: "disc_non_enum".to_string(),
            def_path: "test::disc_non_enum".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },       // return
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) }, // not an enum
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) }, // discriminant dest
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a function with a Discriminant rvalue on an ADT local.
    fn discriminant_on_enum() -> VerifiableFunction {
        VerifiableFunction {
            name: "disc_enum".to_string(),
            def_path: "test::disc_enum".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Adt {
                            name: "MyEnum".into(),
                            fields: vec![("discriminant".into(), Ty::u32())],
                        },
                        name: Some("e".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_discriminant_on_non_enum_generates_vc() {
        let func = discriminant_on_non_enum();
        let vcs = crate::generate_vcs(&func);
        let disc_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::InvalidDiscriminant { .. }))
            .collect();
        assert_eq!(
            disc_vcs.len(), 1,
            "Discriminant on non-enum should produce exactly 1 InvalidDiscriminant VC"
        );
        if let VcKind::InvalidDiscriminant { place_name } = &disc_vcs[0].kind {
            assert_eq!(place_name, "x", "VC should reference the place name");
        }
    }

    #[test]
    fn test_discriminant_on_enum_no_vc() {
        let func = discriminant_on_enum();
        let vcs = crate::generate_vcs(&func);
        let disc_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::InvalidDiscriminant { .. }))
            .collect();
        assert!(
            disc_vcs.is_empty(),
            "Discriminant on ADT should not produce InvalidDiscriminant VC"
        );
    }

    /// Helper: build a function with an Array aggregate where operand count
    /// mismatches the declared array length.
    fn array_aggregate_mismatch() -> VerifiableFunction {
        VerifiableFunction {
            name: "arr_mismatch".to_string(),
            def_path: "test::arr_mismatch".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    // _0: return type
                    LocalDecl {
                        index: 0,
                        ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 },
                        name: None,
                    },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        // Only 2 operands for a [u32; 3] array — mismatch!
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Array,
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a function with a matching Array aggregate.
    fn array_aggregate_matching() -> VerifiableFunction {
        VerifiableFunction {
            name: "arr_match".to_string(),
            def_path: "test::arr_match".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Array { elem: Box::new(Ty::u32()), len: 2 },
                        name: None,
                    },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Array,
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Array { elem: Box::new(Ty::u32()), len: 2 },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_array_aggregate_mismatch_generates_vc() {
        let func = array_aggregate_mismatch();
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert_eq!(
            arr_vcs.len(), 1,
            "Array aggregate with mismatched length should produce 1 VC"
        );
        if let VcKind::AggregateArrayLengthMismatch { expected, actual } = &arr_vcs[0].kind {
            assert_eq!(*expected, 3);
            assert_eq!(*actual, 2);
        }
    }

    #[test]
    fn test_array_aggregate_matching_no_vc() {
        let func = array_aggregate_matching();
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert!(
            arr_vcs.is_empty(),
            "Array aggregate with matching length should not produce VC"
        );
    }

    #[test]
    fn test_discriminant_vc_is_l0_safety() {
        let func = discriminant_on_non_enum();
        let vcs = crate::generate_vcs(&func);
        let disc_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::InvalidDiscriminant { .. }))
            .collect();
        assert_eq!(disc_vcs.len(), 1);
        assert_eq!(
            disc_vcs[0].kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "InvalidDiscriminant should be L0 safety"
        );
    }

    #[test]
    fn test_aggregate_mismatch_vc_is_l0_safety() {
        let func = array_aggregate_mismatch();
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert_eq!(arr_vcs.len(), 1);
        assert_eq!(
            arr_vcs[0].kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "AggregateArrayLengthMismatch should be L0 safety"
        );
    }

    #[test]
    fn test_tuple_aggregate_no_vc() {
        // Tuple aggregates should not produce array-length VCs
        let func = VerifiableFunction {
            name: "tuple_agg".to_string(),
            def_path: "test::tuple_agg".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: None,
                    },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Bool(true)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let vcs = crate::generate_vcs(&func);
        let arr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::AggregateArrayLengthMismatch { .. }))
            .collect();
        assert!(
            arr_vcs.is_empty(),
            "Tuple aggregate should not produce array-length VC"
        );
    }
}
