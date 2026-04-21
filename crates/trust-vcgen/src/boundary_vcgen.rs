// trust-vcgen/boundary_vcgen.rs: VC generation at trust boundaries
//
// Generates precondition VCs when data enters a trusted zone from an
// untrusted source, and postcondition VCs when data leaves a trusted
// zone for an external consumer.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

fn signed_max_formula(width: u32) -> Formula {
    let (_, max) = signed_bounds(width);
    Formula::Int(max)
}

fn signed_min_formula(width: u32) -> Formula {
    let (min, _) = signed_bounds(width);
    Formula::Int(min)
}

fn unsigned_max_formula(width: u32) -> Formula {
    if width >= 128 {
        Formula::UInt(u128::MAX)
    } else {
        Formula::Int(((1u128 << width) - 1) as i128)
    }
}

/// Generate verification conditions for trust boundary crossings.
///
/// For each boundary in the analysis that matches the given function:
/// - Untrusted -> Trusted: generate Precondition VCs for each argument
///   (the function must validate its inputs).
/// - Trusted -> External/FFI: generate Postcondition VCs for the return value
///   (the function must guarantee its outputs are well-formed).
/// - FFI boundaries: generate additional safety VCs for pointer validity.
#[must_use]
pub fn generate_boundary_vcs(
    analysis: &BoundaryAnalysis,
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for boundary in &analysis.boundaries {
        if boundary.function_path != func.def_path {
            continue;
        }

        if boundary.needs_precondition() {
            generate_precondition_vcs(func, boundary, &mut vcs);
        }

        if boundary.needs_postcondition() {
            generate_postcondition_vcs(func, boundary, &mut vcs);
        }

        if boundary.is_ffi() {
            generate_ffi_safety_vcs(func, boundary, &mut vcs);
        }
    }

    vcs
}

/// Generate precondition VCs for function arguments at a trust boundary.
///
/// At an Untrusted -> Trusted boundary, each argument must be validated.
/// We generate a VC asserting that each integer argument is within its
/// type bounds (a basic well-formedness condition).
fn generate_precondition_vcs(
    func: &VerifiableFunction,
    boundary: &TrustBoundary,
    vcs: &mut Vec<VerificationCondition>,
) {
    // Arguments are locals 1..=arg_count (local 0 is the return place).
    for i in 1..=func.body.arg_count {
        let Some(local) = func.body.locals.get(i) else {
            continue;
        };

        let formula = match &local.ty {
            Ty::Int { width, signed: true } => {
                let var_name =
                    local.name.clone().unwrap_or_else(|| format!("_{i}"));
                let var = Formula::Var(var_name, Sort::Int);
                // arg >= min && arg <= max
                Formula::And(vec![
                    Formula::Ge(Box::new(var.clone()), Box::new(signed_min_formula(*width))),
                    Formula::Le(Box::new(var), Box::new(signed_max_formula(*width))),
                ])
            }
            Ty::Int { width, signed: false } => {
                let var_name =
                    local.name.clone().unwrap_or_else(|| format!("_{i}"));
                let var = Formula::Var(var_name, Sort::Int);
                // arg >= 0 && arg <= max
                Formula::And(vec![
                    Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0))),
                    Formula::Le(Box::new(var), Box::new(unsigned_max_formula(*width))),
                ])
            }
            _ => continue,
        };

        vcs.push(VerificationCondition {
            kind: VcKind::Precondition {
                callee: format!(
                    "boundary<{}>::{}",
                    boundary.kind.label(),
                    func.name
                ),
            },
            function: func.name.clone(),
            location: boundary.location.clone(),
            formula,
            contract_metadata: None,
        });
    }
}

/// Generate postcondition VCs for the return value at a trust boundary.
///
/// At a Trusted -> External boundary, the return value must satisfy
/// output guarantees. We generate a VC asserting the return value is
/// within type bounds.
fn generate_postcondition_vcs(
    func: &VerifiableFunction,
    boundary: &TrustBoundary,
    vcs: &mut Vec<VerificationCondition>,
) {
    let return_ty = &func.body.return_ty;

    let formula = match return_ty {
        Ty::Int { width, signed: true } => {
            let var = Formula::Var("_0".to_string(), Sort::Int);
            Formula::And(vec![
                Formula::Ge(Box::new(var.clone()), Box::new(signed_min_formula(*width))),
                Formula::Le(Box::new(var), Box::new(signed_max_formula(*width))),
            ])
        }
        Ty::Int { width, signed: false } => {
            let var = Formula::Var("_0".to_string(), Sort::Int);
            Formula::And(vec![
                Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0))),
                Formula::Le(Box::new(var), Box::new(unsigned_max_formula(*width))),
            ])
        }
        _ => return,
    };

    vcs.push(VerificationCondition {
        kind: VcKind::Postcondition,
        function: func.name.clone(),
        location: boundary.location.clone(),
        formula,
        contract_metadata: None,
    });
}

/// Generate FFI-specific safety VCs.
///
/// At FFI boundaries, we generate an assertion VC noting that FFI data
/// must be validated before use in trusted code.
fn generate_ffi_safety_vcs(
    func: &VerifiableFunction,
    boundary: &TrustBoundary,
    vcs: &mut Vec<VerificationCondition>,
) {
    // For each argument at an FFI boundary, assert a basic safety condition.
    for i in 1..=func.body.arg_count {
        let Some(local) = func.body.locals.get(i) else {
            continue;
        };

        // Only generate FFI safety VCs for reference/pointer types.
        // tRust #432: Include RawPtr locals as well.
        if !local.ty.is_pointer_like() {
            continue;
        }

        let var_name = local.name.clone().unwrap_or_else(|| format!("_{i}"));
        // FFI pointer validity: assert the reference is not null-equivalent.
        // In the SMT encoding, we model this as the variable being "valid" (non-zero).
        let formula = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var(var_name, Sort::Int)),
            Box::new(Formula::Int(0)),
        )));

        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "FFI argument _{} must be valid at {} boundary",
                    i,
                    boundary.kind.label()
                ),
            },
            function: func.name.clone(),
            location: boundary.location.clone(),
            formula,
            contract_metadata: None,
        });
    }
}

/// Compute signed integer bounds for the given bit width.
fn signed_bounds(width: u32) -> (i128, i128) {
    if width >= 128 {
        (i128::MIN, i128::MAX)
    } else {
        let min = -(1i128 << (width - 1));
        let max = (1i128 << (width - 1)) - 1;
        (min, max)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "boundary_test.rs".into(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 40,
        }
    }

    /// A public function: `pub fn process(x: u32, y: i32) -> u32`
    fn public_api_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "process".to_string(),
            def_path: "crate::process".to_string(),
            span: span(10),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// An FFI function: `extern "C" fn ffi_callback(data: &u8) -> i32`
    fn ffi_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "ffi_callback".to_string(),
            def_path: "crate::ffi_callback".to_string(),
            span: span(20),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) },
                        name: Some("data".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_precondition_vcs_at_public_api() {
        let func = public_api_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: span(10),
            function_path: "crate::process".into(),
            kind: BoundaryKind::PublicApi,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);

        // Two arguments => two precondition VCs
        let precond_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::Precondition { .. }))
            .collect();
        assert_eq!(precond_vcs.len(), 2, "should generate precondition VC per integer arg");

        // Check the first VC is for u32 bounds
        assert!(
            matches!(&precond_vcs[0].kind, VcKind::Precondition { callee }
                if callee.contains("public API") && callee.contains("process"))
        );
    }

    #[test]
    fn test_postcondition_vcs_at_outward_boundary() {
        let func = public_api_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Trusted,
            to_zone: TrustZone::External,
            location: span(10),
            function_path: "crate::process".into(),
            kind: BoundaryKind::ModuleBoundary,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);

        let postcond_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
            .collect();
        assert_eq!(postcond_vcs.len(), 1, "should generate postcondition VC for return type");
    }

    #[test]
    fn test_ffi_boundary_generates_safety_vcs() {
        let func = ffi_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Ffi,
            to_zone: TrustZone::Trusted,
            location: span(20),
            function_path: "crate::ffi_callback".into(),
            kind: BoundaryKind::FfiCall,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);

        // FFI boundary: 1 precondition for the ref arg (but ref is not integer, so
        // no integer precondition) + 1 FFI safety assertion for the ref arg
        let assertion_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("FFI")))
            .collect();
        assert_eq!(assertion_vcs.len(), 1, "should generate FFI safety VC for ref arg");
    }

    #[test]
    fn test_no_vcs_for_unmatched_function() {
        let func = public_api_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: span(99),
            function_path: "crate::other_function".into(),
            kind: BoundaryKind::PublicApi,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);
        assert!(vcs.is_empty(), "no VCs for non-matching function path");
    }

    #[test]
    fn test_no_vcs_for_internal_boundary() {
        let func = public_api_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Trusted,
            to_zone: TrustZone::Trusted,
            location: span(10),
            function_path: "crate::process".into(),
            kind: BoundaryKind::ModuleBoundary,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);
        assert!(vcs.is_empty(), "internal boundaries should not generate VCs");
    }

    #[test]
    fn test_precondition_vc_formula_structure() {
        let func = public_api_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: span(10),
            function_path: "crate::process".into(),
            kind: BoundaryKind::PublicApi,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);
        let first_vc = &vcs[0];

        // The formula should be And([x >= 0, x <= u32::MAX])
        match &first_vc.formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2, "bounds check should have 2 clauses");
                assert!(
                    matches!(&clauses[0], Formula::Ge(..)),
                    "first clause should be >= (lower bound)"
                );
                assert!(
                    matches!(&clauses[1], Formula::Le(..)),
                    "second clause should be <= (upper bound)"
                );
            }
            other => panic!("expected And formula, got: {other:?}"),
        }
    }

    #[test]
    fn test_signed_bounds_helper() {
        let (min, max) = signed_bounds(32);
        assert_eq!(min, i32::MIN as i128);
        assert_eq!(max, i32::MAX as i128);

        let (min8, max8) = signed_bounds(8);
        assert_eq!(min8, -128);
        assert_eq!(max8, 127);

        let (min128, max128) = signed_bounds(128);
        assert_eq!(min128, i128::MIN);
        assert_eq!(max128, i128::MAX);
    }

    #[test]
    fn test_unsigned_max_helper() {
        assert_eq!(unsigned_max_formula(8), Formula::Int(255));
        assert_eq!(unsigned_max_formula(32), Formula::Int(u32::MAX as i128));
        assert_eq!(unsigned_max_formula(64), Formula::Int(u64::MAX as i128));
        assert_eq!(unsigned_max_formula(128), Formula::UInt(u128::MAX));
    }

    #[test]
    fn test_proof_level_of_boundary_vcs() {
        let func = public_api_function();
        let mut analysis = BoundaryAnalysis::new();
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: span(10),
            function_path: "crate::process".into(),
            kind: BoundaryKind::PublicApi,
        });

        let vcs = generate_boundary_vcs(&analysis, &func);
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L1Functional,
                "boundary VCs should be L1 (functional)"
            );
        }
    }

    #[test]
    fn test_empty_analysis_no_vcs() {
        let func = public_api_function();
        let analysis = BoundaryAnalysis::new();
        let vcs = generate_boundary_vcs(&analysis, &func);
        assert!(vcs.is_empty());
    }
}
