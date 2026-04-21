// trust-vcgen/trait_verify.rs: Trait contract inheritance verification (#80)
//
// Verifies that trait implementations satisfy the Liskov Substitution Principle:
// - Impl preconditions must be at least as weak as trait preconditions (contravariance)
// - Impl postconditions must be at least as strong as trait postconditions (covariance)
//
// This ensures any code written against the trait contract remains correct when
// a concrete impl is substituted.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// tRust: A trait method's contract (preconditions and postconditions).
#[derive(Debug, Clone)]
pub struct TraitContract {
    /// Fully qualified trait name (e.g., "std::iter::Iterator").
    pub trait_name: String,
    /// Method name within the trait.
    pub method: String,
    /// Preconditions the trait promises callers can rely on being accepted.
    pub preconditions: Vec<Formula>,
    /// Postconditions the trait promises callers can rely on being guaranteed.
    pub postconditions: Vec<Formula>,
}

/// tRust: An impl's contract for a trait method.
#[derive(Debug, Clone)]
pub struct ImplContract {
    /// The concrete type implementing the trait (e.g., "MyVec").
    pub impl_type: String,
    /// Method name (must match a trait method).
    pub method: String,
    /// Preconditions the impl requires.
    pub preconditions: Vec<Formula>,
    /// Postconditions the impl guarantees.
    pub postconditions: Vec<Formula>,
}

/// tRust: Verify that an impl's contract satisfies its trait's contract (Liskov).
///
/// Generates verification conditions checking two properties:
///
/// 1. **Precondition contravariance**: For each trait precondition P_trait,
///    we check that (P_trait => P_impl_conj) — i.e., anything accepted by the
///    trait precondition is also accepted by the impl. In practice, the impl
///    should have *weaker* (or equal) preconditions.
///    VC formula: NOT(P_trait => P_impl_conj) — if SAT, the impl rejects
///    something the trait accepts.
///
/// 2. **Postcondition covariance**: For each trait postcondition Q_trait,
///    we check that (Q_impl_conj => Q_trait) — i.e., everything the impl
///    guarantees implies what the trait promises. The impl should have
///    *stronger* (or equal) postconditions.
///    VC formula: NOT(Q_impl_conj => Q_trait) — if SAT, the impl fails to
///    guarantee something the trait promises.
#[must_use]
pub fn verify_liskov(
    trait_c: &TraitContract,
    impl_c: &ImplContract,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let location = SourceSpan::default();

    // Build conjunction of all impl preconditions.
    let impl_pre_conj = conjunction(&impl_c.preconditions);

    // Precondition contravariance: trait_pre => impl_pre_conj
    // The impl must accept at least everything the trait accepts.
    // We negate the implication to find violations: NOT(trait_pre => impl_pre)
    for trait_pre in &trait_c.preconditions {
        let implication = Formula::Implies(
            Box::new(trait_pre.clone()),
            Box::new(impl_pre_conj.clone()),
        );
        vcs.push(VerificationCondition {
            kind: VcKind::Precondition {
                callee: format!(
                    "<{} as {}>::{}",
                    impl_c.impl_type, trait_c.trait_name, trait_c.method
                ),
            },
            function: format!(
                "<{} as {}>::{}",
                impl_c.impl_type, trait_c.trait_name, impl_c.method
            ),
            location: location.clone(),
            formula: Formula::Not(Box::new(implication)),
            contract_metadata: None,
        });
    }

    // Build conjunction of all impl postconditions.
    let impl_post_conj = conjunction(&impl_c.postconditions);

    // Postcondition covariance: impl_post_conj => trait_post
    // The impl must guarantee at least everything the trait promises.
    // We negate the implication to find violations: NOT(impl_post => trait_post)
    for trait_post in &trait_c.postconditions {
        let implication = Formula::Implies(
            Box::new(impl_post_conj.clone()),
            Box::new(trait_post.clone()),
        );
        vcs.push(VerificationCondition {
            kind: VcKind::Postcondition,
            function: format!(
                "<{} as {}>::{}",
                impl_c.impl_type, trait_c.trait_name, impl_c.method
            ),
            location: location.clone(),
            formula: Formula::Not(Box::new(implication)),
            contract_metadata: None,
        });
    }

    vcs
}

/// Build a conjunction of formulas. Returns `true` for empty input.
fn conjunction(formulas: &[Formula]) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas[0].clone(),
        _ => Formula::And(formulas.to_vec()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: x > 0
    fn x_gt_0() -> Formula {
        Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    /// Helper: x >= 0
    fn x_ge_0() -> Formula {
        Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    /// Helper: result > 0
    fn result_gt_0() -> Formula {
        Formula::Gt(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    /// Helper: result >= 0
    fn result_ge_0() -> Formula {
        Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    fn sample_trait_contract() -> TraitContract {
        TraitContract {
            trait_name: "Compute".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        }
    }

    #[test]
    fn test_verify_liskov_identical_contracts_generates_vcs() {
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "MyComputer".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);

        // 1 precondition check + 1 postcondition check
        assert_eq!(vcs.len(), 2);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee.contains("Compute")));
        assert!(matches!(vcs[1].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_verify_liskov_weaker_precondition_valid() {
        // Trait requires x > 0, impl accepts x >= 0 (weaker = accepts more = valid)
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "RelaxedComputer".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_ge_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // The precondition VC is NOT(x>0 => x>=0), which should be UNSAT
        // (meaning the impl validly weakens the precondition)
        let pre_vc = &vcs[0];
        assert!(matches!(&pre_vc.formula, Formula::Not(inner) if matches!(inner.as_ref(), Formula::Implies(_, _))));
    }

    #[test]
    fn test_verify_liskov_stronger_postcondition_valid() {
        // Trait ensures result >= 0, impl ensures result > 0 (stronger = guarantees more = valid)
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "StrictComputer".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_gt_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // The postcondition VC is NOT(result>0 => result>=0), which should be UNSAT
        // (meaning the stronger postcondition satisfies the weaker trait postcondition)
        let post_vc = &vcs[1];
        assert!(matches!(&post_vc.formula, Formula::Not(inner) if matches!(inner.as_ref(), Formula::Implies(_, _))));
    }

    #[test]
    fn test_verify_liskov_stronger_precondition_generates_violation_vc() {
        // Trait requires x >= 0, but impl requires x > 0 (stronger = rejects more = INVALID)
        let trait_c = TraitContract {
            trait_name: "Compute".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_ge_0()],
            postconditions: vec![result_ge_0()],
        };
        let impl_c = ImplContract {
            impl_type: "StricterComputer".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // Precondition VC: NOT(x>=0 => x>0), which IS SAT (x=0 satisfies x>=0 but not x>0)
        // The solver would find this counterexample, proving the impl violates the trait contract.
        let pre_vc = &vcs[0];
        assert!(matches!(&pre_vc.kind, VcKind::Precondition { .. }));
        assert!(pre_vc.function.contains("StricterComputer"));
    }

    #[test]
    fn test_verify_liskov_weaker_postcondition_generates_violation_vc() {
        // Trait ensures result > 0, but impl only ensures result >= 0 (weaker = INVALID)
        let trait_c = TraitContract {
            trait_name: "Compute".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_gt_0()],
        };
        let impl_c = ImplContract {
            impl_type: "WeakComputer".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // Postcondition VC: NOT(result>=0 => result>0), which IS SAT (result=0)
        let post_vc = &vcs[1];
        assert!(matches!(post_vc.kind, VcKind::Postcondition));
        assert!(post_vc.function.contains("WeakComputer"));
    }

    #[test]
    fn test_verify_liskov_empty_contracts() {
        let trait_c = TraitContract {
            trait_name: "Empty".to_string(),
            method: "noop".to_string(),
            preconditions: vec![],
            postconditions: vec![],
        };
        let impl_c = ImplContract {
            impl_type: "MyEmpty".to_string(),
            method: "noop".to_string(),
            preconditions: vec![],
            postconditions: vec![],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert!(vcs.is_empty(), "empty contracts produce no VCs");
    }

    #[test]
    fn test_verify_liskov_multiple_preconditions() {
        // Trait has 2 preconditions
        let trait_c = TraitContract {
            trait_name: "Multi".to_string(),
            method: "process".to_string(),
            preconditions: vec![x_gt_0(), x_ge_0()],
            postconditions: vec![result_ge_0()],
        };
        let impl_c = ImplContract {
            impl_type: "MultiImpl".to_string(),
            method: "process".to_string(),
            preconditions: vec![x_ge_0()],
            postconditions: vec![result_gt_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        // 2 trait preconditions + 1 trait postcondition = 3 VCs
        assert_eq!(vcs.len(), 3);
        assert_eq!(
            vcs.iter().filter(|v| matches!(v.kind, VcKind::Precondition { .. })).count(),
            2
        );
        assert_eq!(
            vcs.iter().filter(|v| matches!(v.kind, VcKind::Postcondition)).count(),
            1
        );
    }

    #[test]
    fn test_verify_liskov_multiple_postconditions() {
        let trait_c = TraitContract {
            trait_name: "Multi".to_string(),
            method: "process".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0(), result_gt_0()],
        };
        let impl_c = ImplContract {
            impl_type: "MultiImpl".to_string(),
            method: "process".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_gt_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        // 1 precondition + 2 postconditions = 3 VCs
        assert_eq!(vcs.len(), 3);
    }

    #[test]
    fn test_verify_liskov_vc_function_names_include_impl_and_trait() {
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "Foo".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        for vc in &vcs {
            assert!(
                vc.function.contains("Foo") && vc.function.contains("Compute"),
                "function name should reference both impl type and trait: got {}",
                vc.function
            );
        }
    }

    #[test]
    fn test_conjunction_empty() {
        assert_eq!(conjunction(&[]), Formula::Bool(true));
    }

    #[test]
    fn test_conjunction_single() {
        let f = x_gt_0();
        assert_eq!(conjunction(std::slice::from_ref(&f)), f);
    }

    #[test]
    fn test_conjunction_multiple() {
        let formulas = vec![x_gt_0(), x_ge_0()];
        let result = conjunction(&formulas);
        assert!(matches!(result, Formula::And(ref v) if v.len() == 2));
    }

    #[test]
    fn test_verify_liskov_impl_with_no_preconditions_is_valid() {
        // An impl with no preconditions (accepts everything) is always valid
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "Permissive".to_string(),
            method: "compute".to_string(),
            preconditions: vec![],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        // 1 precondition VC (trait_pre => true, which is trivially valid) + 1 postcondition VC
        assert_eq!(vcs.len(), 2);

        // The precondition VC formula is NOT(x>0 => true) which is UNSAT — correct
        let pre_vc = &vcs[0];
        if let Formula::Not(inner) = &pre_vc.formula
            && let Formula::Implies(_, rhs) = inner.as_ref()
        {
            assert_eq!(**rhs, Formula::Bool(true), "empty impl preconditions should be true");
        }
    }

    #[test]
    fn test_verify_liskov_proof_levels() {
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "T".to_string(),
            method: "compute".to_string(),
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L1Functional,
                "trait contract VCs should be L1 functional"
            );
        }
    }
}
