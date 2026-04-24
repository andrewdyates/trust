// trust-cegar: Tests for Rust-specific abstraction domains
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use trust_types::{Formula, Sort};

use crate::abstraction::{AbstractDomain, is_bottom};
use crate::predicate::{AbstractState, CmpOp, Predicate};

use super::borrow_check::BorrowCheckPredicate;
use super::domain::{RustAbstractionDomain, combined_abstraction, refine_with_rust_semantics};
use super::interval::IntervalAbstraction;
use super::lifetime::LifetimeAbstraction;
use super::ownership::{
    OwnershipAbstraction, OwnershipPredicate, OwnershipState, more_restrictive,
};
use super::type_abs::TypeAbstraction;

// -----------------------------------------------------------------------
// OwnershipAbstraction tests
// -----------------------------------------------------------------------

#[test]
fn test_ownership_new_is_empty() {
    let own = OwnershipAbstraction::new();
    assert!(own.is_empty());
    assert_eq!(own.len(), 0);
}

#[test]
fn test_ownership_set_and_get_state() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::Owned);
    own.set_state("y", OwnershipState::MutableBorrow);
    assert_eq!(own.get_state("x"), Some(OwnershipState::Owned));
    assert_eq!(own.get_state("y"), Some(OwnershipState::MutableBorrow));
    assert_eq!(own.get_state("z"), None);
    assert_eq!(own.len(), 2);
}

#[test]
fn test_ownership_is_moved() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::Moved);
    own.set_state("y", OwnershipState::Owned);
    assert!(own.is_moved("x"));
    assert!(!own.is_moved("y"));
    assert!(!own.is_moved("z"));
}

#[test]
fn test_ownership_moved_variables() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("a", OwnershipState::Moved);
    own.set_state("b", OwnershipState::Owned);
    own.set_state("c", OwnershipState::Moved);
    let moved = own.moved_variables();
    assert_eq!(moved.len(), 2);
    assert!(moved.contains(&"a"));
    assert!(moved.contains(&"c"));
}

#[test]
fn test_ownership_join_same_state() {
    let mut a = OwnershipAbstraction::new();
    a.set_state("x", OwnershipState::SharedBorrow);
    let mut b = OwnershipAbstraction::new();
    b.set_state("x", OwnershipState::SharedBorrow);
    let joined = a.join(&b);
    assert_eq!(joined.get_state("x"), Some(OwnershipState::SharedBorrow));
}

#[test]
fn test_ownership_join_disagreement_uses_owned() {
    let mut a = OwnershipAbstraction::new();
    a.set_state("x", OwnershipState::SharedBorrow);
    let mut b = OwnershipAbstraction::new();
    b.set_state("x", OwnershipState::MutableBorrow);
    let joined = a.join(&b);
    assert_eq!(joined.get_state("x"), Some(OwnershipState::Owned));
}

#[test]
fn test_ownership_join_drops_one_sided_vars() {
    let mut a = OwnershipAbstraction::new();
    a.set_state("x", OwnershipState::Owned);
    a.set_state("y", OwnershipState::Owned);
    let mut b = OwnershipAbstraction::new();
    b.set_state("x", OwnershipState::Owned);
    let joined = a.join(&b);
    assert_eq!(joined.get_state("x"), Some(OwnershipState::Owned));
    assert_eq!(joined.get_state("y"), None);
}

#[test]
fn test_ownership_meet_prefers_restrictive() {
    let mut a = OwnershipAbstraction::new();
    a.set_state("x", OwnershipState::Owned);
    let mut b = OwnershipAbstraction::new();
    b.set_state("x", OwnershipState::MutableBorrow);
    let met = a.meet(&b);
    assert_eq!(met.get_state("x"), Some(OwnershipState::MutableBorrow));
}

#[test]
fn test_ownership_meet_adds_new_vars() {
    let mut a = OwnershipAbstraction::new();
    a.set_state("x", OwnershipState::Owned);
    let mut b = OwnershipAbstraction::new();
    b.set_state("y", OwnershipState::SharedBorrow);
    let met = a.meet(&b);
    assert_eq!(met.get_state("x"), Some(OwnershipState::Owned));
    assert_eq!(met.get_state("y"), Some(OwnershipState::SharedBorrow));
}

#[test]
fn test_ownership_to_predicates() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("a", OwnershipState::Moved);
    own.set_state("b", OwnershipState::MutableBorrow);
    own.set_state("c", OwnershipState::SharedBorrow);
    own.set_state("d", OwnershipState::Owned);
    let preds = own.to_predicates();
    assert_eq!(preds.len(), 3); // Owned generates no predicate.
    assert!(preds.contains(&Predicate::Custom("a:moved".into())));
    assert!(preds.contains(&Predicate::Custom("b:exclusive".into())));
    assert!(preds.contains(&Predicate::NonNull("c".into())));
}

#[test]
fn test_ownership_display() {
    assert_eq!(format!("{}", OwnershipState::Owned), "owned");
    assert_eq!(format!("{}", OwnershipState::SharedBorrow), "&");
    assert_eq!(format!("{}", OwnershipState::MutableBorrow), "&mut");
    assert_eq!(format!("{}", OwnershipState::Moved), "moved");
}

// -----------------------------------------------------------------------
// LifetimeAbstraction tests
// -----------------------------------------------------------------------

#[test]
fn test_lifetime_new_is_empty() {
    let lt = LifetimeAbstraction::new();
    assert_eq!(lt.num_relations(), 0);
    assert_eq!(lt.num_bindings(), 0);
}

#[test]
fn test_lifetime_outlives_direct() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    assert!(lt.outlives("'a", "'b"));
    assert!(!lt.outlives("'b", "'a"));
}

#[test]
fn test_lifetime_outlives_transitive() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.add_outlives("'b", "'c");
    assert!(lt.outlives_transitive("'a", "'c"));
    assert!(!lt.outlives_transitive("'c", "'a"));
}

#[test]
fn test_lifetime_outlives_transitive_not_found() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.add_outlives("'c", "'d");
    assert!(!lt.outlives_transitive("'a", "'d"));
}

#[test]
fn test_lifetime_variable_binding() {
    let mut lt = LifetimeAbstraction::new();
    lt.bind_variable("x", "'a");
    lt.bind_variable("y", "'b");
    assert_eq!(lt.variable_lifetime("x"), Some("'a"));
    assert_eq!(lt.variable_lifetime("z"), None);
}

#[test]
fn test_lifetime_is_valid_borrow() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.bind_variable("ref_var", "'b");
    lt.bind_variable("referent", "'a");
    assert!(lt.is_valid_borrow("ref_var", "referent"));
    assert!(!lt.is_valid_borrow("referent", "ref_var"));
}

#[test]
fn test_lifetime_is_valid_borrow_no_info() {
    let lt = LifetimeAbstraction::new();
    assert!(lt.is_valid_borrow("x", "y"));
}

#[test]
fn test_lifetime_join_keeps_common() {
    let mut a = LifetimeAbstraction::new();
    a.add_outlives("'a", "'b");
    a.add_outlives("'a", "'c");
    a.bind_variable("x", "'a");

    let mut b = LifetimeAbstraction::new();
    b.add_outlives("'a", "'b");
    b.bind_variable("x", "'a");

    let joined = a.join(&b);
    assert_eq!(joined.num_relations(), 1);
    assert!(joined.outlives("'a", "'b"));
    assert!(!joined.outlives("'a", "'c"));
    assert_eq!(joined.variable_lifetime("x"), Some("'a"));
}

#[test]
fn test_lifetime_meet_unions_all() {
    let mut a = LifetimeAbstraction::new();
    a.add_outlives("'a", "'b");

    let mut b = LifetimeAbstraction::new();
    b.add_outlives("'c", "'d");

    let met = a.meet(&b);
    assert_eq!(met.num_relations(), 2);
    assert!(met.outlives("'a", "'b"));
    assert!(met.outlives("'c", "'d"));
}

#[test]
fn test_lifetime_to_predicates() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.add_outlives("'b", "'c");
    let preds = lt.to_predicates();
    assert_eq!(preds.len(), 2);
    assert!(preds.contains(&Predicate::Custom("'a:outlives:'b".into())));
    assert!(preds.contains(&Predicate::Custom("'b:outlives:'c".into())));
}

// -----------------------------------------------------------------------
// TypeAbstraction tests
// -----------------------------------------------------------------------

#[test]
fn test_type_new_is_empty() {
    let ty = TypeAbstraction::new();
    assert!(ty.integer_range("x").is_none());
    assert!(ty.discriminants("x").is_none());
}

#[test]
fn test_type_integer_range() {
    let mut ty = TypeAbstraction::new();
    ty.add_integer_range("x", 0, 255);
    assert_eq!(ty.integer_range("x"), Some((0, 255)));
    assert!(ty.is_in_range("x", 0));
    assert!(ty.is_in_range("x", 255));
    assert!(!ty.is_in_range("x", 256));
    assert!(!ty.is_in_range("x", -1));
}

#[test]
fn test_type_integer_range_signed() {
    let mut ty = TypeAbstraction::new();
    ty.add_integer_range("y", -128, 127);
    assert!(ty.is_in_range("y", -128));
    assert!(ty.is_in_range("y", 127));
    assert!(!ty.is_in_range("y", 128));
}

#[test]
fn test_type_enum_discriminants() {
    let mut ty = TypeAbstraction::new();
    ty.add_enum_discriminants("opt", [0, 1]);
    assert!(ty.is_valid_discriminant("opt", 0));
    assert!(ty.is_valid_discriminant("opt", 1));
    assert!(!ty.is_valid_discriminant("opt", 2));
    assert!(!ty.is_valid_discriminant("opt", -1));
}

#[test]
fn test_type_enum_discriminants_unknown_var() {
    let ty = TypeAbstraction::new();
    assert!(ty.is_valid_discriminant("unknown", 42));
}

#[test]
fn test_type_boolean() {
    let mut ty = TypeAbstraction::new();
    ty.add_boolean("flag");
    assert!(ty.is_boolean("flag"));
    assert!(!ty.is_boolean("x"));
}

#[test]
fn test_type_non_null_ref() {
    let mut ty = TypeAbstraction::new();
    ty.add_non_null_ref("ptr");
    assert!(ty.is_non_null_ref("ptr"));
    assert!(!ty.is_non_null_ref("val"));
}

#[test]
fn test_type_is_consistent() {
    let mut ty = TypeAbstraction::new();
    ty.add_integer_range("x", 0, 255);
    ty.add_enum_discriminants("disc", [0, 1, 2]);
    ty.add_boolean("flag");

    assert!(ty.is_consistent("x", 100));
    assert!(!ty.is_consistent("x", 300));
    assert!(ty.is_consistent("disc", 1));
    assert!(!ty.is_consistent("disc", 5));
    assert!(ty.is_consistent("flag", 0));
    assert!(ty.is_consistent("flag", 1));
    assert!(!ty.is_consistent("flag", 2));
}

#[test]
fn test_type_join_widens_ranges() {
    let mut a = TypeAbstraction::new();
    a.add_integer_range("x", 0, 100);
    let mut b = TypeAbstraction::new();
    b.add_integer_range("x", 50, 200);
    let joined = a.join(&b);
    assert_eq!(joined.integer_range("x"), Some((0, 200)));
}

#[test]
fn test_type_join_unions_discriminants() {
    let mut a = TypeAbstraction::new();
    a.add_enum_discriminants("e", [0, 1]);
    let mut b = TypeAbstraction::new();
    b.add_enum_discriminants("e", [1, 2]);
    let joined = a.join(&b);
    let discs = joined.discriminants("e").unwrap();
    assert_eq!(*discs, BTreeSet::from([0, 1, 2]));
}

#[test]
fn test_type_meet_narrows_ranges() {
    let mut a = TypeAbstraction::new();
    a.add_integer_range("x", 0, 200);
    let mut b = TypeAbstraction::new();
    b.add_integer_range("x", 50, 150);
    let met = a.meet(&b);
    assert_eq!(met.integer_range("x"), Some((50, 150)));
}

#[test]
fn test_type_meet_intersects_discriminants() {
    let mut a = TypeAbstraction::new();
    a.add_enum_discriminants("e", [0, 1, 2]);
    let mut b = TypeAbstraction::new();
    b.add_enum_discriminants("e", [1, 2, 3]);
    let met = a.meet(&b);
    let discs = met.discriminants("e").unwrap();
    assert_eq!(*discs, BTreeSet::from([1, 2]));
}

#[test]
fn test_type_to_predicates() {
    let mut ty = TypeAbstraction::new();
    ty.add_integer_range("x", 0, 255);
    ty.add_boolean("flag");
    ty.add_non_null_ref("ptr");
    ty.add_enum_discriminants("opt", [0, 1]);
    let preds = ty.to_predicates();
    assert!(preds.contains(&Predicate::range("x", 0, 255)));
    assert!(preds.contains(&Predicate::range("flag", 0, 1)));
    assert!(preds.contains(&Predicate::NonNull("ptr".into())));
    assert!(preds.contains(&Predicate::range("opt", 0, 1)));
}

// -----------------------------------------------------------------------
// RustAbstractionDomain tests
// -----------------------------------------------------------------------

#[test]
fn test_rust_domain_new_is_default() {
    let domain = RustAbstractionDomain::new();
    assert!(domain.ownership.is_empty());
    assert_eq!(domain.lifetimes.num_relations(), 0);
}

#[test]
fn test_rust_domain_all_predicates_combines_sub_domains() {
    let mut domain = RustAbstractionDomain::new();
    domain.ownership.set_state("a", OwnershipState::Moved);
    domain.lifetimes.add_outlives("'x", "'y");
    domain.type_info.add_integer_range("n", 0, 100);
    let preds = domain.all_predicates();
    assert!(preds.contains(&Predicate::Custom("a:moved".into())));
    assert!(preds.contains(&Predicate::Custom("'x:outlives:'y".into())));
    assert!(preds.contains(&Predicate::range("n", 0, 100)));
}

#[test]
fn test_rust_domain_is_infeasible_moved_var() {
    let mut domain = RustAbstractionDomain::new();
    domain.ownership.set_state("x", OwnershipState::Moved);
    assert!(domain.is_infeasible("x", 42));
}

#[test]
fn test_rust_domain_is_infeasible_type_violation() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 255);
    assert!(domain.is_infeasible("x", 300));
    assert!(!domain.is_infeasible("x", 100));
}

#[test]
fn test_rust_domain_is_infeasible_no_constraints() {
    let domain = RustAbstractionDomain::new();
    assert!(!domain.is_infeasible("x", 42));
}

#[test]
fn test_rust_domain_implements_abstract_domain_top() {
    let domain = RustAbstractionDomain::new();
    let top = domain.top();
    assert!(top.is_empty());
}

#[test]
fn test_rust_domain_implements_abstract_domain_bottom() {
    let domain = RustAbstractionDomain::new();
    let bot = domain.bottom();
    assert!(is_bottom(&bot));
}

#[test]
fn test_rust_domain_join_preserves_type_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 255);

    let mut a = AbstractState::top();
    a.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    a.add(Predicate::comparison("y", CmpOp::Lt, "10"));

    let mut b = AbstractState::top();
    b.add(Predicate::comparison("x", CmpOp::Ge, "0"));

    let joined = domain.join(&a, &b);
    assert!(joined.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
    assert!(!joined.contains(&Predicate::comparison("y", CmpOp::Lt, "10")));
    assert!(joined.contains(&Predicate::range("x", 0, 255)));
}

#[test]
fn test_rust_domain_join_with_bottom() {
    let domain = RustAbstractionDomain::new();
    let bot = domain.bottom();
    let mut a = AbstractState::top();
    a.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    let joined = domain.join(&bot, &a);
    assert!(joined.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
}

#[test]
fn test_rust_domain_meet_adds_rust_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_non_null_ref("ptr");
    let a = AbstractState::top();
    let b = AbstractState::top();
    let met = domain.meet(&a, &b);
    assert!(met.contains(&Predicate::NonNull("ptr".into())));
}

#[test]
fn test_rust_domain_widen_preserves_type_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_boolean("flag");
    let mut prev = AbstractState::top();
    prev.add(Predicate::comparison("x", CmpOp::Lt, "5"));
    let mut next = AbstractState::top();
    next.add(Predicate::comparison("x", CmpOp::Lt, "10"));
    let widened = domain.widen(&prev, &next);
    assert!(widened.contains(&Predicate::range("flag", 0, 1)));
}

// -----------------------------------------------------------------------
// combined_abstraction tests
// -----------------------------------------------------------------------

#[test]
fn test_combined_abstraction_integrates_all() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::Owned);

    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");

    let mut ty = TypeAbstraction::new();
    ty.add_integer_range("x", 0, 255);

    let domain = combined_abstraction(&own, &lt, &ty);
    assert_eq!(domain.ownership.get_state("x"), Some(OwnershipState::Owned));
    assert!(domain.lifetimes.outlives("'a", "'b"));
    assert_eq!(domain.type_info.integer_range("x"), Some((0, 255)));
}

// -----------------------------------------------------------------------
// refine_with_rust_semantics tests
// -----------------------------------------------------------------------

#[test]
fn test_refine_empty_cex_returns_domain_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 100);
    let preds = refine_with_rust_semantics(&[], &domain);
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
}

#[test]
fn test_refine_adds_moved_predicate_for_moved_var() {
    let mut domain = RustAbstractionDomain::new();
    domain.ownership.set_state("val", OwnershipState::Moved);
    let cex = vec![Formula::Var("val".into(), Sort::Int)];
    let preds = refine_with_rust_semantics(&cex, &domain);
    assert!(preds.contains(&Predicate::Custom("val:moved".into())));
}

#[test]
fn test_refine_adds_range_for_typed_var() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_integer_range("idx", 0, 255);
    let cex = vec![Formula::Eq(
        Box::new(Formula::Var("idx".into(), Sort::Int)),
        Box::new(Formula::Int(300)),
    )];
    let preds = refine_with_rust_semantics(&cex, &domain);
    assert!(preds.contains(&Predicate::range("idx", 0, 255)));
}

#[test]
fn test_refine_adds_non_null_for_ref() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_non_null_ref("ptr");
    let cex = vec![Formula::Eq(
        Box::new(Formula::Var("ptr".into(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )];
    let preds = refine_with_rust_semantics(&cex, &domain);
    assert!(preds.contains(&Predicate::NonNull("ptr".into())));
}

#[test]
fn test_refine_adds_discriminant_range() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_enum_discriminants("result", [0, 1]);
    let cex = vec![Formula::Var("result".into(), Sort::Int)];
    let preds = refine_with_rust_semantics(&cex, &domain);
    assert!(preds.contains(&Predicate::range("result", 0, 1)));
}

#[test]
fn test_refine_deduplicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 100);
    let cex = vec![
        Formula::Var("x".into(), Sort::Int),
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(50))),
    ];
    let preds = refine_with_rust_semantics(&cex, &domain);
    let range_count = preds.iter().filter(|p| **p == Predicate::range("x", 0, 100)).count();
    assert_eq!(range_count, 1);
}

#[test]
fn test_refine_handles_nested_and() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_non_null_ref("a");
    domain.type_info.add_non_null_ref("b");
    let cex = vec![Formula::And(vec![
        Formula::Var("a".into(), Sort::Int),
        Formula::Var("b".into(), Sort::Int),
    ])];
    let preds = refine_with_rust_semantics(&cex, &domain);
    assert!(preds.contains(&Predicate::NonNull("a".into())));
    assert!(preds.contains(&Predicate::NonNull("b".into())));
}

#[test]
fn test_refine_with_no_domain_info_returns_empty_from_cex() {
    let domain = RustAbstractionDomain::new();
    let cex = vec![Formula::Var("x".into(), Sort::Int)];
    let preds = refine_with_rust_semantics(&cex, &domain);
    assert!(preds.is_empty());
}

// -----------------------------------------------------------------------
// Integration: sub-domain join/meet with domain predicates
// -----------------------------------------------------------------------

#[test]
fn test_ownership_join_with_type_domain() {
    let mut own_a = OwnershipAbstraction::new();
    own_a.set_state("x", OwnershipState::SharedBorrow);
    own_a.set_state("y", OwnershipState::Owned);

    let mut own_b = OwnershipAbstraction::new();
    own_b.set_state("x", OwnershipState::SharedBorrow);
    own_b.set_state("y", OwnershipState::MutableBorrow);

    let joined = own_a.join(&own_b);
    assert_eq!(joined.get_state("x"), Some(OwnershipState::SharedBorrow));
    assert_eq!(joined.get_state("y"), Some(OwnershipState::Owned));
}

#[test]
fn test_lifetime_join_binding_disagreement() {
    let mut a = LifetimeAbstraction::new();
    a.bind_variable("x", "'a");
    let mut b = LifetimeAbstraction::new();
    b.bind_variable("x", "'b");
    let joined = a.join(&b);
    assert_eq!(joined.variable_lifetime("x"), None);
}

#[test]
fn test_type_join_drops_one_sided_range() {
    let mut a = TypeAbstraction::new();
    a.add_integer_range("x", 0, 100);
    let b = TypeAbstraction::new();
    let joined = a.join(&b);
    assert_eq!(joined.integer_range("x"), None);
}

#[test]
fn test_type_meet_adds_one_sided_range() {
    let mut a = TypeAbstraction::new();
    a.add_integer_range("x", 0, 100);
    let b = TypeAbstraction::new();
    let met = a.meet(&b);
    assert_eq!(met.integer_range("x"), Some((0, 100)));
}

#[test]
fn test_more_restrictive_ordering() {
    assert_eq!(
        more_restrictive(OwnershipState::Owned, OwnershipState::Moved),
        OwnershipState::Moved
    );
    assert_eq!(
        more_restrictive(OwnershipState::MutableBorrow, OwnershipState::SharedBorrow),
        OwnershipState::MutableBorrow
    );
    assert_eq!(
        more_restrictive(OwnershipState::Owned, OwnershipState::Owned),
        OwnershipState::Owned
    );
}

// -----------------------------------------------------------------------
// OwnershipPredicate tests
// -----------------------------------------------------------------------

#[test]
fn test_ownership_predicate_variable() {
    let pred = OwnershipPredicate::IsOwned("x".into());
    assert_eq!(pred.variable(), "x");
    let pred = OwnershipPredicate::IsMutRef("y".into());
    assert_eq!(pred.variable(), "y");
}

#[test]
fn test_ownership_predicate_conflicts_different_states() {
    let owned = OwnershipPredicate::IsOwned("x".into());
    let moved = OwnershipPredicate::IsMoved("x".into());
    assert!(owned.conflicts_with(&moved));
    assert!(moved.conflicts_with(&owned));
}

#[test]
fn test_ownership_predicate_no_conflict_same_state() {
    let a = OwnershipPredicate::IsOwned("x".into());
    let b = OwnershipPredicate::IsOwned("x".into());
    assert!(!a.conflicts_with(&b));
}

#[test]
fn test_ownership_predicate_no_conflict_different_vars() {
    let a = OwnershipPredicate::IsOwned("x".into());
    let b = OwnershipPredicate::IsMoved("y".into());
    assert!(!a.conflicts_with(&b));
}

#[test]
fn test_ownership_predicate_to_predicate() {
    let owned = OwnershipPredicate::IsOwned("x".into());
    assert_eq!(owned.to_predicate(), Predicate::Custom("x:ownership:owned".into()));

    let shared = OwnershipPredicate::IsSharedRef("r".into());
    assert_eq!(shared.to_predicate(), Predicate::Custom("r:ownership:shared_ref".into()));

    let mut_ref = OwnershipPredicate::IsMutRef("m".into());
    assert_eq!(mut_ref.to_predicate(), Predicate::Custom("m:ownership:mut_ref".into()));

    let moved = OwnershipPredicate::IsMoved("v".into());
    assert_eq!(moved.to_predicate(), Predicate::Custom("v:moved".into()));

    let dropped = OwnershipPredicate::IsDropped("d".into());
    assert_eq!(dropped.to_predicate(), Predicate::Custom("d:ownership:dropped".into()));
}

#[test]
fn test_ownership_predicate_blocks_access() {
    assert!(!OwnershipPredicate::IsOwned("x".into()).blocks_access());
    assert!(!OwnershipPredicate::IsSharedRef("x".into()).blocks_access());
    assert!(!OwnershipPredicate::IsMutRef("x".into()).blocks_access());
    assert!(OwnershipPredicate::IsMoved("x".into()).blocks_access());
    assert!(OwnershipPredicate::IsDropped("x".into()).blocks_access());
}

#[test]
fn test_ownership_predicate_display() {
    assert_eq!(format!("{}", OwnershipPredicate::IsOwned("x".into())), "x: owned");
    assert_eq!(format!("{}", OwnershipPredicate::IsSharedRef("r".into())), "r: &T");
    assert_eq!(format!("{}", OwnershipPredicate::IsMutRef("m".into())), "m: &mut T");
    assert_eq!(format!("{}", OwnershipPredicate::IsMoved("v".into())), "v: moved");
    assert_eq!(format!("{}", OwnershipPredicate::IsDropped("d".into())), "d: dropped");
}

// -----------------------------------------------------------------------
// BorrowCheckPredicate tests
// -----------------------------------------------------------------------

#[test]
fn test_borrow_check_no_mut_while_shared_to_predicate() {
    let pred = BorrowCheckPredicate::NoMutWhileShared { place: "x".into() };
    assert_eq!(pred.to_predicate(), Predicate::Custom("x:no_mut_while_shared".into()));
}

#[test]
fn test_borrow_check_exclusive_mut_to_predicate() {
    let pred = BorrowCheckPredicate::ExclusiveMut { place: "x".into() };
    assert_eq!(pred.to_predicate(), Predicate::Custom("x:exclusive_mut".into()));
}

#[test]
fn test_borrow_check_borrow_active_to_predicate() {
    let pred =
        BorrowCheckPredicate::BorrowActive { borrow_var: "ref_x".into(), referent: "x".into() };
    assert_eq!(pred.to_predicate(), Predicate::Custom("ref_x:borrows:x".into()));
}

#[test]
fn test_borrow_check_no_alias_canonical_ordering() {
    let pred1 = BorrowCheckPredicate::NoAlias { var_a: "b".into(), var_b: "a".into() };
    let pred2 = BorrowCheckPredicate::NoAlias { var_a: "a".into(), var_b: "b".into() };
    assert_eq!(pred1.to_predicate(), pred2.to_predicate());
    assert_eq!(pred1.to_predicate(), Predicate::Custom("a:no_alias:b".into()));
}

#[test]
fn test_borrow_check_shared_borrow_count_to_predicate() {
    let pred = BorrowCheckPredicate::SharedBorrowCount { place: "buf".into(), max_shared: 3 };
    assert_eq!(pred.to_predicate(), Predicate::Custom("buf:shared_borrow_count:<=3".into()));
}

#[test]
fn test_borrow_check_no_mut_while_shared_violation() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::MutableBorrow);
    own.set_state("y", OwnershipState::SharedBorrow);
    let pred = BorrowCheckPredicate::NoMutWhileShared { place: "x".into() };
    assert!(pred.is_violated(&own));
}

#[test]
fn test_borrow_check_no_mut_while_shared_no_violation() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::SharedBorrow);
    own.set_state("y", OwnershipState::SharedBorrow);
    let pred = BorrowCheckPredicate::NoMutWhileShared { place: "x".into() };
    assert!(!pred.is_violated(&own));
}

#[test]
fn test_borrow_check_exclusive_mut_violation() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::MutableBorrow);
    own.set_state("y", OwnershipState::SharedBorrow);
    let pred = BorrowCheckPredicate::ExclusiveMut { place: "x".into() };
    assert!(pred.is_violated(&own));
}

#[test]
fn test_borrow_check_exclusive_mut_no_violation_single() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("x", OwnershipState::MutableBorrow);
    own.set_state("y", OwnershipState::Owned);
    let pred = BorrowCheckPredicate::ExclusiveMut { place: "x".into() };
    assert!(!pred.is_violated(&own));
}

#[test]
fn test_borrow_check_borrow_active_violation_moved() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("ref_x", OwnershipState::Moved);
    let pred =
        BorrowCheckPredicate::BorrowActive { borrow_var: "ref_x".into(), referent: "x".into() };
    assert!(pred.is_violated(&own));
}

#[test]
fn test_borrow_check_borrow_active_no_violation() {
    let mut own = OwnershipAbstraction::new();
    own.set_state("ref_x", OwnershipState::SharedBorrow);
    let pred =
        BorrowCheckPredicate::BorrowActive { borrow_var: "ref_x".into(), referent: "x".into() };
    assert!(!pred.is_violated(&own));
}

#[test]
fn test_borrow_check_display() {
    let p1 = BorrowCheckPredicate::NoMutWhileShared { place: "x".into() };
    assert_eq!(format!("{p1}"), "no_mut_while_shared(x)");

    let p2 = BorrowCheckPredicate::ExclusiveMut { place: "x".into() };
    assert_eq!(format!("{p2}"), "exclusive_mut(x)");

    let p3 = BorrowCheckPredicate::BorrowActive { borrow_var: "r".into(), referent: "x".into() };
    assert_eq!(format!("{p3}"), "borrow_active(r -> x)");

    let p4 = BorrowCheckPredicate::NoAlias { var_a: "a".into(), var_b: "b".into() };
    assert_eq!(format!("{p4}"), "no_alias(a, b)");

    let p5 = BorrowCheckPredicate::SharedBorrowCount { place: "buf".into(), max_shared: 5 };
    assert_eq!(format!("{p5}"), "shared_borrow_count(buf) <= 5");
}

// -----------------------------------------------------------------------
// IntervalAbstraction tests
// -----------------------------------------------------------------------

#[test]
fn test_interval_new_is_empty() {
    let ia = IntervalAbstraction::new();
    assert!(ia.is_empty());
    assert_eq!(ia.len(), 0);
}

#[test]
fn test_interval_set_and_get() {
    let mut ia = IntervalAbstraction::new();
    ia.set_interval("x", 0, 100);
    assert_eq!(ia.get_interval("x"), Some((0, 100)));
    assert_eq!(ia.get_interval("y"), None);
    assert_eq!(ia.len(), 1);
}

#[test]
fn test_interval_contains_value() {
    let mut ia = IntervalAbstraction::new();
    ia.set_interval("x", 0, 100);
    assert!(ia.contains_value("x", 0));
    assert!(ia.contains_value("x", 50));
    assert!(ia.contains_value("x", 100));
    assert!(!ia.contains_value("x", -1));
    assert!(!ia.contains_value("x", 101));
    assert!(ia.contains_value("y", 42));
}

#[test]
fn test_interval_refine_from_cex_inside() {
    let mut ia = IntervalAbstraction::new();
    ia.set_interval("x", 0, 100);
    let preds = ia.refine_from_cex("x", 50);
    assert!(!preds.is_empty());
    assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "50")));
    assert!(preds.contains(&Predicate::comparison("x", CmpOp::Gt, "50")));
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
}

#[test]
fn test_interval_refine_from_cex_at_boundary() {
    let mut ia = IntervalAbstraction::new();
    ia.set_interval("x", 0, 100);
    let preds = ia.refine_from_cex("x", 0);
    assert!(preds.contains(&Predicate::comparison("x", CmpOp::Gt, "0")));
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
}

#[test]
fn test_interval_refine_from_cex_outside() {
    let mut ia = IntervalAbstraction::new();
    ia.set_interval("x", 0, 100);
    let preds = ia.refine_from_cex("x", 200);
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
}

#[test]
fn test_interval_refine_from_cex_no_interval() {
    let mut ia = IntervalAbstraction::new();
    let preds = ia.refine_from_cex("x", 50);
    assert!(preds.contains(&Predicate::comparison("x", CmpOp::Ge, "51")));
    assert!(preds.contains(&Predicate::comparison("x", CmpOp::Le, "49")));
}

#[test]
fn test_interval_join_widens() {
    let mut a = IntervalAbstraction::new();
    a.set_interval("x", 0, 50);
    let mut b = IntervalAbstraction::new();
    b.set_interval("x", 30, 100);
    let joined = a.join(&b);
    assert_eq!(joined.get_interval("x"), Some((0, 100)));
}

#[test]
fn test_interval_join_drops_one_sided() {
    let mut a = IntervalAbstraction::new();
    a.set_interval("x", 0, 50);
    let b = IntervalAbstraction::new();
    let joined = a.join(&b);
    assert_eq!(joined.get_interval("x"), None);
}

#[test]
fn test_interval_meet_narrows() {
    let mut a = IntervalAbstraction::new();
    a.set_interval("x", 0, 100);
    let mut b = IntervalAbstraction::new();
    b.set_interval("x", 30, 70);
    let met = a.meet(&b);
    assert_eq!(met.get_interval("x"), Some((30, 70)));
}

#[test]
fn test_interval_meet_adds_one_sided() {
    let mut a = IntervalAbstraction::new();
    a.set_interval("x", 0, 50);
    let mut b = IntervalAbstraction::new();
    b.set_interval("y", 10, 20);
    let met = a.meet(&b);
    assert_eq!(met.get_interval("x"), Some((0, 50)));
    assert_eq!(met.get_interval("y"), Some((10, 20)));
}

#[test]
fn test_interval_to_predicates() {
    let mut ia = IntervalAbstraction::new();
    ia.set_interval("x", 0, 100);
    ia.set_interval("y", -10, 10);
    let preds = ia.to_predicates();
    assert_eq!(preds.len(), 2);
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
    assert!(preds.contains(&Predicate::range("y", -10, 10)));
}

// -----------------------------------------------------------------------
// LifetimeAbstraction refinement tests
// -----------------------------------------------------------------------

#[test]
fn test_lifetime_refine_from_borrow_creates_outlives() {
    let mut lt = LifetimeAbstraction::new();
    lt.bind_variable("ref_var", "'b");
    lt.bind_variable("referent", "'a");
    let preds = lt.refine_from_borrow("ref_var", "referent");
    assert!(lt.outlives("'a", "'b"));
    assert!(preds.contains(&Predicate::Custom("'a:outlives:'b".into())));
}

#[test]
fn test_lifetime_refine_from_borrow_no_duplicate() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.bind_variable("ref_var", "'b");
    lt.bind_variable("referent", "'a");
    let preds = lt.refine_from_borrow("ref_var", "referent");
    assert!(preds.is_empty());
}

#[test]
fn test_lifetime_refine_from_borrow_auto_binds() {
    let mut lt = LifetimeAbstraction::new();
    let preds = lt.refine_from_borrow("r", "x");
    assert!(!preds.is_empty());
    assert!(lt.variable_lifetime("r").is_some());
    assert!(lt.variable_lifetime("x").is_some());
}

#[test]
fn test_lifetime_all_lifetimes() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.bind_variable("x", "'c");
    let all = lt.all_lifetimes();
    assert!(all.contains("'a"));
    assert!(all.contains("'b"));
    assert!(all.contains("'c"));
}

#[test]
fn test_lifetime_are_compatible_same() {
    let mut lt = LifetimeAbstraction::new();
    lt.bind_variable("x", "'a");
    lt.bind_variable("y", "'a");
    assert!(lt.are_compatible("x", "y"));
}

#[test]
fn test_lifetime_are_compatible_outlives() {
    let mut lt = LifetimeAbstraction::new();
    lt.add_outlives("'a", "'b");
    lt.bind_variable("x", "'a");
    lt.bind_variable("y", "'b");
    assert!(lt.are_compatible("x", "y"));
}

#[test]
fn test_lifetime_are_compatible_no_info() {
    let lt = LifetimeAbstraction::new();
    assert!(lt.are_compatible("x", "y"));
}

#[test]
fn test_lifetime_are_compatible_unrelated() {
    let mut lt = LifetimeAbstraction::new();
    lt.bind_variable("x", "'a");
    lt.bind_variable("y", "'b");
    assert!(!lt.are_compatible("x", "y"));
}

// -----------------------------------------------------------------------
// RustAbstractionDomain extended tests
// -----------------------------------------------------------------------

#[test]
fn test_rust_domain_all_predicates_includes_new_fields() {
    let mut domain = RustAbstractionDomain::new();
    domain.intervals.set_interval("x", 0, 100);
    domain.add_borrow_check(BorrowCheckPredicate::ExclusiveMut { place: "y".into() });
    domain.add_ownership_predicate(OwnershipPredicate::IsOwned("z".into()));

    let preds = domain.all_predicates();
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
    assert!(preds.contains(&Predicate::Custom("y:exclusive_mut".into())));
    assert!(preds.contains(&Predicate::Custom("z:ownership:owned".into())));
}

#[test]
fn test_rust_domain_is_infeasible_interval_violation() {
    let mut domain = RustAbstractionDomain::new();
    domain.intervals.set_interval("x", 0, 100);
    assert!(domain.is_infeasible("x", 200));
    assert!(!domain.is_infeasible("x", 50));
}

#[test]
fn test_rust_domain_is_infeasible_ownership_predicate_blocks() {
    let mut domain = RustAbstractionDomain::new();
    domain.add_ownership_predicate(OwnershipPredicate::IsMoved("x".into()));
    assert!(domain.is_infeasible("x", 42));
}

#[test]
fn test_rust_domain_is_infeasible_borrow_check_violation() {
    let mut domain = RustAbstractionDomain::new();
    domain.ownership.set_state("x", OwnershipState::MutableBorrow);
    domain.ownership.set_state("y", OwnershipState::SharedBorrow);
    domain.add_borrow_check(BorrowCheckPredicate::NoMutWhileShared { place: "x".into() });
    assert!(domain.is_infeasible("x", 0));
}

#[test]
fn test_rust_domain_add_ownership_predicate_replaces_conflict() {
    let mut domain = RustAbstractionDomain::new();
    domain.add_ownership_predicate(OwnershipPredicate::IsOwned("x".into()));
    assert_eq!(domain.ownership_predicates.len(), 1);
    domain.add_ownership_predicate(OwnershipPredicate::IsMoved("x".into()));
    assert_eq!(domain.ownership_predicates.len(), 1);
    assert_eq!(domain.ownership_predicates[0], OwnershipPredicate::IsMoved("x".into()));
}

#[test]
fn test_rust_domain_add_borrow_check_no_duplicate() {
    let mut domain = RustAbstractionDomain::new();
    let pred = BorrowCheckPredicate::ExclusiveMut { place: "x".into() };
    domain.add_borrow_check(pred.clone());
    domain.add_borrow_check(pred);
    assert_eq!(domain.borrow_checks.len(), 1);
}

#[test]
fn test_rust_domain_refine_from_counterexample_moved() {
    let mut domain = RustAbstractionDomain::new();
    domain.ownership.set_state("x", OwnershipState::Moved);
    let preds = domain.refine_from_counterexample(&[("x", 42)]);
    assert!(preds.contains(&Predicate::Custom("x:moved".into())));
}

#[test]
fn test_rust_domain_refine_from_counterexample_type_violation() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 255);
    let preds = domain.refine_from_counterexample(&[("x", 300)]);
    assert!(preds.contains(&Predicate::range("x", 0, 255)));
}

#[test]
fn test_rust_domain_refine_from_counterexample_interval() {
    let mut domain = RustAbstractionDomain::new();
    domain.intervals.set_interval("x", 0, 100);
    let preds = domain.refine_from_counterexample(&[("x", 50)]);
    assert!(!preds.is_empty());
}

#[test]
fn test_rust_domain_refine_from_counterexample_non_null_ref() {
    let mut domain = RustAbstractionDomain::new();
    domain.type_info.add_non_null_ref("ptr");
    let preds = domain.refine_from_counterexample(&[("ptr", 42)]);
    assert!(preds.contains(&Predicate::NonNull("ptr".into())));
}

#[test]
fn test_rust_domain_refine_from_counterexample_borrow_check_violation() {
    let mut domain = RustAbstractionDomain::new();
    domain.ownership.set_state("x", OwnershipState::MutableBorrow);
    domain.ownership.set_state("y", OwnershipState::SharedBorrow);
    domain.add_borrow_check(BorrowCheckPredicate::NoMutWhileShared { place: "x".into() });
    let preds = domain.refine_from_counterexample(&[("z", 0)]);
    assert!(preds.contains(&Predicate::Custom("x:no_mut_while_shared".into())));
}

#[test]
fn test_rust_domain_join_preserves_ownership_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.add_ownership_predicate(OwnershipPredicate::IsOwned("x".into()));

    let mut a = AbstractState::top();
    a.add(Predicate::comparison("y", CmpOp::Ge, "0"));
    let b = AbstractState::top();

    let joined = domain.join(&a, &b);
    assert!(joined.contains(&Predicate::Custom("x:ownership:owned".into())));
}

#[test]
fn test_rust_domain_join_preserves_borrow_check_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.add_borrow_check(BorrowCheckPredicate::ExclusiveMut { place: "x".into() });

    let a = AbstractState::top();
    let b = AbstractState::top();

    let joined = domain.join(&a, &b);
    assert!(joined.contains(&Predicate::Custom("x:exclusive_mut".into())));
}

#[test]
fn test_rust_domain_widen_preserves_ownership_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.add_ownership_predicate(OwnershipPredicate::IsMutRef("r".into()));

    let prev = AbstractState::top();
    let next = AbstractState::top();
    let widened = domain.widen(&prev, &next);
    assert!(widened.contains(&Predicate::Custom("r:ownership:mut_ref".into())));
}

#[test]
fn test_rust_domain_widen_preserves_borrow_check_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.add_borrow_check(BorrowCheckPredicate::NoMutWhileShared { place: "x".into() });

    let prev = AbstractState::top();
    let next = AbstractState::top();
    let widened = domain.widen(&prev, &next);
    assert!(widened.contains(&Predicate::Custom("x:no_mut_while_shared".into())));
}

#[test]
fn test_rust_domain_join_preserves_interval_predicates() {
    let mut domain = RustAbstractionDomain::new();
    domain.intervals.set_interval("x", 0, 100);

    let a = AbstractState::top();
    let b = AbstractState::top();

    let joined = domain.join(&a, &b);
    assert!(joined.contains(&Predicate::range("x", 0, 100)));
}

#[test]
fn test_combined_abstraction_includes_new_fields() {
    let own = OwnershipAbstraction::new();
    let lt = LifetimeAbstraction::new();
    let ty = TypeAbstraction::new();
    let domain = combined_abstraction(&own, &lt, &ty);
    assert!(domain.intervals.is_empty());
    assert!(domain.borrow_checks.is_empty());
    assert!(domain.ownership_predicates.is_empty());
}
