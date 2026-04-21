// trust-cegar: Rust-specific abstraction domains for CEGAR
//
// Retains Rust-specific abstractions (ownership, lifetime, type) rather than
// falling back to generic predicate abstraction. These domains exploit Rust's
// type system guarantees to prune infeasible paths and generate more precise
// predicates during counterexample-guided refinement.
//
// Key insight: Rust's ownership model, lifetime system, and enum discriminants
// provide strong invariants that a generic CEGAR loop would have to rediscover
// through expensive predicate refinement. By encoding these as first-class
// abstract domains, we start with a much tighter abstraction.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod borrow_check;
mod domain;
mod interval;
mod lifetime;
mod ownership;
mod type_abs;

#[cfg(test)]
mod tests;

pub use borrow_check::BorrowCheckPredicate;
pub use domain::{RustAbstractionDomain, combined_abstraction, refine_with_rust_semantics};
pub use interval::IntervalAbstraction;
pub use lifetime::LifetimeAbstraction;
pub use ownership::{OwnershipAbstraction, OwnershipPredicate, OwnershipState};
pub use type_abs::TypeAbstraction;
