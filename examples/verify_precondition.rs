// tRust test: precondition violation at call site
// VcKind: Precondition { callee: "reciprocal" }
// Expected: Precondition FAILED
// NOTE: This single-file regression example still uses the legacy contracts
// surface. New crate-based public examples should prefer `trust-spec` and
// `#[trust::requires(...)]`.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(contracts)]

extern crate core;

use core::contracts::requires;

#[requires(n > 0)]
fn reciprocal(n: u32) -> f64 {
    1.0 / (n as f64)
}

fn caller(x: u32) -> f64 {
    reciprocal(x) // BUG: caller does not check x > 0
}

fn main() {
    println!("{}", caller(5));
}
