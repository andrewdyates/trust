// tRust test: postcondition violation
// VcKind: Postcondition
// Expected: Postcondition FAILED
// The postcondition (result >= 0) is violated for negative inputs.
// NOTE: This single-file regression example still uses the legacy contracts
// surface. New crate-based public examples should prefer `trust-spec` and
// `#[trust::ensures(...)]`.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(contracts)]

extern crate core;

use core::contracts::ensures;

#[ensures(|ret: &i32| *ret >= 0)]
fn abs_broken(x: i32) -> i32 {
    x // BUG: returns negative values for negative inputs
}

fn main() {
    println!("{}", abs_broken(5));
}
