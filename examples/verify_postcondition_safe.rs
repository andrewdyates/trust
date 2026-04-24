// tRust test: postcondition -- safe variant (correct abs implementation)
// VcKind: Postcondition
// Expected: Postcondition PROVED (absent -- abs always returns non-negative)
// Safe pattern: correct abs implementation handles negative inputs properly
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
fn abs_correct(x: i32) -> i32 {
    if x == i32::MIN {
        i32::MAX
    } else if x < 0 {
        -x // SAFE: negates negative values to make them positive
    } else {
        x // already non-negative
    }
}

fn main() {
    println!("{}", abs_correct(5));
    println!("{}", abs_correct(-5));
}
