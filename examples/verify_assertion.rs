// tRust test: assertion violation
// VcKind: Assertion { message: "sqrt requires non-negative input" }
// Expected: Assertion FAILED
// Counterexample: x = -1 (or any x < 0)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn checked_sqrt_approx(x: i32) -> i32 {
    assert!(x >= 0, "sqrt requires non-negative input");
    x
}

fn caller(val: i32) -> i32 {
    checked_sqrt_approx(val) // BUG: val may be negative
}

fn main() {
    println!("{}", caller(4));
}
