// tRust test: postcondition violation
// VcKind: Postcondition
// Expected: Postcondition FAILED
// The postcondition (result >= 0) is violated for negative inputs.
//
// Note: Contract annotations (#[ensures]) depend on compiler parser integration.
// Until available, this test operates at Layer 2 only (synthetic MIR).
// The source file documents the intended contract pattern.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// #[ensures(result >= 0)]
fn abs_broken(x: i32) -> i32 {
    x // BUG: returns negative values for negative inputs
}

fn main() {
    println!("{}", abs_broken(5));
}
