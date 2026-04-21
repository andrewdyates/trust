// tRust test: precondition violation at call site
// VcKind: Precondition { callee: "reciprocal" }
// Expected: Precondition FAILED
//
// Note: Contract annotations (#[requires]) depend on compiler parser integration.
// Until available, this test operates at Layer 2 only (synthetic MIR).
// The source file documents the intended contract pattern.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// #[requires(n > 0)]
fn reciprocal(n: u32) -> f64 {
    1.0 / (n as f64)
}

fn caller(x: u32) -> f64 {
    reciprocal(x) // BUG: caller does not check x > 0
}

fn main() {
    println!("{}", caller(5));
}
