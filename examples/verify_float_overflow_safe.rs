// tRust test: float addition overflow to infinity -- safe variant
// VcKind: FloatOverflowToInfinity { op: BinOp::Add, operand_ty: Ty::Float { width: 64 } }
// Expected: FloatOverflowToInfinity(Add) PROVED (absent -- range-limited inputs)
// Safe pattern: precondition guards ensure inputs are within safe range
//               so addition cannot exceed f64::MAX
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

const SAFE_LIMIT: f64 = 1.0e300; // well below f64::MAX (~1.8e308)

fn float_add_safe(a: f64, b: f64) -> f64 {
    if a.abs() > SAFE_LIMIT || b.abs() > SAFE_LIMIT {
        0.0 // fallback: reject inputs that could overflow
    } else {
        a + b // SAFE: both operands bounded, sum cannot reach Inf
    }
}

fn main() {
    println!("{}", float_add_safe(1.0, 2.0));
    println!("{}", float_add_safe(f64::MAX, 1.0)); // takes fallback branch
}
