// tRust test: float addition overflow to infinity
// VcKind: FloatOverflowToInfinity { op: BinOp::Add, operand_ty: Ty::Float { width: 64 } }
// Expected: FloatOverflowToInfinity(Add) FAILED
// Counterexample: a and b near f64::MAX
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_add(a: f64, b: f64) -> f64 {
    a + b // BUG: produces +Inf when a + b > f64::MAX
}

fn main() {
    println!("{}", float_add(1.0, 2.0));
}
