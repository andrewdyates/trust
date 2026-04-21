// tRust test: float division by zero (produces Inf per IEEE 754)
// VcKind: FloatDivisionByZero
// Expected: FloatDivisionByZero FAILED
// Counterexample: y = 0.0
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_divide(x: f64, y: f64) -> f64 {
    x / y // BUG: produces +/-Inf when y == 0.0
}

fn main() {
    println!("{}", float_divide(10.0, 3.0));
}
