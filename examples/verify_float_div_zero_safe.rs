// tRust test: float division by zero -- safe variant
// VcKind: FloatDivisionByZero
// Expected: FloatDivisionByZero PROVED (absent -- guard prevents zero divisor)
// Safe pattern: if-guard `y == 0.0` returns fallback before division
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_divide_safe(x: f64, y: f64) -> f64 {
    if y == 0.0 {
        0.0 // fallback for zero divisor (avoids +/-Inf)
    } else {
        x / y // SAFE: guard ensures y != 0.0
    }
}

fn main() {
    println!("{}", float_divide_safe(10.0, 3.0));
    println!("{}", float_divide_safe(10.0, 0.0)); // takes fallback branch
}
