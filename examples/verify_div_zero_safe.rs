// tRust test: division by zero -- safe variant
// VcKind: DivisionByZero
// Expected: DivisionByZero PROVED (absent -- guard prevents zero divisor)
// Safe pattern: if-guard `y == 0` returns fallback before division
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn divide_safe(x: u32, y: u32) -> u32 {
    if y == 0 {
        0 // fallback for zero divisor
    } else {
        x / y // SAFE: guard ensures y != 0
    }
}

fn main() {
    println!("{}", divide_safe(10, 2));
    println!("{}", divide_safe(10, 0)); // takes fallback branch
}
