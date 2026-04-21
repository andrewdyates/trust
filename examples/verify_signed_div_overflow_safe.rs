// tRust test: signed division overflow -- safe variant
// VcKind: DivisionByZero AND ArithmeticOverflow { op: BinOp::Div }
// Expected: DivisionByZero PROVED AND ArithmeticOverflow(Div) PROVED
//           (absent -- guard prevents both zero divisor and MIN/-1 overflow)
// Safe pattern: if-guard checks both y == 0 and (x == i32::MIN && y == -1)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn signed_divide_safe(x: i32, y: i32) -> i32 {
    if y == 0 || (x == i32::MIN && y == -1) {
        0 // fallback for div-by-zero or overflow
    } else {
        x / y // SAFE: guard prevents both failure modes
    }
}

fn main() {
    println!("{}", signed_divide_safe(10, 3));
    println!("{}", signed_divide_safe(10, 0)); // div-by-zero fallback
    println!("{}", signed_divide_safe(i32::MIN, -1)); // overflow fallback
}
