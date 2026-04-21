// tRust test: signed division overflow (i32::MIN / -1)
// VcKind: DivisionByZero AND ArithmeticOverflow { op: BinOp::Div }
// Expected: DivisionByZero FAILED AND ArithmeticOverflow(Div) FAILED
// Counterexample: x = i32::MIN, y = -1 for overflow; y = 0 for div-by-zero
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn signed_divide(x: i32, y: i32) -> i32 {
    x / y // BUG: panics when y == 0; overflows when x == i32::MIN and y == -1
}

fn main() {
    println!("{}", signed_divide(10, 3));
}
