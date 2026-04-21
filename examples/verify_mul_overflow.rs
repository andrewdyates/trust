// tRust test: integer multiplication overflow
// VcKind: ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Mul) FAILED
// Counterexample: any pair where width * height > u32::MAX
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn area(width: u32, height: u32) -> u32 {
    width * height // BUG: overflows for large dimensions
}

fn main() {
    println!("{}", area(100, 200));
}
