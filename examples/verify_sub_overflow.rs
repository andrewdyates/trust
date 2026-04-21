// tRust test: unsigned subtraction underflow
// VcKind: ArithmeticOverflow { op: BinOp::Sub, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Sub) FAILED
// Counterexample: any pair where a < b (e.g., a = 0, b = 1)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn unsigned_subtract(a: u32, b: u32) -> u32 {
    a - b // BUG: underflows when a < b
}

fn main() {
    println!("{}", unsigned_subtract(5, 3));
}
