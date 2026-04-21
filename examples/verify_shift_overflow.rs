// tRust test: left shift overflow
// VcKind: ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() }
// Expected: ShiftOverflow(Shl) FAILED
// Counterexample: any shift >= 32 for u32
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn shift_left(x: u32, shift: u32) -> u32 {
    x << shift // BUG: panics in debug mode / wraps in release when shift >= 32
}

fn main() {
    println!("{}", shift_left(1, 4));
}
