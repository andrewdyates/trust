// tRust test: left shift overflow -- safe variant
// VcKind: ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() }
// Expected: ShiftOverflow(Shl) PROVED (absent -- guard prevents invalid shift)
// Safe pattern: if-guard `shift < 32` ensures shift within bit width of u32
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn shift_left_safe(x: u32, shift: u32) -> u32 {
    if shift < 32 {
        x << shift // SAFE: guard ensures shift < bit width
    } else {
        0 // fallback for invalid shift amount
    }
}

fn main() {
    println!("{}", shift_left_safe(1, 4));
    println!("{}", shift_left_safe(1, 40)); // takes fallback branch
}
