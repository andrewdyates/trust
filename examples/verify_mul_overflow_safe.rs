// tRust test: integer multiplication -- safe variant
// VcKind: ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Mul) PROVED (absent -- saturating_mul prevents overflow)
// Safe pattern: saturating_mul caps at u32::MAX instead of overflowing
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn area_safe(width: u32, height: u32) -> u32 {
    width.saturating_mul(height) // SAFE: saturates at u32::MAX instead of overflow
}

fn main() {
    println!("{}", area_safe(100, 200));
    println!("{}", area_safe(u32::MAX, 2)); // saturates to u32::MAX
}
