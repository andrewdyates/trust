// tRust test: narrowing cast overflow
// VcKind: CastOverflow { from_ty: Ty::u32(), to_ty: Ty::Int { width: 8, signed: false } }
// Expected: CastOverflow FAILED
// Counterexample: any x > 255 for u32 -> u8
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn narrow(x: u32) -> u8 {
    x as u8 // BUG: silently truncates when x > 255
}

fn main() {
    println!("{}", narrow(100));
}
