// tRust test: narrowing cast overflow -- safe variant
// VcKind: CastOverflow { from_ty: Ty::u32(), to_ty: Ty::Int { width: 8, signed: false } }
// Expected: CastOverflow PROVED (absent -- guard prevents truncation)
// Safe pattern: if-guard `x <= 255` ensures value fits in u8 range
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn narrow_safe(x: u32) -> u8 {
    if x <= 255 {
        x as u8 // SAFE: guard ensures x fits in u8 range
    } else {
        u8::MAX // fallback: clamp to max u8 value
    }
}

fn main() {
    println!("{}", narrow_safe(100));
    println!("{}", narrow_safe(1000)); // takes fallback branch
}
