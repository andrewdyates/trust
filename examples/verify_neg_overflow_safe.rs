// tRust test: negation overflow (signed MIN) -- safe variant
// VcKind: NegationOverflow { ty: Ty::i32() }
// Expected: NegationOverflow PROVED (absent -- guard prevents MIN negation)
// Safe pattern: if-guard `x == i32::MIN` avoids negating the un-negatable value
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn negate_safe(x: i32) -> i32 {
    if x == i32::MIN {
        i32::MAX // fallback: closest representable value to -i32::MIN
    } else {
        -x // SAFE: guard ensures x != i32::MIN
    }
}

fn main() {
    println!("{}", negate_safe(42));
    println!("{}", negate_safe(i32::MIN)); // takes fallback branch
}
