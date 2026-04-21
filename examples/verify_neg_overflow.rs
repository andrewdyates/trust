// tRust test: negation overflow (signed MIN)
// VcKind: NegationOverflow { ty: Ty::i32() }
// Expected: NegationOverflow FAILED
// Counterexample: x = i32::MIN (-2147483648)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn negate(x: i32) -> i32 {
    -x // BUG: overflows when x == i32::MIN (-(-2^31) > i32::MAX)
}

fn main() {
    println!("{}", negate(42));
}
