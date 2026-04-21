// tRust test: remainder by zero
// VcKind: RemainderByZero
// Expected: RemainderByZero FAILED
// Counterexample: y = 0
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn modulo(x: u32, y: u32) -> u32 {
    x % y // BUG: panics when y == 0
}

fn main() {
    println!("{}", modulo(10, 3));
}
