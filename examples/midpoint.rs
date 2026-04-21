// examples/midpoint.rs — The golden test for tRust verification.
//
// This function contains a real bug: (a + b) can overflow for large values.
// tRust should detect this and provide a counterexample.
// The division by 2 is trivially safe (no division by zero).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn get_midpoint(a: usize, b: usize) -> usize {
    (a + b) / 2
}

fn main() {
    println!("{}", get_midpoint(3, 7));
}
