// tRust test: array index out of bounds
// VcKind: IndexOutOfBounds
// Expected: IndexOutOfBounds FAILED
// Counterexample: any idx >= 10
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn lookup(arr: [u32; 10], idx: usize) -> u32 {
    arr[idx] // BUG: panics when idx >= 10
}

fn main() {
    let arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    println!("{}", lookup(arr, 5));
}
