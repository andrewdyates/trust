// tRust test: slice access on potentially empty slice
// VcKind: SliceBoundsCheck
// Expected: SliceBoundsCheck FAILED (or IndexOutOfBounds)
// Counterexample: data with len == 0
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn first(data: &[u32]) -> u32 {
    data[0] // BUG: panics when data is empty
}

fn main() {
    println!("{}", first(&[1, 2, 3]));
}
