// tRust test: slice access on potentially empty slice -- safe variant
// VcKind: SliceBoundsCheck
// Expected: SliceBoundsCheck PROVED (absent -- guard prevents empty-slice access)
// Safe pattern: if-guard `data.is_empty()` avoids accessing data[0] on empty slice
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn first_safe(data: &[u32]) -> u32 {
    if data.is_empty() {
        0 // fallback for empty slice
    } else {
        data[0] // SAFE: guard ensures data has at least one element
    }
}

fn main() {
    println!("{}", first_safe(&[1, 2, 3]));
    println!("{}", first_safe(&[])); // takes fallback branch
}
