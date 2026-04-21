// tRust test: unreachable code reached
// VcKind: Unreachable
// Expected: Unreachable FAILED
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn classify(x: u32) -> &'static str {
    match x {
        0 => "zero",
        1..=100 => "small",
        _ => unreachable!("value too large"), // BUG: reachable for x > 100
    }
}

fn main() {
    println!("{}", classify(50));
}
