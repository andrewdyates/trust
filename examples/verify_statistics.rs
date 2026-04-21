// tRust test: multiple bug types in a realistic function
// VcKind: DivisionByZero, ArithmeticOverflow(Add), IndexOutOfBounds
// Expected: DivisionByZero FAILED, ArithmeticOverflow(Add) FAILED, IndexOutOfBounds FAILED
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn mean(data: &[u32]) -> u32 {
    let mut sum: u32 = 0;
    let mut i: usize = 0;
    while i < data.len() + 1 {   // BUG 1: off-by-one, IndexOutOfBounds at data[data.len()]
        sum = sum + data[i];      // BUG 2: ArithmeticOverflow if sum exceeds u32::MAX
        i += 1;
    }
    sum / data.len() as u32       // BUG 3: DivisionByZero when data is empty
}

fn main() {
    println!("{}", mean(&[1, 2, 3, 4, 5]));
}
