// tRust test: every signed arithmetic edge case in one function
// VcKind: NegationOverflow, DivisionByZero, ArithmeticOverflow(Div), CastOverflow
// Expected: NegationOverflow FAILED, DivisionByZero FAILED,
//           ArithmeticOverflow(Div) FAILED, CastOverflow FAILED
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[allow(unused_variables)]
fn signed_chaos(x: i32, y: i32) -> i8 {
    let neg = -x;           // BUG 1: NegationOverflow when x == i32::MIN
    let div = x / y;        // BUG 2: DivisionByZero when y == 0
                             //        ArithmeticOverflow(Div) when x == i32::MIN, y == -1
    let cast = div as i8;   // BUG 3: CastOverflow when div outside [-128, 127]
    cast
}

fn main() {
    println!("{}", signed_chaos(10, 3));
}
