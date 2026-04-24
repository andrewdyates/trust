// tRust: Regression test for rust-lang#49682
// References to #[thread_local] statics must not be held across yield points.
// After a coroutine is resumed on a different thread, such references would
// point to the wrong thread's data (or deallocated memory).
//
// compile-fail

#![feature(coroutines, coroutine_trait, thread_local)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[thread_local]
static TLS_VALUE: u32 = 42;

fn main() {
    let mut gen = #[coroutine] || {
        let r = &TLS_VALUE; //~ ERROR reference to thread-local static held across yield point
        yield;
        let _ = *r;
    };
}
