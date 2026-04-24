// tRust: Regression test for rust-lang#134225
// #[alloc_error_handler] must not be an unsafe function because the runtime
// calls it as safe — an unsafe fn has preconditions the runtime cannot verify.
//
// compile-fail

#![feature(alloc_error_handler)]
#![no_std]

use core::alloc::Layout;

#[alloc_error_handler]
unsafe fn my_handler(_layout: Layout) -> ! { //~ ERROR must not be unsafe
    loop {}
}
