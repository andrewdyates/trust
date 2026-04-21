// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 5

#![feature(no_core)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use mini_core::*;

static mut TWO: usize = 2;

fn index_slice(s: &[u32]) -> u32 {
    // SAFETY: `TWO` (value 2) is within bounds for the slice `s` which has 4 elements.
    unsafe { s[TWO] }
}

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let array = [42, 7, 5];
    // SAFETY: the raw pointer is valid and properly aligned; the referenced data has the correct type.
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, index_slice(&array));
    }
    0
}
