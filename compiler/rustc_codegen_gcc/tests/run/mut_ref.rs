// Compiler:
//
// Run-time:
//   stdout: 2
//     7
//     6
//     11

#![feature(no_core)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use mini_core::*;

struct Test {
    field: isize,
}

fn test(num: isize) -> Test {
    Test { field: num + 1 }
}

fn update_num(num: &mut isize) {
    *num = *num + 5;
}

#[no_mangle]
extern "C" fn main(mut argc: isize, _argv: *const *const u8) -> i32 {
    let mut test = test(argc);
    // SAFETY: the raw pointer is valid and properly aligned; the referenced data has the correct type.
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, test.field);
    }
    update_num(&mut test.field);
    // SAFETY: the raw pointer is valid and properly aligned; the referenced data has the correct type.
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, test.field);
    }

    update_num(&mut argc);
    // SAFETY: the raw pointer is valid and properly aligned; the referenced data has the correct type.
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, argc);
    }

    let refe = &mut argc;
    *refe = *refe + 5;
    // SAFETY: the raw pointer is valid and properly aligned; the referenced data has the correct type.
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, argc);
    }

    0
}
