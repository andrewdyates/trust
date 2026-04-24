// tRust: Modified from run-crash to run-pass. Projecting to an extern type
// field at non-zero offset now uses the statically-computed layout offset
// instead of falling through to the DST path that panics.
// See rust-lang/rust#127336, tRust#919.
//@ run-pass
//@ ignore-backends: gcc
#![feature(extern_types)]

extern "C" {
    type Opaque;
}

struct Newtype(Opaque);

struct S {
    i: i32,
    j: i32,
    a: Newtype,
}

fn main() {
    let buf = [0i32; 4];

    let x: &Newtype = unsafe { &*(&buf as *const _ as *const Newtype) };
    // Projecting to the newtype works, because it is always at offset 0.
    let field = &x.0;
    // Avoid being eliminated by DSE.
    std::hint::black_box(field);

    let x: &S = unsafe { &*(&buf as *const _ as *const S) };
    // Accessing sized fields is perfectly fine, even at non-zero offsets.
    let field = &x.i;
    std::hint::black_box(field);
    let field = &x.j;
    std::hint::black_box(field);
    // tRust: This now correctly uses the static offset from the struct layout
    // to compute the pointer to the extern type field. No dynamic alignment
    // computation is needed because extern types have no runtime metadata.
    let field = &x.a;
    std::hint::black_box(field);
}
