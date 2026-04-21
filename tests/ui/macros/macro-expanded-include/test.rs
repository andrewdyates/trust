//@ needs-asm-support
//@ build-pass (FIXME(62277): could be check-pass?)
#![allow(unused)]


m!();
fn f() {
    n!();
}

fn main() {}
