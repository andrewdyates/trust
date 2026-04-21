//@ edition: 2021

#![feature(proc_macro_span)]
#![deny(dead_code)] // catch if a test function is never called

extern crate proc_macro;


use proc_macro::TokenStream;

#[proc_macro]
pub fn run(input: TokenStream) -> TokenStream {
    assert!(input.is_empty());

    cmp::test();
    ident::test();
    literal::test();
    tokenstream::test();

    TokenStream::new()
}
