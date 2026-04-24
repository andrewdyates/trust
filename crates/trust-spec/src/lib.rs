//! Stable no-op contract attributes for the initial tRust spec surface.

#![forbid(unsafe_code)]

use proc_macro::TokenStream;

fn passthrough(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// Marks a precondition contract while Wave 1A keeps the annotated item unchanged.
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

/// Marks a postcondition contract while Wave 1A keeps the annotated item unchanged.
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

/// Marks an invariant contract while Wave 1A keeps the annotated item unchanged.
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}
