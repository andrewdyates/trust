//@ ignore-backends: gcc


fn main() {
    let _: usize = unclosed_delim_mod::new();
}

//~? ERROR mismatched closing delimiter: `}`
