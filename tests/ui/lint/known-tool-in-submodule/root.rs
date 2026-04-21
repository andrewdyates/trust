//@ check-pass

#![feature(register_tool)]
#![register_tool(tool)]


fn main() {
    submodule::foo();
}
