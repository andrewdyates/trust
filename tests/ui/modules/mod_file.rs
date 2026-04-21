//@ run-pass

// Testing that a plain .rs file can load modules from other source files


pub fn main() {
    assert_eq!(mod_file_aux::foo(), 10);
}
