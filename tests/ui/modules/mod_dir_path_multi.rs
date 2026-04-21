//@ run-pass

#[path = "mod_dir_simple"]
mod biscuits {
}

#[path = "mod_dir_simple"]
mod gravy {
}

pub fn main() {
    assert_eq!(biscuits::test::foo(), 10);
    assert_eq!(gravy::test::foo(), 10);
}
