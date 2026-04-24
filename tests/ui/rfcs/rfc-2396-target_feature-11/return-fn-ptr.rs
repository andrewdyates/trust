// tRust: #861 — Updated to use unsafe fn pointer. Coercion of #[target_feature]
// functions to safe fn pointers is now always rejected (soundness fix).

//@ only-x86_64
//@ run-pass

#[target_feature(enable = "sse2")]
fn foo() -> bool {
    true
}

#[target_feature(enable = "sse2")]
fn bar() -> unsafe fn() -> bool {
    foo
}

fn main() {
    if !std::is_x86_feature_detected!("sse2") {
        return;
    }
    let f = unsafe { bar() };
    assert!(unsafe { f() });
}
