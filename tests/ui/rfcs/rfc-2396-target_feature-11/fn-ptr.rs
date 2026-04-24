//@ only-x86_64

#[target_feature(enable = "avx")]
fn foo_avx() {}

#[target_feature(enable = "sse2")]
fn foo() {}

#[target_feature(enable = "sse2")]
fn bar() {
    // tRust: #861 — coercion to safe fn ptr is now ALWAYS rejected, even when
    // the caller has the necessary features, because the pointer can escape.
    let foo: fn() = foo; //~ ERROR mismatched types
    let foo: fn() = foo_avx; //~ ERROR mismatched types
}

fn main() {
    if std::is_x86_feature_detected!("sse2") {
        unsafe {
            bar();
        }
    }
    let foo: fn() = foo; //~ ERROR mismatched types
}
