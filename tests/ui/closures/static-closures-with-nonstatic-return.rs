// tRust: Fixed regression test for rust-lang#84366 (closure lifetime unsoundness).
// Previously marked check-pass / known-bug. Now correctly rejected.
//
// A closure `|| -> &'a str` is 'static itself (no captures), but its
// associated output type `&'a str` is NOT 'static. The compiler must not
// allow treating associated types of 'static types as 'static when the
// closure's signature references non-'static lifetimes.

#[allow(dead_code)]
fn foo<'a>() {
    let closure = || -> &'a str { "" };
    assert_static(closure);
    //~^ ERROR the associated type `<{closure@
}

fn assert_static<T: 'static>(_: T) {}

fn main() {}
