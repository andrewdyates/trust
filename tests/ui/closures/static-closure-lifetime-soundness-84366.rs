// tRust: Regression test for the full unsoundness from rust-lang#84366.
// This demonstrates the actual use-after-free that was possible before the fix.
// The closure `|| -> &'a str { "" }` is 'static, but its return type is not.
// Through a blanket impl of a trait with an associated type, the non-'static
// return type gets laundered into a 'static context, enabling use-after-free.

use std::fmt;

trait Trait {
    type Associated;
}

impl<R, F: Fn() -> R> Trait for F {
    type Associated = R;
}

fn static_transfers_to_associated<T: Trait + 'static>(
    _: &T,
    x: T::Associated,
) -> Box<dyn fmt::Display> {
    Box::new(x) //~ ERROR the associated type `<T as Trait>::Associated` may not live long enough
}

fn make_static_displayable<'a>(s: &'a str) -> Box<dyn fmt::Display> {
    let f = || -> &'a str { "" };
    static_transfers_to_associated(&f, s) //~ ERROR lifetime may not live long enough
}

fn main() {
    let d;
    {
        let x = "Hello World".to_string();
        d = make_static_displayable(&x);
    }
    println!("{}", d);
}
