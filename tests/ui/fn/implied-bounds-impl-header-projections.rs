// tRust: fixed soundness bug rust-lang#100051 (Part of #859)
// Implied bounds from projections in impl headers must not create improper
// lifetime relationships. The projection `<&'b &'a () as Trait>::Type`
// normalizes to `()`, so WF of `&'b &'a ()` (which requires 'a: 'b) must
// NOT be assumed as an implied bound.

trait Trait {
    type Type;
}

impl<T> Trait for T {
    type Type = ();
}

trait Extend<'a, 'b> {
    fn extend(self, s: &'a str) -> &'b str;
}

impl<'a, 'b> Extend<'a, 'b> for <&'b &'a () as Trait>::Type
where
    for<'what, 'ever> &'what &'ever (): Trait,
{
    fn extend(self, s: &'a str) -> &'b str {
        s //~ ERROR lifetime may not live long enough
    }
}

fn main() {
    let y = <() as Extend<'_, '_>>::extend((), &String::from("Hello World"));
    println!("{}", y);
}
