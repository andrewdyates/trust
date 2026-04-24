// tRust: Regression test for rust-lang#143047
// Const eval must not construct values of uninhabited types.
// Transmuting to an uninhabited type is immediate UB because
// uninhabited types have no valid values.

enum Void {}

const BAD: Void = unsafe { std::mem::transmute(()) };
//~^ ERROR: evaluation of constant value failed
//~| uninhabited type

fn main() {}
