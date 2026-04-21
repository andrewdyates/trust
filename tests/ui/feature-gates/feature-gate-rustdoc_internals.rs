#[doc(keyword = "match")] //~ ERROR: `#[doc(keyword)]` is meant for 
/// wonderful
mod foo {}

#[doc(attribute = "repr")] //~ ERROR: `#[doc(attribute)]` is meant for 
/// wonderful
mod foo2 {}

trait Mine {}

#[doc(fake_variadic)]  //~ ERROR: `#[doc(fake_variadic)]` is meant for 
impl<T> Mine for (T,) {}

#[doc(search_unbox)]  //~ ERROR: `#[doc(search_unbox)]` is meant for 
struct Wrap<T> (T);

fn main() {}
