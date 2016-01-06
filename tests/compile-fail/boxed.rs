// error-pattern:error: `x` does not live long enough
#[macro_use]
extern crate any_ref;

use any_ref::*;

fn main() {
    let x = 123;
    let b: Box<AnyRef> = Box::new(vec![&x]);
    downcast_box::<Vec<&'static i32>>(b).ok();
}
