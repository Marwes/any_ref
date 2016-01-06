// error-pattern:error: `x` does not live long enough
#[macro_use]
extern crate any_ref;

use any_ref::*;

fn main() {
    let x = 0;
    (& &x as &AnyRef).downcast_ref::<&'static i32>();
}
