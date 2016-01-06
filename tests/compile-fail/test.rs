// error-pattern:error: `s` does not live long enough
#[macro_use]
extern crate any_ref;

use any_ref::*;

fn main() {
    let x = {
        let s = String::from("asd");
        let mut opt = Some(&s[..]);
        let borrow = &mut &mut opt as &mut AnyRef;
        assert!(borrow.is::<&mut Option<&str>>());
        assert!(!borrow.is::<&mut Option<&i32>>());
        borrow.downcast_ref::<&mut Option<&str>>().unwrap().unwrap()
    };
    assert_eq!(x, "asd");
}
