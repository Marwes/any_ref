# any_ref

Rust library which implements a version of the [Any][] trait for types which contains borrows.

# WARNING
This crate contains unsafe code which has not been properly vetted so this crate may not be safe to use.

# Usage
```
#[macro_use]
extern crate any_ref;
use any_ref::AnyRef;

struct MyWrapper(i32);
any_ref!(MyWrapper);

# #[allow(dead_code)]
struct MyType<T, U>(T, U);
any_ref!(MyType<T, U>);

struct MyRef<'a, T: 'a, U>(&'a T, U);
any_ref!(MyRef<'a, T, U>);

fn main() {
    let x = MyWrapper(1);
    assert!((&x as &AnyRef).is::<MyWrapper>());
    assert!(!(&x as &AnyRef).is::<i32>());
    let r = MyRef(&x, ());
    let ar = &r as &AnyRef;
    assert!(ar.is::<MyRef<MyWrapper, ()>>());
    assert!(ar.downcast_ref::<MyRef<MyWrapper, ()>>().is_some());

    // Would be a compile error
    // assert!((&r as &AnyRef).is::<MyRef<'static, MyWrapper, ()>>());
}
```

[Documentation](https://marwes.github.io/any_ref/any_ref/index.html)

[Any]:http://doc.rust-lang.org/std/any/trait.Any.html
