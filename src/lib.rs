use std::mem;
use std::any::{Any, TypeId};

/// Trait which provides TypeId for types which are not static.
///
/// To be safe this trait requires that `Static` is the same type as `Self` but with the lifetimes
/// replaced with 'static
pub unsafe trait Type<'a> {
    /// Type which should be the same as `Self` but with the static lifetime
    type Static: Any;
}

/// Returns the `TypeId` for `T::Static`
pub fn type_id<'a, T>() -> TypeId
    where T: Type<'a>
{
    TypeId::of::<T::Static>()
}

/// `Any` for types containing borrows.
///
/// Safe(?) if implemented using the provided any_ref macro
///
/// ```
/// #[macro_use]
/// extern crate any_ref;
///
/// struct MyType<T, U>(T, U);
/// any_ref!(MyType<T, U>);
///
/// struct MyRef<'a, T: 'a, U>(&'a T, U);
/// any_ref!(MyRef<'a, T, U>);
///
/// # fn main() {
/// # }
/// ```
pub unsafe trait AnyRef<'a> {
    /// Converts `&self` to `&Any`
    ///
    /// Unsafe as the lifetime of any interior references are forgotten
    unsafe fn as_any_ref(&self) -> &Any;

    /// Converts `&mut self` to `&mut Any`
    ///
    /// Unsafe as the lifetime of any interior references are forgotten
    unsafe fn as_any_mut(&mut self) -> &mut Any;
    /// Converts `Box<Self>` to `Box<Any>`
    ///
    /// Unsafe as the lifetime of any interior references are forgotten
    unsafe fn as_any_box(self: Box<Self>) -> Box<Any>;
}

#[macro_export]
macro_rules! any_ref_inner {
    () => {
        unsafe fn as_any_ref(&self) -> &::std::any::Any {
            ::std::mem::transmute::<&Self, &<Self as $crate::Type<'a>>::Static>(self)
        }
        unsafe fn as_any_mut(&mut self) -> &mut ::std::any::Any {
            ::std::mem::transmute::<&mut Self,
                                    &mut <Self as $crate::Type<'a>>::Static>(self)
        }
        unsafe fn as_any_box(self: Box<Self>) -> Box<::std::any::Any> {
            ::std::mem::transmute::<Box<Self>,
                                    Box<<Self as $crate::Type<'a>>::Static>>(self)
        }
    };
}

#[macro_export]
macro_rules! any_ref {
    ($t: ident) => {
        unsafe impl <'a> Type<'a> for $t
        {
            type Static = $t;
        }
        unsafe impl <'a> AnyRef<'a> for $t
        {
            any_ref_inner!();
        }
    };
    ($t: ident<'a $(, $arg: ident)*>) => {
        unsafe impl <'a $(, $arg)*> $crate::Type<'a> for $t<'a $(, $arg)*>
            where $($arg: $crate::Type<'a>, $arg::Static: Sized),*
        {
            type Static = $t<'static $(, $arg::Static)*>;
        }
        unsafe impl <'a $(, $arg)*> $crate::AnyRef<'a> for $t<'a $(, $arg)*>
            where $($arg: $crate::Type<'a>, $arg::Static: Sized),*
        {
            any_ref_inner!();
        }
    };
    ($t: ident<$($arg: ident),+>) => {
        unsafe impl <'a $(, $arg)*> $crate::Type<'a> for $t<$($arg),*>
            where $($arg: $crate::Type<'a>, $arg::Static: Sized),*
        {
            type Static = $t<$($arg::Static),*>;
        }
        unsafe impl <'a $(, $arg)*> $crate::AnyRef<'a> for $t<$($arg),*>
            where $($arg: $crate::Type<'a>, $arg::Static: Sized),*
        {
            any_ref_inner!();
        }
    }
}
macro_rules! any_refs {
    ($($t: ident<$($arg: ident),+>),+) => {
        $(
            any_ref!($t<$($arg),+>);
        )*
    };
    ($($t: ident)+) => {
        $(
            any_ref!($t);
        )*
    };
}

use std::cell::{Cell, RefCell, Ref, RefMut, UnsafeCell};
use std::sync::Arc;
use std::rc::Rc;

any_refs!(Box<T>, Rc<T>, Arc<T>, Vec<T>, Option<T>, Result<T, R>, Cell<T>, RefCell<T>,
             UnsafeCell<T>);
any_ref!(Ref<'a, T>);
any_ref!(RefMut<'a, T>);

use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};

any_refs!(BTreeMap<K, V>, BTreeSet<T>, BinaryHeap<T>, HashMap<K, V>, HashSet<T>,
             LinkedList<T>, VecDeque<T>);

any_refs!(i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 String char);

unsafe impl<'a> Type<'a> for &'a str {
    type Static = &'static str;
}
unsafe impl<'a> AnyRef<'a> for &'a str {
    any_ref_inner!();
}

unsafe impl<'a> Type<'a> for &'a mut str {
    type Static = &'static mut str;
}
unsafe impl<'a> AnyRef<'a> for &'a mut str {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a [T] {
    type Static = &'static [T::Static];
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a [T] {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a mut [T] {
    type Static = &'static mut T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a mut [T] {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a T {
    type Static = &'static T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a T {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a mut T {
    type Static = &'static mut T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a mut T {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for *const T {
    type Static = *const T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for *const T {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for *mut T {
    type Static = *mut T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for *mut T {
    any_ref_inner!();
}

impl<'a: 'b, 'b> AnyRef<'a> + 'b {
    pub fn is<T>(&self) -> bool
        where T: AnyRef<'a> + Type<'a>
    {
        unsafe { self.as_any_ref().is::<T::Static>() }
    }
    pub fn downcast_ref<T>(&self) -> Option<&T>
        where T: AnyRef<'a> + Type<'a>
    {
        unsafe {
            self.as_any_ref()
                .downcast_ref::<T::Static>()
                .map(|x| mem::transmute(x))
        }
    }
    pub fn downcast_mut<T>(&mut self) -> Option<&mut T>
        where T: AnyRef<'a> + Type<'a>
    {
        unsafe {
            self.as_any_mut()
                .downcast_mut::<T::Static>()
                .map(|x| mem::transmute(x))
        }
    }
}

pub fn downcast_box<'a: 'b, 'b, T>(b: Box<AnyRef<'a> + 'b>) -> Result<Box<T>, Box<AnyRef<'a> + 'b>>
    where T: AnyRef<'a> + Type<'a>
{
    unsafe {
        if b.is::<T>() {
            Ok(mem::transmute(b.as_any_box().downcast::<T::Static>().ok().unwrap()))
        } else {
            Err(b)
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn downcast() {
        let ref x = 1;
        assert!((x as &AnyRef).is::<i32>());
        assert!((&x as &AnyRef).is::<&i32>());
        assert!(!(&x as &AnyRef).is::<Cell<&i32>>());

        let s = "";
        let cell = Cell::new(&s);
        assert!((&&cell as &AnyRef).is::<&Cell<&&str>>());
        assert_eq!((&&cell as &AnyRef).downcast_ref::<&Cell<&&str>>(),
                   Some(&&cell));
        assert!((&mut &cell as &mut AnyRef).downcast_mut::<&Cell<&&str>>().is_some());

        assert!(!(&&cell as &AnyRef).is::<&Cell<&str>>());
        assert!(!(&&cell as &AnyRef).is::<Cell<&str>>());
        assert!((&cell as &AnyRef).is::<Cell<&&str>>());

        let s = String::from("asd");
        let mut opt = Some(&s[..]);
        let borrow = &mut &mut opt as &mut AnyRef;
        assert!(borrow.is::<&mut Option<&str>>());
        assert!(!borrow.is::<&mut Option<&i32>>());
        let x = borrow.downcast_ref::<&mut Option<&str>>().unwrap().unwrap();
        assert_eq!(x, "asd");
    }

    #[test]
    fn boxed() {
        let x = 123;
        let b: Box<AnyRef> = Box::new(vec![&x]);
        let result = downcast_box::<&i32>(b);
        assert!(result.is_err());
        assert_eq!(downcast_box::<Vec<&i32>>(result.err().unwrap()).ok(),
                   Some(Box::new(vec![&x])));
    }
}
