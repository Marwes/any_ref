use std::mem;
use std::any::{Any, TypeId};

/// Trait which provides TypeId for types which are not static.
///
/// To be safe this trait requires that `Static` is the same type as `Self` but with the lifetimes
/// replaced with 'static
pub unsafe trait Type<'a> {
    /// Type which should be the same as `Self` but with the static lifetime
    type Static: ?Sized + 'static;
}

/// Returns the `TypeId` for `T::Static`
pub fn type_id<'a, T>() -> TypeId
    where T: Type<'a>, T::Static: Any
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
/// struct MyWrapper(i32);
/// any_ref!(MyWrapper);
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
            use std::mem::{size_of, transmute_copy};
            assert!(size_of::<&Self>() == size_of::<&<Self as $crate::Type<'a>>::Static>());
            transmute_copy::<&Self, &<Self as $crate::Type<'a>>::Static>(&self)
        }
        unsafe fn as_any_mut(&mut self) -> &mut ::std::any::Any {
            use std::mem::{size_of, transmute_copy};
            assert!(size_of::<&mut Self>() == size_of::<&mut <Self as $crate::Type<'a>>::Static>());
            transmute_copy::<&mut Self, &mut <Self as $crate::Type<'a>>::Static>(&self)
        }
        unsafe fn as_any_box(self: Box<Self>) -> Box<::std::any::Any> {
            use std::mem::{forget, size_of, transmute_copy};
            assert!(size_of::<Box<Self>>() == size_of::<Box<<Self as $crate::Type<'a>>::Static>>());
            let b = transmute_copy::<Box<Self>, Box<<Self as $crate::Type<'a>>::Static>>(&self);
            forget(self);
            b
        }
    };
}
macro_rules! any_ref_tuple {
    () => { };
    ($head: ident $($tail: ident)*) => {
        any_ref_tuple!($($tail)*);

        unsafe impl <'a, $head $(, $tail)*> $crate::Type<'a> for ($head, $($tail),*)
            where $head: Type<'a>, $head::Static: Sized,
                  $($tail: $crate::Type<'a>, $tail::Static: Sized),*
        {
            type Static = ($head::Static, $($tail::Static),*);
        }
        unsafe impl <'a, $head $(, $tail)*> $crate::AnyRef<'a> for ($head, $($tail),*)
            where $head: Type<'a>, $head::Static: Sized + ::std::any::Any,
                  $($tail: $crate::Type<'a>, $tail::Static: Sized + ::std::any::Any),*
        {
            any_ref_inner!();
        }
    }
}

unsafe impl <'a> Type<'a> for ()
{
    type Static = ();
}
unsafe impl <'a> AnyRef<'a> for ()
{
    any_ref_inner!();
}
any_ref_tuple!(A B C D E F G H I J K L);

#[macro_export]
macro_rules! any_ref {
    ($t: ident) => {
        unsafe impl <'a> $crate::Type<'a> for $t
        {
            type Static = $t;
        }
        unsafe impl <'a> $crate::AnyRef<'a> for $t
        {
            any_ref_inner!();
        }
    };
    ($t: ident<'a>) => {
        unsafe impl <'a> $crate::Type<'a> for $t<'a>
        {
            type Static = $t<'static>;
        }
        unsafe impl <'a> $crate::AnyRef<'a> for $t<'a>
        {
            any_ref_inner!();
        }
    };
    ($t: ident<'a $(, $arg: ident)+>) => {
        unsafe impl <'a $(, $arg)+> $crate::Type<'a> for $t<'a $(, $arg)+>
            where $($arg: $crate::Type<'a>, $arg::Static: Sized),+
        {
            type Static = $t<'static $(, $arg::Static)+>;
        }
        unsafe impl <'a $(, $arg)+> $crate::AnyRef<'a> for $t<'a $(, $arg)+>
            where $($arg: $crate::Type<'a>, $arg::Static: Sized + ::std::any::Any),+
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
            where $($arg: $crate::Type<'a>, $arg::Static: Sized + ::std::any::Any),*
        {
            any_ref_inner!();
        }
    }
}

macro_rules! unsized_any_ref {
    ($t: ident<T>) => {
        unsafe impl <'a, T: ?Sized> $crate::Type<'a> for $t<T>
            where T: $crate::Type<'a>
        {
            type Static = $t<T::Static>;
        }
        unsafe impl <'a, T: ?Sized> $crate::AnyRef<'a> for $t<T>
            where T: $crate::Type<'a>, T::Static: Sized + ::std::any::Any
        {
            any_ref_inner!();
        }
    };
    ($t: ident<'a, T>) => {
        unsafe impl <'a, T: ?Sized> $crate::Type<'a> for $t<'a, T>
            where T: $crate::Type<'a>
        {
            type Static = $t<'static, T::Static>;
        }
        unsafe impl <'a, T: ?Sized> $crate::AnyRef<'a> for $t<'a, T>
            where T: $crate::Type<'a>, T::Static: Sized + ::std::any::Any
        {
            any_ref_inner!();
        }
    };
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

unsized_any_ref!(Box<T>);
unsized_any_ref!(Rc<T>);
unsized_any_ref!(Arc<T>);
unsized_any_ref!(RefCell<T>);
unsized_any_ref!(UnsafeCell<T>);
unsized_any_ref!(Ref<'a, T>);
unsized_any_ref!(RefMut<'a, T>);

any_refs!(Vec<T>, Option<T>, Result<T, R>, Cell<T>);

use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};

any_refs!(BTreeMap<K, V>, BTreeSet<T>, BinaryHeap<T>, HashMap<K, V>, HashSet<T>,
             LinkedList<T>, VecDeque<T>);

any_refs!(i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 String char Any);

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

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a [T]
    where T::Static: Sized {
    type Static = &'static [T::Static];
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a [T]
    where T::Static: Sized + Any {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a mut [T]
    where T::Static: Sized {
    type Static = &'static mut T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a mut [T]
    where T::Static: Sized + Any {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a T {
    type Static = &'static T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a T
    where T::Static: Sized + Any {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for &'a mut T {
    type Static = &'static mut T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for &'a mut T
    where T::Static: Sized + Any {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for *const T {
    type Static = *const T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for *const T
    where T::Static: Sized + Any {
    any_ref_inner!();
}

unsafe impl<'a, T: Type<'a>> Type<'a> for *mut T {
    type Static = *mut T::Static;
}
unsafe impl<'a, T: Type<'a>> AnyRef<'a> for *mut T
    where T::Static: Sized + Any {
    any_ref_inner!();
}

impl<'a: 'b, 'b> AnyRef<'a> + 'b {
    pub fn is<T>(&self) -> bool
        where T: AnyRef<'a> + Type<'a>,
              T::Static: Sized + Any
    {
        unsafe { self.as_any_ref().is::<T::Static>() }
    }
    pub fn downcast_ref<T>(&self) -> Option<&T>
        where T: AnyRef<'a> + Type<'a>,
              T::Static: Sized + Any
    {
        unsafe {
            self.as_any_ref()
                .downcast_ref::<T::Static>()
                .map(|x| mem::transmute_copy::<&T::Static, &T>(&x))
        }
    }
    pub fn downcast_mut<T>(&mut self) -> Option<&mut T>
        where T: AnyRef<'a> + Type<'a>,
              T::Static: Sized + Any
    {
        unsafe {
            self.as_any_mut()
                .downcast_mut::<T::Static>()
                .map(|x| mem::transmute_copy::<&mut T::Static, &mut T>(&x))
        }
    }
}

pub fn downcast_box<'a: 'b, 'b, T>(b: Box<AnyRef<'a> + 'b>) -> Result<Box<T>, Box<AnyRef<'a> + 'b>>
    where T: AnyRef<'a> + Type<'a>,
          T::Static: Sized + Any
{
    unsafe {
        if b.is::<T>() {
            use std::mem::size_of;
            let b = b.as_any_box().downcast::<T::Static>().ok().unwrap();
            assert!(size_of::<Box<T::Static>>() == size_of::<Box<T>>());
            let result = mem::transmute_copy::<Box<T::Static>, Box<T>>(&b);
            mem::forget(b);
            Ok(result)
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

    struct OnlyRef<'a>(&'a ());
    any_ref!(OnlyRef<'a>);

    #[test]
    fn only_ref() {
        assert!((&OnlyRef(&()) as &AnyRef).is::<OnlyRef>());
    }
}
