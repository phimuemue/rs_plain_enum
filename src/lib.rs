#![allow(clippy::missing_safety_doc)] // TODO fix this
//! This crate offers some tools to deal with static enums. It offers a way to declare a simple
//! enum, which then offers e.g. `values()` which can be used to iterate over the values of the enum.
//! In addition, it offers a type `EnumMap` which is an array-backed map from enum values to some type.
//!
//! It offers a macro `plain_enum_mod` which declares an own module which contains a simple enum
//! and the associated functionality:
//!
//! ```
//! mod examples_not_to_be_used_by_clients {
//!     #[macro_use]
//!     use plain_enum::*;
//!     plain_enum_mod!{example_mod_name, ExampleEnum {
//!         V1,
//!         V2,
//!         SomeOtherValue,
//!         LastValue, // note trailing comma
//!     }}
//!     
//!     fn do_some_stuff() {
//!         let map = ExampleEnum::map_from_fn(|example| // create a map from ExampleEnum to usize
//!             example.to_usize() + 1                   // enum values convertible to usize
//!         );
//!         for ex in ExampleEnum::values() {            // iterating over the enum's values
//!             assert_eq!(map[ex], ex.to_usize() + 1);
//!         }
//!     }
//! }
//! ```
//!
//! Internally, the macro generates a simple enum whose numeric values start counting at 0.

#![recursion_limit="256"] // my tests indicate that 139 would be enough but I do not know how if that is enough in foreign code, so I chose the limit suggested by rustc

#[macro_export]
macro_rules! enum_seq_len {
    () => (0);
    ($($enumval_0: tt, $enumval_1: tt,)*) => (2*($crate::enum_seq_len!($($enumval_0,)*)));
    ($enumval: tt, $($enumval_0: tt, $enumval_1: tt,)*) => (1+2*($crate::enum_seq_len!($($enumval_0,)*)));
}

#[macro_use]
mod plain_enum {
    pub trait TArrayExt {
        type Item;
        fn from_fn(f: impl FnMut(usize)->Self::Item) -> Self;
        type MappedType<U>: TArrayExt<Item=U>;
        fn map<U>(self, f: impl FnMut(Self::Item)->U) -> Self::MappedType<U>;

        unsafe fn index(&self, e: usize) -> &Self::Item;
        unsafe fn index_mut(&mut self, e: usize) -> &mut Self::Item;
        fn iter(&self) -> slice::Iter<'_, Self::Item>;
        fn iter_mut(&mut self) -> slice::IterMut<'_, Self::Item>;
    }
    impl<T, const N: usize> TArrayExt for [T; N] {
        type Item = T;
        fn from_fn(f: impl FnMut(usize)->Self::Item) -> Self {
            std::array::from_fn(f)
        }
        type MappedType<U> = [U; N];
        fn map<U>(self, f: impl FnMut(Self::Item)->U) -> Self::MappedType<U> {
            self.map(f)
        }

        #[inline(always)]
        unsafe fn index(&self, e: usize) -> &Self::Item {
            self.get_unchecked(e)
        }
        #[inline(always)]
        unsafe fn index_mut(&mut self, e: usize) -> &mut Self::Item {
            self.get_unchecked_mut(e)
        }
        fn iter(&self) -> slice::Iter<'_, Self::Item> {
            <[Self::Item]>::iter(self)
        }
        fn iter_mut(&mut self) -> slice::IterMut<'_, Self::Item> {
            <[Self::Item]>::iter_mut(self)
        }
    }

    use std;
    use std::iter;
    use std::ops;
    use std::ops::{Index, IndexMut};
    use std::slice;

    pub struct SWrappedDifference<E>(pub E);

    /// This trait is implemented by enums declared via the `plain_enum_mod` macro.
    /// Do not implement it yourself, but use this macro.
    pub unsafe trait PlainEnum : Sized {
        /// Arity, i.e. the smallest `usize` not representable by the enum.
        const SIZE : usize;
        /// Internal type of enum maps.
        type EnumMapArray<T> : TArrayExt<Item=T>;
        /// Converts `u` to the associated enum value. Assumes that `u` is a valid value for the enum, and is, thus, unsafe.
        unsafe fn from_usize(u: usize) -> Self;
        /// Converts the enum to its numerical representation.
        fn to_usize(self) -> usize;

        /// Checks whether `u` is the numerical representation of a valid enum value.
        fn valid_usize(u: usize) -> bool {
            u < Self::SIZE
        }
        /// Converts `u` to the associated enum value. if `u` is a valid value for the enum.
        fn checked_from_usize(u: usize) -> Option<Self> {
            if Self::valid_usize(u) {
                unsafe { Some(Self::from_usize(u)) }
            } else {
                None
            }
        }
        /// Converts `u` to the associated enum value, but wraps `u` it before conversion (i.e. it
        /// applies the modulo operation with a modulus equal to the arity of the enum before converting).
        fn wrapped_from_usize(u: usize) -> Self {
            unsafe { Self::from_usize(u % Self::SIZE) }
        }
        /// Computes the difference between two enum values, wrapping around if necessary.
        fn wrapped_difference_usize(self, e_other: Self) -> usize {
            (self.to_usize() + Self::SIZE - e_other.to_usize()) % Self::SIZE
        }
        /// Computes the difference between two enum values, wrapping around if necessary, and converts it to an enum value.
        fn wrapped_difference(self, e_other: Self) -> SWrappedDifference<Self> {
            SWrappedDifference(unsafe{Self::from_usize(self.wrapped_difference_usize(e_other))})
        }
        /// Returns an iterator over the enum's values.
        fn values() -> iter::Map<ops::Range<usize>, fn(usize) -> Self> {
            (0..Self::SIZE)
                .map(|u| unsafe { Self::from_usize(u) })
        }
        /// Adds a number to the enum, wrapping.
        fn wrapping_add(self, n_offset: usize) -> Self {
            unsafe { Self::from_usize((self.to_usize() + n_offset) % Self::SIZE) }
        }
        /// Creates a enum map from enum values to a type, determined by `func`.
        /// The map will contain the results of applying `func` to each enum value.
        fn map_from_fn<F, T>(mut func: F) -> EnumMap<Self, T>
            where F: FnMut(Self) -> T,
        {
            EnumMap::from_raw(Self::EnumMapArray::<T>::from_fn(|i| func(unsafe{Self::from_usize(i)})))
        }
        /// Creates a enum map from a raw array.
        fn map_from_raw<V>(a: Self::EnumMapArray::<V>) -> EnumMap<Self, V>
            where
        {
            EnumMap::from_raw(a)
        }
    }

    #[allow(dead_code)]
    #[derive(Eq, PartialEq, Hash, Copy)]
    pub struct EnumMap<E: PlainEnum, V>
        where E: PlainEnum,
    {
        phantome: std::marker::PhantomData<E>,
        a: E::EnumMapArray<V>,
    }

    impl<E, V> Clone for EnumMap<E, V>
        where
            E: PlainEnum,
            V: Clone,
    {
        fn clone(&self) -> Self {
            E::map_from_fn(|e| self[e].clone()) // TODO can this be improved?
        }
    }

    impl<E, V> std::fmt::Debug for EnumMap<E, V> // TODO can this be more elegant?
        where
            E: PlainEnum + std::fmt::Debug,
            V: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f
                .debug_map()
                .entries(E::values().map(|e| {
                    let i = e.to_usize();
                    let e2 = unsafe { E::from_usize(i) }; // avoids requiring Clone
                    let e3 = unsafe { E::from_usize(i) }; // avoids requiring Clone
                    (e2, &self[e3])
                }))
                .finish()
        }
    }

    impl<V: Default, E: PlainEnum> Default for EnumMap<E, V> {
        fn default() -> Self {
            E::map_from_fn(|_| Default::default())
        }
    }

    impl<E, V> EnumMap<E, V>
        where E: PlainEnum,
    {
        /// Constructs an `EnumMap` from the underlying array type.
        pub fn from_raw(a: E::EnumMapArray<V>) -> Self {
            EnumMap{
                phantome: std::marker::PhantomData{},
                a,
            }
        }
        /// Returns an iterator over the values of the EnumMap. (Similar to an iterator over a slice.)
        pub fn iter(&self) -> slice::Iter<'_, V> {
            self.a.iter()
        }
        /// Returns an iterator over the mutable values of the EnumMap. (Similar to an iterator over a slice.)
        pub fn iter_mut(&mut self) -> slice::IterMut<'_, V> {
            self.a.iter_mut()
        }
        /// Maps the values in a map. (Similar to `Iterator::map`.)
        pub fn map<FnMap, W>(&self, fn_map: FnMap) -> EnumMap<E, W>
            where FnMap: Fn(&V) -> W,
                  E: PlainEnum,
        {
            E::map_from_fn(|e|
                fn_map(&self[e])
            )
        }
        /// Moves and maps the values in a map. (Similar to `Iterator::map`.)
        pub fn map_into<FnMap, W>(self, fn_map: FnMap) -> EnumMap<E, W>
            where FnMap: Fn(V) -> W,
                  E: PlainEnum,
                  <<E as PlainEnum>::EnumMapArray<V> as TArrayExt>::MappedType::<W>: Into<E::EnumMapArray<W>>
        {
            EnumMap::<E, W>::from_raw(self.a.map(fn_map).into())
        }
        /// Consumes an `EnumMap` and returns the underlying array.
        pub fn into_raw(self) -> E::EnumMapArray::<V> {
            self.a
        }
        /// Exposes a reference to the underlying array.
        pub fn as_raw(&self) -> &E::EnumMapArray::<V> {
            &self.a
        }
        /// Exposes a mutable reference to the underlying array.
        pub fn as_raw_mut(&mut self) -> &mut E::EnumMapArray::<V> {
            &mut self.a
        }
    }
    impl<E, V> Index<E> for EnumMap<E, V>
        where E: PlainEnum,
    {
        type Output = V;
        fn index(&self, e: E) -> &V {
            unsafe { self.a.index(e.to_usize()) } // array size is E::SIZE
        }
    }
    impl<E, V> IndexMut<E> for EnumMap<E, V>
        where E: PlainEnum,
    {
        fn index_mut(&mut self, e: E) -> &mut Self::Output {
            unsafe { self.a.index_mut(e.to_usize()) } // array size is E::SIZE
        }
    }

    #[macro_export]
    macro_rules! tt {
        ($func: ident, [$($acc: expr,)*], []) => {
            [$($acc,)*]
        };
        ($func: ident, [$($acc: expr,)*], [$enumval: ident, $($enumvals: ident,)*]) => {
            acc_arr!($func, [$($acc,)* $func($enumval),], [$($enumvals,)*])
        };
    }


    #[macro_export]
    macro_rules! internal_impl_plainenum {($enumname: ty, $enumsize: expr, $from_usize: expr,) => {
        unsafe impl $crate::PlainEnum for $enumname {
            const SIZE : usize = $enumsize;
            type EnumMapArray<T> = [T; $enumsize];
            unsafe fn from_usize(u: usize) -> Self {
                $from_usize(u)
            }
            fn to_usize(self) -> usize {
                self as usize
            }
        }
    }}

    #[macro_export]
    macro_rules! plain_enum_mod {
        ($modname: ident, derive($($derives:ident, )*), map_derive($($mapderives:ident, )*), $enumname: ident {
            $($enumvals: ident,)*
        } ) => {
            #[repr(usize)]
            #[derive(PartialEq, Eq, Debug, Copy, Clone, PartialOrd, Ord, $($derives,)*)]
            pub enum $enumname {
                $(#[allow(dead_code)] $enumvals,)*
            }
            mod $modname {
                use super::$enumname;

                const SIZE : usize = $crate::enum_seq_len!($($enumvals,)*);
                $crate::internal_impl_plainenum!(
                    $enumname,
                    SIZE,
                    |u|{
                        use std::mem;
                        debug_assert!(Self::valid_usize(u));
                        mem::transmute(u)
                    },
                );
            }
        };
        ($modname: ident, $enumname: ident {
            $($enumvals: ident,)*
        } ) => {
            plain_enum_mod!($modname, derive(), map_derive(), $enumname { $($enumvals,)* });
        };
    }
}

pub use crate::plain_enum::PlainEnum;
pub use crate::plain_enum::EnumMap;
pub use crate::plain_enum::TArrayExt;

internal_impl_plainenum!(
    bool,
    2,
    |u|{
        debug_assert!(u==0 || u==1);
        0!=u
    },
);

unsafe impl PlainEnum for () {
    const SIZE : usize = 1;
    type EnumMapArray<T> = [T; 1];
    unsafe fn from_usize(u: usize) -> Self {
        debug_assert_eq!(0, u);
    }
    fn to_usize(self) -> usize {
        0
    }
}

unsafe impl PlainEnum for std::cmp::Ordering {
    const SIZE : usize = 3;
    type EnumMapArray<T> = [T; 3];
    // TODO: can we do better here by e.g. exploiting that Less==-1, Equal==0, Greater==1? Not sure if this is guaranteed.
    unsafe fn from_usize(u: usize) -> Self {
        match u {
            0 => std::cmp::Ordering::Less,
            1 => std::cmp::Ordering::Equal,
            u => {
                debug_assert_eq!(u, 2);
                std::cmp::Ordering::Greater
            },
        }
    }
    fn to_usize(self) -> usize {
        match self {
            std::cmp::Ordering::Less => 0,
            std::cmp::Ordering::Equal => 1,
            std::cmp::Ordering::Greater => 2,
        }
    }
}

// TODO support Option, Result, etc.
// TODO support nested enums

#[cfg(test)]
mod tests {
    use crate::plain_enum::*;
    plain_enum_mod!{test_module, ETest {
        E1, E2, E3,
    }}
    plain_enum_mod!{test_module_with_hash, derive(Hash,), map_derive(Hash,), ETestWithHash {
        E1, E2, E3,
    }}

    #[test]
    fn test_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(ETestWithHash::E1);
        assert!(set.contains(&ETestWithHash::E1));
        assert!(!set.contains(&ETestWithHash::E2));
        let enummap = ETestWithHash::map_from_fn(|e| e);
        let mut set2 = HashSet::new();
        set2.insert(enummap);
    }

    #[test]
    fn test_clone() {
        let map1 = ETest::map_from_fn(|e| e);
        #[allow(clippy::clone_on_copy)]
        let map2 = map1.clone();
        assert_eq!(map1, map2);
    }

    #[test]
    fn test_enum_seq_len() {
        assert_eq!(0, enum_seq_len!());
        assert_eq!(1, enum_seq_len!(E1,));
        assert_eq!(2, enum_seq_len!(E1, E3,));
        assert_eq!(3, enum_seq_len!(E1, E2, E3,));
        assert_eq!(14, enum_seq_len!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,));
        assert_eq!(13, enum_seq_len!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, ));
    }

    #[test]
    fn test_plain_enum() {
        assert_eq!(3, ETest::SIZE);
    }

    #[test]
    fn test_values() {
        assert_eq!(vec![ETest::E1, ETest::E2, ETest::E3], ETest::values().collect::<Vec<_>>());
        assert_eq!(ETest::values().count(), 3);
        assert_eq!((3, Some(3)), ETest::values().size_hint());
        assert_eq!(3, ETest::values().len());
        assert!(ETest::values().eq(ETest::values().rev().rev()));
    }

    #[test]
    fn test_enummap() {
        let mut map_test_to_usize = ETest::map_from_fn(|test| test.to_usize());
        for test in ETest::values() {
            assert_eq!(map_test_to_usize[test], test.to_usize());
        }
        for test in ETest::values() {
            map_test_to_usize[test] += 1;
        }
        for test in ETest::values() {
            assert_eq!(map_test_to_usize[test], test.to_usize()+1);
        }
        for v in map_test_to_usize.iter().zip(ETest::values()) {
            assert_eq!(*v.0, v.1.to_usize()+1);
        }
        for v in map_test_to_usize.map(|n| Some(n*n)).iter() {
            assert!(v.is_some());
        }
    }

    #[test]
    fn test_map_into() {
        struct NonCopy;
        let map_test_to_usize = ETest::map_from_fn(|_| NonCopy);
        let _map2 : EnumMap<_, (NonCopy, usize)> =  map_test_to_usize.map_into(|noncopy| (noncopy, 0));
    }

    #[test]
    fn test_bool() {
        let mapbn = bool::map_from_fn(|b| b as usize);
        assert_eq!(mapbn[false], 0);
        assert_eq!(mapbn[true], 1);
    }

    #[test]
    fn test_unit() {
        let mapbn = <()>::map_from_fn(|()| 42);
        assert_eq!(mapbn[()], 42);
        assert_eq!(<()>::SIZE, 1);
    }

    #[test]
    fn test_wrapped_difference() {
        assert_eq!(ETest::E3.wrapped_difference_usize(ETest::E1), 2);
        assert_eq!(ETest::E1.wrapped_difference_usize(ETest::E3), 1);
        assert_eq!(ETest::E3.wrapped_difference(ETest::E1).0, ETest::E3);
        assert_eq!(ETest::E1.wrapped_difference(ETest::E3).0, ETest::E2);
        for e1 in ETest::values() {
            for e2 in ETest::values() {
                assert_eq!(e1.wrapped_difference_usize(e2), e1.wrapped_difference(e2).0.to_usize());
            }
        }
    }

    #[test]
    fn test_default() {
        let _enummap : EnumMap<ETest, usize> = Default::default();
    }

    #[test]
    fn test_from_raw() {
        let enummap = ETest::map_from_raw([1,2,3]);
        assert_eq!(enummap[ETest::E1], 1);
        assert_eq!(enummap[ETest::E2], 2);
        assert_eq!(enummap[ETest::E3], 3);
    }
}

