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
    ($($enumval_0: tt, $enumval_1: tt,)*) => (2*(enum_seq_len!($($enumval_0,)*)));
    ($enumval: tt, $($enumval_0: tt, $enumval_1: tt,)*) => (1+2*(enum_seq_len!($($enumval_0,)*)));
}

#[macro_use]
mod plain_enum {
    macro_rules! for_each_prefix (
        ($m:ident, [$($acc:tt,)*], []) => {
            $m!($($acc,)*);
        };
        ($m:ident, [$($acc:tt,)*], [$arg0:tt, $($arg:tt,)*]) => {
            $m!($($acc,)*);
            for_each_prefix!($m, [$($acc,)* $arg0,], [$($arg,)*]);
        };
    );
    pub trait TArrayFromFn<T> {
        fn array_from_fn<F>(func: F) -> Self
            where F: FnMut(usize) -> T;
        fn index(a: &Self, e: usize) -> &T;
        fn index_mut(a: &mut Self, e: usize) -> &mut T;
        fn iter(a: &Self) -> slice::Iter<T>;
    }
    macro_rules! impl_array_from_fn{($($i: tt,)*) => {
        impl<T> TArrayFromFn<T> for [T; enum_seq_len!($($i,)*)] {
            fn array_from_fn<F>(mut func: F) -> Self
                where F: FnMut(usize) -> T
            {
                [$(func($i),)*]
            }
            fn index(a: &Self, e: usize) -> &T {
                &a[e]
            }
            fn index_mut(a: &mut Self, e: usize) -> &mut T {
                &mut a[e]
            }
            fn iter(a: &Self) -> slice::Iter<T> {
                a.iter()
            }
        }
    }}
    for_each_prefix!{
        impl_array_from_fn,
        [0,],
        [
            1, 2, 3, 4, 5, 6, 7, 8, 9,
            10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
            30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
            40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
            50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
            60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
            70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
            80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
            90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
            100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
            110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
            120, 121, 122, 123, 124, 125, 126, 127, 128,
        ]
    }

    use std;
    use std::iter;
    use std::ops;
    use std::ops::{Index, IndexMut};
    use std::slice;

    /// This trait is implemented by enums declared via the `plain_enum_mod` macro.
    /// Do not implement it yourself, but use this macro.
    pub trait TPlainEnum : Sized {
        /// Arity, i.e. the smallest `usize` not representable by the enum.
        const SIZE : usize;
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
        fn wrapped_difference(self, e_other: Self) -> usize {
            (self.to_usize() + Self::SIZE - e_other.to_usize()) % Self::SIZE
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
                  Self: TInternalEnumMapType<T>,
        {
            EnumMap::from_raw(TArrayFromFn::array_from_fn(|i| func(unsafe{Self::from_usize(i)})))
        }
        /// Creates a enum map from a raw array.
        fn map_from_raw<V>(a: <Self as TInternalEnumMapType<V>>::InternalEnumMapType) -> EnumMap<Self, V>
            where
                Self: TInternalEnumMapType<V>, // TODORUST
        {
            EnumMap::from_raw(a)
        }
    }

    /// Trait used to associated enum with EnumMap.
    /// Needed because of https://github.com/rust-lang/rust/issues/46969.
    /// TODO Rust: Once this is solved, use array directly within EnumMap.
    pub trait TInternalEnumMapType<V> : TPlainEnum {
        type InternalEnumMapType : TArrayFromFn<V>;
    }

    #[allow(dead_code)]
    #[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
    pub struct EnumMap<E: TPlainEnum, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        phantome: std::marker::PhantomData<E>,
        a: E::InternalEnumMapType,
    }

    impl<E, V> EnumMap<E, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        /// Constructs an `EnumMap` from the underlying array type.
        pub fn from_raw(a: E::InternalEnumMapType) -> Self {
            EnumMap{
                phantome: std::marker::PhantomData{},
                a,
            }
        }
        /// Returns an iterator over the values of the EnumMap. (Similar to an iterator over a slice.)
        pub fn iter(&self) -> slice::Iter<V> {
            TArrayFromFn::iter(&self.a)
        }
        /// Maps the values in a map. (Similar to `Iterator::map`.)
        pub fn map<FnMap, W>(&self, fn_map: FnMap) -> EnumMap<E, W>
            where FnMap: Fn(&V) -> W,
                  E: TInternalEnumMapType<W>,
                  E: TPlainEnum,
        {
            E::map_from_fn(|e|
                fn_map(&self[e])
            )
        }
        /// Consumes an `EnumMap` and returns the underlying array.
        pub fn into_raw(self) -> E::InternalEnumMapType {
            self.a
        }
    }
    impl<E, V> Index<E> for EnumMap<E, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        type Output = V;
        fn index(&self, e: E) -> &V {
            TArrayFromFn::index(&self.a, e.to_usize())
        }
    }
    impl<E, V> IndexMut<E> for EnumMap<E, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        fn index_mut(&mut self, e: E) -> &mut Self::Output {
            TArrayFromFn::index_mut(&mut self.a, e.to_usize())
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
    macro_rules! internal_impl_plainenum {($enumname: ident, $enumsize: expr, $from_usize: expr,) => {
        impl TPlainEnum for $enumname {
            const SIZE : usize = $enumsize;
            unsafe fn from_usize(u: usize) -> Self {
                $from_usize(u)
            }
            fn to_usize(self) -> usize {
                self as usize
            }
        }
        impl<V> TInternalEnumMapType<V> for $enumname {
            type InternalEnumMapType = [V; $enumname::SIZE];
        }
    }}

    #[macro_export]
    macro_rules! plain_enum_mod {
        ($modname: ident, derive($($derives:ident, )*), map_derive($($mapderives:ident, )*), $enumname: ident {
            $($enumvals: ident,)*
        } ) => {
            mod $modname {
                use plain_enum::*;
                #[repr(usize)]
                #[derive(PartialEq, Eq, Debug, Copy, Clone, PartialOrd, Ord, $($derives,)*)]
                pub enum $enumname {
                    $(#[allow(dead_code)] $enumvals,)*
                }

                const SIZE : usize = enum_seq_len!($($enumvals,)*);
                internal_impl_plainenum!(
                    $enumname,
                    SIZE,
                    |u|{
                        use std::mem;
                        debug_assert!(Self::valid_usize(u));
                        mem::transmute(u)
                    },
                );
            }
            pub use self::$modname::$enumname;
        };
        ($modname: ident, $enumname: ident {
            $($enumvals: ident,)*
        } ) => {
            plain_enum_mod!($modname, derive(), map_derive(), $enumname { $($enumvals,)* });
        };
    }
}

pub use plain_enum::TPlainEnum;
pub use plain_enum::EnumMap;
pub use plain_enum::TInternalEnumMapType;

internal_impl_plainenum!(
    bool,
    2,
    |u|{
        debug_assert!(u==0 || u==1);
        0!=u
    },
);

#[cfg(test)]
mod tests {
    use plain_enum::*;
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
    fn test_bool() {
        let mapbn = bool::map_from_fn(|b| b as usize);
        assert_eq!(mapbn[false], 0);
        assert_eq!(mapbn[true], 1);
    }
}

