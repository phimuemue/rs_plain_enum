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

#[macro_use]
mod plain_enum {
    #[macro_export]
    macro_rules! enum_seq_len {
        ($n: expr, $enumval: ident,) => ($n);
        ($n: expr, $enumval: ident, $($enumvals: ident,)*) => (enum_seq_len!(($n + 1), $($enumvals,)*));
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
        /// Checks whether `u` is the numerical representation of a valid enum value.
        fn valid_usize(u: usize) -> bool;
        /// Converts `u` to the associated enum value. `assert`s that `u` is a valid value for the enum.
        fn from_usize(u: usize) -> Self;
        /// Converts `u` to the associated enum value. if `u` is a valid value for the enum.
        fn checked_from_usize(u: usize) -> Option<Self>;
        /// Converts `u` to the associated enum value, but wraps `u` it before conversion (i.e. it
        /// applies the modulo operation with a modulus equal to the arity of the enum before converting).
        fn wrapped_from_usize(u: usize) -> Self;
        /// Computes the difference between two enum values, wrapping around if necessary.
        fn wrapped_difference(self, e_other: Self) -> usize;
        /// Converts the enum to its numerical representation.
        fn to_usize(self) -> usize;
        /// Returns an iterator over the enum's values.
        fn values() -> iter::Map<ops::Range<usize>, fn(usize) -> Self> {
            (0..Self::SIZE)
                .map(Self::from_usize)
        }
        /// Adds a number to the enum, wrapping.
        fn wrapping_add(self, n_offset: usize) -> Self;
    }

    /// Trait used to associated enum with EnumMap.
    /// Needed because of https://github.com/rust-lang/rust/issues/46969.
    /// TODO Rust: Once this is solved, use array directly within EnumMap.
    pub trait TInternalEnumMapType<V> : TPlainEnum {
        type InternalEnumMapType;
        fn index(a: &Self::InternalEnumMapType, e: Self) -> &V;
        fn index_mut(a: &mut Self::InternalEnumMapType, e: Self) -> &mut V;
        fn iter(a: &Self::InternalEnumMapType) -> slice::Iter<V>;
    }

    #[allow(dead_code)]
    #[derive(Eq, PartialEq, Hash, Clone, Debug)]
    pub struct EnumMap<E: TPlainEnum, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        phantome: std::marker::PhantomData<E>,
        a: E::InternalEnumMapType,
    }

    macro_rules! forward_fn {
        ($(@$pub:tt)* fn $func:ident (&$(@$mut:tt)* self, $($param:ident : $type:ty,)*) -> $R:ty) => {
            $($pub)* fn $func(&$($mut)* self, $($param : $type,)*) -> $R {
                E::$func(&$($mut)* self.a, $($param,)*)
            }
        };
    }

    impl<E, V> EnumMap<E, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        pub fn from_raw(a: E::InternalEnumMapType) -> Self {
            EnumMap{
                phantome: std::marker::PhantomData{},
                a,
            }
        }
        forward_fn!(@pub fn iter(&self,) -> slice::Iter<V>);
    }
    impl<E, V> Index<E> for EnumMap<E, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        type Output = V;
        forward_fn!(fn index(&self, e: E,) -> &V);
    }
    impl<E, V> IndexMut<E> for EnumMap<E, V>
        where E: TPlainEnum + TInternalEnumMapType<V>,
    {
        forward_fn!(fn index_mut(&@mut self, e: E,) -> &mut Self::Output);
    }

    #[macro_export]
    macro_rules! acc_arr {
        ($func: ident, [$($acc: expr,)*], []) => {
            [$($acc,)*]
        };
        ($func: ident, [$($acc: expr,)*], [$enumval: ident, $($enumvals: ident,)*]) => {
            acc_arr!($func, [$($acc,)* $func($enumval),], [$($enumvals,)*])
        };
    }

    #[macro_export]
    macro_rules! plain_enum_mod {
        ($modname: ident, derive($($derives:ident, )*), map_derive($($mapderives:ident, )*), $enumname: ident {
            $($enumvals: ident,)*
        } ) => {
            mod $modname {
                use plain_enum::*;
                use std::slice;
                #[repr(usize)]
                #[derive(PartialEq, Eq, Debug, Copy, Clone, PartialOrd, Ord, $($derives,)*)]
                pub enum $enumname {
                    $($enumvals,)*
                }

                impl TPlainEnum for $enumname {

                    const SIZE : usize = enum_seq_len!(1, $($enumvals,)*);

                    fn valid_usize(u: usize) -> bool {
                        u < Self::SIZE
                    }
                    fn from_usize(u: usize) -> Self {
                        use std::mem;
                        debug_assert!(Self::valid_usize(u));
                        unsafe{mem::transmute(u)}
                    }
                    fn checked_from_usize(u: usize) -> Option<Self> {
                        if Self::valid_usize(u) {
                            Some(Self::from_usize(u))
                        } else {
                            None
                        }
                    }
                    fn wrapped_from_usize(u: usize) -> Self {
                        Self::from_usize(u % Self::SIZE)
                    }
                    fn wrapped_difference(self, e_other: Self) -> usize {
                        (self.to_usize() + Self::SIZE - e_other.to_usize()) % Self::SIZE
                    }
                    fn to_usize(self) -> usize {
                        self as usize
                    }
                    fn wrapping_add(self, n_offset: usize) -> Self {
                        Self::from_usize((self.to_usize() + n_offset) % Self::SIZE)
                    }
                }

                impl<V> TInternalEnumMapType<V> for $enumname {
                    type InternalEnumMapType = [V; $enumname::SIZE];
                    fn index(a: &Self::InternalEnumMapType, e: Self) -> &V {
                        &a[e.to_usize()]
                    }
                    fn index_mut(a: &mut Self::InternalEnumMapType, e: Self) -> &mut V {
                        &mut a[e.to_usize()]
                    }
                    fn iter(a: &Self::InternalEnumMapType) -> slice::Iter<V> {
                        a.iter()
                    }
                }

                impl $enumname {
                    #[allow(dead_code)]
                    /// Creates a enum map from enum values to a type, determined by `func`.
                    /// The map will contain the results of applying `func` to each enum value.
                    pub fn map_from_fn<F, T>(mut func: F) -> EnumMap<$enumname, T>
                        where F: FnMut($enumname) -> T,
                    {
                        use self::$enumname::*;
                        EnumMap::from_raw(acc_arr!(func, [], [$($enumvals,)*]))
                    }
                    /// Creates a enum map from a raw array.
                    #[allow(dead_code)]
                    pub fn map_from_raw<V>(a: <Self as TInternalEnumMapType<V>>::InternalEnumMapType) -> EnumMap<$enumname, V> {
                        EnumMap::from_raw(a)
                    }
                }
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
    fn test_plain_enum() {
        assert_eq!(3, enum_seq_len!(1, E1, E2, E3,));
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
    }
}

pub mod examples_not_to_be_used_by_clients {
    //! A sample module showing the capabilities of this crate. Do not use it or rely on it.
    plain_enum_mod!{example_mod_name, ExampleEnum {
        V1,
        V2,
        SomeOtherValue,
        LastValue, // note trailing comma
    }}
}
