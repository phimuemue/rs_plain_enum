#[macro_use]
mod plain_enum {
    #[macro_export]
    macro_rules! enum_seq_len {
        ($n: expr, $enumval: ident,) => ($n);
        ($n: expr, $enumval: ident, $($enumvals: ident,)*) => (enum_seq_len!(($n + 1), $($enumvals,)*));
    }

    use std::iter;
    use std::ops;

    pub trait TPlainEnum : Sized {
        fn valid_usize(u: usize) -> bool;
        fn from_usize(u: usize) -> Self;
        fn checked_from_usize(u: usize) -> Option<Self>;
        fn wrapped_from_usize(u: usize) -> Self;
        fn wrapped_difference(self, e_other: Self) -> usize;
        fn to_usize(self) -> usize;
        fn ubound_usize() -> usize;
        fn values() -> iter::Map<ops::Range<usize>, fn(usize) -> Self> {
            (0..Self::ubound_usize())
                .map(Self::from_usize)
        }
        fn wrapping_add(self, n_offset: usize) -> Self;
    }

    pub trait TEnumMapType<T> : TPlainEnum {
        type MapType;
    }

    #[allow(dead_code)]
    pub type EnumMap<PlainEnum, T> where PlainEnum: TEnumMapType<T> = PlainEnum::MapType;

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
        ($modname: ident, $enumname: ident {
            $($enumvals: ident,)*
        } ) => {
            mod $modname {
                use plain_enum::*;
                use std::slice;
                #[repr(usize)]
                #[derive(PartialEq, Eq, Debug, Copy, Clone, PartialOrd, Ord, Hash)]
                pub enum $enumname {
                    $($enumvals,)*
                }

                const ENUMSIZE : usize = enum_seq_len!(1, $($enumvals,)*);

                impl TPlainEnum for $enumname {
                    fn ubound_usize() -> usize {
                        ENUMSIZE
                    }
                    fn valid_usize(u: usize) -> bool {
                        u < ENUMSIZE
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
                        Self::from_usize(u % ENUMSIZE)
                    }
                    fn wrapped_difference(self, e_other: Self) -> usize {
                        (self.to_usize() + ENUMSIZE - e_other.to_usize()) % ENUMSIZE
                    }
                    fn to_usize(self) -> usize {
                        self as usize
                    }
                    fn wrapping_add(self, n_offset: usize) -> Self {
                        Self::from_usize((self.to_usize() + n_offset) % ENUMSIZE)
                    }
                }

                impl $enumname {
                    #[allow(dead_code)]
                    pub fn map_from_fn<F, T>(mut func: F) -> Map<T>
                        where F: FnMut($enumname) -> T,
                    {
                        use self::$enumname::*;
                        Map::from_raw(acc_arr!(func, [], [$($enumvals,)*]))
                    }
                    #[allow(dead_code)]
                    pub fn map_from_raw<T>(at: [T; ENUMSIZE]) -> Map<T> {
                        Map::from_raw(at)
                    }
                }

                impl<T> TEnumMapType<T> for $enumname {
                    type MapType = Map<T>;
                }

                use std::ops::{Index, IndexMut};
                #[derive(PartialEq, Debug)]
                pub struct Map<T> {
                    m_at : [T; ENUMSIZE],
                }
                impl<T> Index<$enumname> for Map<T> {
                    type Output = T;
                    fn index(&self, e : $enumname) -> &T {
                        &self.m_at[e.to_usize()]
                    }
                }
                impl<T> IndexMut<$enumname> for Map<T> {
                    fn index_mut(&mut self, e : $enumname) -> &mut Self::Output {
                        &mut self.m_at[e.to_usize()]
                    }
                }
                impl<T> Map<T> {
                    #[allow(dead_code)]
                    pub fn iter(&self) -> slice::Iter<T> {
                        self.m_at.iter()
                    }
                    pub fn from_raw(at: [T; ENUMSIZE]) -> Map<T> {
                        Map {
                            m_at : at,
                        }
                    }
                }
            }
            pub use self::$modname::$enumname;
        }
    }
}
pub use plain_enum::TPlainEnum;
pub use plain_enum::TEnumMapType;
pub use plain_enum::EnumMap;

#[cfg(test)]
mod tests {
    use plain_enum::*;
    plain_enum_mod!{test_module, ETest {
        E1, E2, E3,
    }}

    #[test]
    fn test_plain_enum() {
        assert_eq!(3, enum_seq_len!(1, E1, E2, E3,));
        assert_eq!(3, ETest::ubound_usize());
    }

    #[test]
    fn test_values() {
        assert_eq!(vec![ETest::E1, ETest::E2, ETest::E3], ETest::values().collect::<Vec<_>>());
        assert_eq!(ETest::values().count(), 3);
    }

    fn type_test(_map: &EnumMap<ETest, usize>) {}

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
        type_test(&map_test_to_usize);
    }
}
