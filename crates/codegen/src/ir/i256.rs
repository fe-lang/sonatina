use std::{cmp, fmt, hash};

use primitive_types::U256;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct I256 {
    is_negative: bool,
    abs: U256,
}

const I256_MASK: U256 = primitive_types::U256([
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x7fff_ffff_ffff_ffff,
]);

impl I256 {
    pub fn from_u256(val: U256) -> Self {
        let is_negative = (val & I256_MASK) != val;
        let abs = if is_negative { !val + U256::one() } else { val };

        Self { is_negative, abs }
    }

    pub fn to_u256(&self) -> U256 {
        if self.is_negative {
            !self.abs + U256::one()
        } else {
            self.abs
        }
    }

    pub fn make_positive(abs: U256) -> Self {
        Self {
            is_negative: false,
            abs,
        }
    }

    pub fn make_negative(abs: U256) -> Self {
        Self {
            is_negative: true,
            abs,
        }
    }

    pub fn is_negative(&self) -> bool {
        self.is_negative
    }

    pub fn is_zero(&self) -> bool {
        self.abs.is_zero()
    }

    pub fn is_minimum(&self) -> bool {
        self.is_negative && self.abs != U256::zero() && (self.abs & I256_MASK) == U256::zero()
    }

    pub fn overflowing_div(self, rhs: I256) -> (I256, bool) {
        if rhs.is_zero() {
            panic!("attempt to divide by zero");
        }

        if self.is_minimum() && rhs.is_negative && rhs.abs == U256::one() {
            return (self, true);
        }

        let div_abs = self.abs / rhs.abs;

        match (self.is_negative, rhs.is_negative) {
            (true, true) | (false, false) => (I256::make_positive(div_abs), false),
            _ => (I256::make_negative(div_abs), false),
        }
    }
}

impl Ord for I256 {
    fn cmp(&self, rhs: &I256) -> cmp::Ordering {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => self.abs.cmp(&rhs.abs).reverse(),
            (true, false) => cmp::Ordering::Greater,
            (false, true) => cmp::Ordering::Less,
            (false, false) => self.abs.cmp(&rhs.abs),
        }
    }
}

impl PartialOrd<I256> for I256 {
    fn partial_cmp(&self, other: &I256) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for I256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_negative() {
            write!(f, "-{}", self.abs)
        } else {
            write!(f, "{}", self.abs)
        }
    }
}

impl hash::Hash for I256 {
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.to_u256().hash(state)
    }
}

macro_rules! impl_from {
    ($ty:ty, signed) => {
        impl From<$ty> for I256 {
            fn from(val: $ty) -> Self {
                if !val.is_negative() {
                    Self {
                        is_negative: false,
                        abs: U256::from(val),
                    }
                } else if val == <$ty>::MIN {
                    Self {
                        is_negative: true,
                        abs: U256::one() << std::mem::size_of::<$ty>() * 8,
                    }
                } else {
                    Self {
                        is_negative: true,
                        abs: U256::from(-val),
                    }
                }
            }
        }
    };

    ($ty:ty, unsigned) => {
        impl From<$ty> for I256 {
            fn from(val: $ty) -> Self {
                Self {
                    is_negative: false,
                    abs: U256::from(val),
                }
            }
        }
    };
}

impl_from!(i8, signed);
impl_from!(i16, signed);
impl_from!(i32, signed);
impl_from!(i64, signed);
impl_from!(i128, signed);
impl_from!(u8, unsigned);
impl_from!(u16, unsigned);
impl_from!(u32, unsigned);
impl_from!(u64, unsigned);
impl_from!(u128, unsigned);
