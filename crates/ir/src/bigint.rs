use std::{cmp, fmt, hash, ops};

pub type U256 = primitive_types::U256;

#[derive(Copy, Clone, Debug)]
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
    pub fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (val, flag) = self.to_u256().overflowing_add(rhs.to_u256());
        (Self::from_u256(val), flag)
    }

    pub fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (val, flag) = self.to_u256().overflowing_sub(rhs.to_u256());
        (Self::from_u256(val), flag)
    }

    pub fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (val, flag) = self.to_u256().overflowing_mul(rhs.to_u256());
        (Self::from_u256(val), flag)
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

    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        let u256_val = U256::from_big_endian(bytes);
        Self::from_u256(u256_val)
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        let u256_val = U256::from_little_endian(bytes);
        Self::from_u256(u256_val)
    }

    pub fn zero() -> Self {
        Self::from_u256(U256::zero())
    }

    pub fn one() -> Self {
        Self::from_u256(U256::one())
    }

    pub fn all_one() -> Self {
        I256::zero().overflowing_sub(I256::one()).0
    }

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

    pub fn trunc_to_i1(self) -> bool {
        (self.to_u256().low_u32() & 0x1) != 0
    }

    pub fn trunc_to_i8(self) -> i8 {
        self.to_u256().low_u32() as i8
    }

    pub fn trunc_to_i16(self) -> i16 {
        self.to_u256().low_u32() as i16
    }

    pub fn trunc_to_i32(self) -> i32 {
        self.to_u256().low_u32() as i32
    }

    pub fn trunc_to_i64(self) -> i64 {
        self.to_u256().low_u64() as i64
    }

    pub fn trunc_to_i128(self) -> i128 {
        self.to_u256().low_u128() as i128
    }

    pub fn is_positive(&self) -> bool {
        !self.is_negative && !self.is_zero()
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

    fn make_positive(abs: U256) -> Self {
        Self {
            is_negative: false,
            abs,
        }
    }

    fn make_negative(abs: U256) -> Self {
        Self {
            is_negative: true,
            abs,
        }
    }
}

impl ops::BitAnd for I256 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        Self::from_u256(self.to_u256() & rhs.to_u256())
    }
}

impl ops::BitOr for I256 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        Self::from_u256(self.to_u256() | rhs.to_u256())
    }
}

impl ops::Not for I256 {
    type Output = Self;

    fn not(self) -> Self {
        Self::from_u256(!self.to_u256())
    }
}

impl ops::Neg for I256 {
    type Output = Self;

    fn neg(self) -> Self {
        (!self).overflowing_add(Self::one()).0
    }
}

impl ops::BitXor for I256 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        Self::from_u256(self.to_u256() ^ rhs.to_u256())
    }
}

impl ops::Shl for I256 {
    type Output = Self;
    fn shl(self, rhs: Self) -> Self::Output {
        Self::from_u256(self.to_u256() << rhs.to_u256())
    }
}

impl ops::Shr for I256 {
    type Output = Self;
    fn shr(self, rhs: Self) -> Self::Output {
        Self::from_u256(self.to_u256() >> rhs.to_u256())
    }
}

impl Ord for I256 {
    fn cmp(&self, rhs: &I256) -> cmp::Ordering {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => self.abs.cmp(&rhs.abs).reverse(),
            (true, false) => cmp::Ordering::Less,
            (false, true) => cmp::Ordering::Greater,
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

impl cmp::PartialEq for I256 {
    fn eq(&self, rhs: &Self) -> bool {
        self.is_negative == rhs.is_negative && self.abs == rhs.abs
    }
}

impl cmp::Eq for I256 {}

impl From<U256> for I256 {
    fn from(val: U256) -> Self {
        Self::from_u256(val)
    }
}

impl From<bool> for I256 {
    fn from(val: bool) -> Self {
        if val {
            Self::all_one()
        } else {
            Self::zero()
        }
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
                        abs: U256::one() << std::mem::size_of::<$ty>() * 8 - 1,
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
impl_from!(usize, unsigned);
