use std::mem;

use byteorder::{BigEndian, WriteBytesExt};
use sonatina_ir::{module::ModuleCtx, Type, I256, U256};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum EvalValue {
    Literal(I256),
    #[default]
    Undefined,
}

impl EvalValue {
    pub fn from_i256(i256: I256) -> Self {
        Self::Literal(i256)
    }

    pub fn from_usize(addr: usize) -> Self {
        Self::Literal(addr.into())
    }

    pub fn i256(&self) -> I256 {
        let Self::Literal(i256) = *self else {
            panic!("undefined");
        };
        i256
    }

    pub fn deserialize(ctx: &ModuleCtx, ty: Type, b: &[u8]) -> Option<Self> {
        macro_rules! from_be_bytes {
            ($integral:ty) => {
                <$integral>::from_be_bytes(b.try_into().unwrap()).into()
            };
        }

        Some(Self::Literal(match ty {
            Type::I1 => (b[0] & 0b1).into(),
            Type::I8 => from_be_bytes!(i8),
            Type::I16 => from_be_bytes!(i16),
            Type::I32 => from_be_bytes!(i32),
            Type::I64 => from_be_bytes!(i64),
            Type::I128 => from_be_bytes!(i128),
            Type::I256 => I256::from_u256(U256::from_big_endian(b)),
            Type::Compound(ty) => {
                debug_assert!(ctx.with_ty_store(|s| s.resolve_compound(ty).is_ptr()));
                debug_assert!(b.len() == mem::size_of::<usize>());
                from_be_bytes!(usize)
            }
            Type::Void => return None,
        }))
    }

    pub fn serialize(&self, ctx: &ModuleCtx, ty: Type, mut buff: &mut [u8]) {
        macro_rules! to_be_bytes {
            ($bytes:expr) => {{
                let data = self.i256().trunc_to_i128();
                buff.write_int128::<BigEndian>(data, $bytes).unwrap()
            }};
        }

        match ty {
            Type::I1 => to_be_bytes!(1),
            Type::I8 => to_be_bytes!(1),
            Type::I16 => to_be_bytes!(2),
            Type::I32 => to_be_bytes!(4),
            Type::I64 => to_be_bytes!(8),
            Type::I128 => to_be_bytes!(16),
            Type::I256 => self.i256().to_u256().to_big_endian(buff),
            Type::Compound(ty) => {
                debug_assert!(ctx.with_ty_store(|s| s.resolve_compound(ty).is_ptr()));
                to_be_bytes!(mem::size_of::<usize>());
            }
            Type::Void => (),
        }
    }
}

pub enum EvalResult {
    I1(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    I256(I256),
    Void,
    Addr(usize),
}

impl EvalResult {
    pub fn from_i256(ctx: &ModuleCtx, i256: I256, ty: Type) -> Self {
        use EvalResult::*;
        match ty {
            Type::I1 => I1(i256.trunc_to_i1()),
            Type::I8 => I8(i256.trunc_to_i8()),
            Type::I16 => I16(i256.trunc_to_i16()),
            Type::I32 => I32(i256.trunc_to_i32()),
            Type::I64 => I64(i256.trunc_to_i64()),
            Type::I128 => I128(i256.trunc_to_i128()),
            Type::I256 => I256(i256),
            Type::Compound(_) => {
                debug_assert!(ctx.with_ty_store(|s| s.is_ptr(ty)));
                Addr(i256.to_u256().as_usize())
            }
            _ => unreachable!(),
        }
    }

    pub fn into_bool(self) -> bool {
        let Self::I1(boolean) = self else {
            panic!("not a boolean")
        };
        boolean
    }

    pub fn into_i8(self) -> i8 {
        let Self::I8(i8) = self else {
            panic!("not an i8")
        };
        i8
    }

    pub fn into_i16(self) -> i16 {
        let Self::I16(i16) = self else {
            panic!("not an i16")
        };
        i16
    }

    pub fn into_i32(self) -> i32 {
        let Self::I32(i32) = self else {
            panic!("not an i32")
        };
        i32
    }

    pub fn into_i64(self) -> i64 {
        let Self::I64(i64) = self else {
            panic!("not an i64")
        };
        i64
    }

    pub fn into_i128(self) -> i128 {
        let Self::I128(i128) = self else {
            panic!("not an i128")
        };
        i128
    }

    pub fn into_i256(self) -> I256 {
        let Self::I256(i256) = self else {
            panic!("not an i256")
        };
        i256
    }

    pub fn into_void(self) {
        let Self::Void = self else {
            panic!("not a void")
        };
    }

    pub fn into_usize(self) -> usize {
        let Self::Addr(usize) = self else {
            panic!("not a memory address")
        };
        usize
    }
}
