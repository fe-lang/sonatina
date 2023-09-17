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

    pub fn deserialize(ctx: &ModuleCtx, ty: Type, b: Vec<u8>) -> Option<Self> {
        Some(Self::Literal(match ty {
            Type::I1 => (b[0] & 0b1).into(),
            Type::I8 => i8::from_be_bytes(b.try_into().unwrap()).into(),
            Type::I16 => i16::from_be_bytes(b.try_into().unwrap()).into(),
            Type::I32 => i32::from_be_bytes(b.try_into().unwrap()).into(),
            Type::I64 => i64::from_be_bytes(b.try_into().unwrap()).into(),
            Type::I128 => i128::from_be_bytes(b.try_into().unwrap()).into(),
            Type::I256 => I256::from_u256(U256::from_big_endian(&b)),
            Type::Compound(ty) => {
                debug_assert!(ctx.with_ty_store(|s| s.resolve_compound(ty).is_ptr()));
                debug_assert!(b.len() == std::mem::size_of::<usize>());
                U256::from(usize::from_be_bytes(b.try_into().unwrap())).into()
            }
            Type::Void => return None,
        }))
    }

    pub fn serialize(&self, ctx: &ModuleCtx, ty: Type) -> Vec<u8> {
        match ty {
            Type::I1 => self.i256().trunc_to_i8().to_be_bytes().to_vec(),
            Type::I8 => self.i256().trunc_to_i8().to_be_bytes().to_vec(),
            Type::I16 => self.i256().trunc_to_i16().to_be_bytes().to_vec(),
            Type::I32 => self.i256().trunc_to_i32().to_be_bytes().to_vec(),
            Type::I64 => self.i256().trunc_to_i64().to_be_bytes().to_vec(),
            Type::I128 => self.i256().trunc_to_i128().to_be_bytes().to_vec(),
            Type::I256 => {
                let mut b = [0u8; 32];
                self.i256().to_u256().to_big_endian(&mut b);
                b.to_vec()
            }
            Type::Compound(ty) => {
                debug_assert!(ctx.with_ty_store(|s| s.resolve_compound(ty).is_ptr()));
                let mut b = [0u8; 32];
                self.i256().to_u256().to_big_endian(&mut b);
                b[32 - std::mem::size_of::<usize>()..].to_vec()
            }
            Type::Void => Vec::new(),
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
