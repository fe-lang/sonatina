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
        match self {
            Self::Literal(i256) => *i256,
            _ => panic!(),
        }
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
