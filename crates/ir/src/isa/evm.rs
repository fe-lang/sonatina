use std::sync::LazyLock;

use sonatina_triple::{Architecture, TargetTriple};

use super::{Endian, Isa, TypeLayout, TypeLayoutError};
use crate::{inst::evm::inst_set::EvmInstSet, module::ModuleCtx, types::CompoundTypeData, Type};

#[derive(Debug, Clone, Copy)]
pub struct Evm {
    triple: TargetTriple,
}

impl Evm {
    pub fn new(triple: TargetTriple) -> Self {
        assert!(matches!(triple.architecture, Architecture::Evm));
        Self { triple }
    }
}

impl Isa for Evm {
    type InstSet = EvmInstSet;

    fn triple(&self) -> TargetTriple {
        self.triple
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        const TL: EvmTypeLayout = EvmTypeLayout {};
        &TL
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        static IS: LazyLock<EvmInstSet> = LazyLock::new(EvmInstSet::new);
        &IS
    }
}

struct EvmTypeLayout {}
impl TypeLayout for EvmTypeLayout {
    fn size_of(&self, ty: crate::Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        let size = match ty {
            Type::Unit => 0,
            Type::I1 => 1,
            Type::I8 => 1,
            Type::I16 => 2,
            Type::I32 => 4,
            Type::I64 => 8,
            Type::I128 => 16,
            Type::I256 => 32,

            Type::Compound(cmpd) => {
                let cmpd_data = ctx.with_ty_store(|s| s.resolve_compound(cmpd).clone());
                match cmpd_data {
                    CompoundTypeData::Array { elem, len } => self.size_of(elem, ctx)? * len,

                    CompoundTypeData::Ptr(_) => 32,

                    CompoundTypeData::Struct(s) => {
                        if s.packed {
                            panic!("packed data is not supported yet!");
                        }
                        let mut size = 0;
                        for &field in &s.fields {
                            size += self.size_of(field, ctx)?;
                        }

                        size
                    }

                    CompoundTypeData::Func { .. } => {
                        return Err(TypeLayoutError::UnrepresentableType(ty))
                    }
                }
            }
        };

        Ok(size)
    }

    fn pointer_repl(&self) -> Type {
        Type::I256
    }

    fn align_of(&self, _ty: Type, _ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        Ok(1)
    }

    fn endian(&self) -> Endian {
        Endian::Be
    }
}
