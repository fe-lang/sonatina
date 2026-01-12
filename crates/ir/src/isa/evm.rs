use std::sync::LazyLock;

use sonatina_triple::{Architecture, TargetTriple};

use super::{Endian, Isa, TypeLayout, TypeLayoutError};
use crate::{Type, inst::evm::inst_set::EvmInstSet, module::ModuleCtx, types::CompoundType};

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
            // EVM memory is word-addressed by the MLOAD/MSTORE family. For now we model all
            // scalar/pointer values as occupying one full 32-byte slot.
            Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::I256 => 32,

            Type::Compound(cmpd) => {
                let cmpd_data = ctx.with_ty_store(|s| s.resolve_compound(cmpd).clone());
                match cmpd_data {
                    CompoundType::Array { elem, len } => self.size_of(elem, ctx)? * len,

                    CompoundType::Ptr(_) => 32,

                    CompoundType::Struct(s) => {
                        if s.packed {
                            panic!("packed data is not supported yet!");
                        }
                        let mut size = 0;
                        for &field in &s.fields {
                            size += self.size_of(field, ctx)?;
                        }

                        size
                    }

                    CompoundType::Func { .. } => {
                        return Err(TypeLayoutError::UnrepresentableType(ty));
                    }
                }
            }
        };

        Ok(size)
    }

    fn pointer_repl(&self) -> Type {
        Type::I256
    }

    fn align_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        let size = self.size_of(ty, ctx)?;
        if size == 0 { Ok(1) } else { Ok(32) }
    }

    fn endian(&self) -> Endian {
        Endian::Be
    }
}
