use cranelift_entity::{entity_impl, PrimaryMap};

use crate::Function;

use crate::isa::TargetIsa;

use super::Linkage;

#[derive(Debug)]
pub struct Module {
    /// Target ISA of the module.
    pub isa: TargetIsa,

    /// Holds all function declared in the contract.
    pub funcs: PrimaryMap<FuncRef, Function>,
}

impl Module {
    #[doc(hidden)]
    pub fn new(isa: TargetIsa) -> Self {
        Self {
            isa,
            funcs: PrimaryMap::default(),
        }
    }

    /// Returns `func_ref` in the module.
    pub fn iter_functions(&self) -> impl Iterator<Item = FuncRef> {
        self.funcs.keys()
    }

    /// Returns `true` if the function has external linkage.
    pub fn is_external(&self, func_ref: FuncRef) -> bool {
        self.funcs[func_ref].sig.linkage() == Linkage::External
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncRef(u32);
entity_impl!(FuncRef);
