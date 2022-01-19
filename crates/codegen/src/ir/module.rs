use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};

use crate::ir::Function;

use crate::isa::TargetIsa;

#[derive(Debug)]
pub struct Module {
    /// Target ISA of the module.
    pub isa: TargetIsa,

    /// Holds all function declared in the contract.
    pub funcs: PrimaryMap<FuncRef, Function>,

    pub func_attributes: SecondaryMap<FuncRef, FuncAttribute>,
}

impl Module {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncAttribute {
    pub linkage: Linkage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncRef(u32);
entity_impl!(FuncRef);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Linkage of the function.
pub enum Linkage {
    /// The function is defined in the contract, and can be called from another accounts.
    Public,

    /// The function is defined in the contract, and can NOT be called from another accounts.
    Private,

    /// The function is defined outside of the contract.
    External,
}
