use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};

use crate::{Function, Signature};

#[derive(Debug, Clone)]
pub struct Module {
    /// Hold all function declared in the contract.
    pub funcs: PrimaryMap<FuncRef, Function>,

    pub func_attributes: SecondaryMap<FuncRef, FuncAttribute>,
}

impl Module {
    pub fn declare_function(&mut self, name: String, sig: Signature, linkage: Linkage) -> FuncRef {
        let func = Function::new(name, sig);
        let func_ref = self.funcs.push(func);
        self.func_attributes[func_ref] = FuncAttribute { linkage };
        func_ref
    }
}

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
