use cranelift_entity::{PrimaryMap, SecondaryMap};

use crate::{
    ir::{
        module::{FuncAttribute, FuncRef, Linkage},
        Function, Module, Signature,
    },
    TargetIsa,
};

use super::FunctionBuilder;

#[derive(Debug)]
pub struct ModuleBuilder {
    pub(super) isa: TargetIsa,

    pub(super) funcs: PrimaryMap<FuncRef, Function>,

    pub(super) func_attributes: SecondaryMap<FuncRef, FuncAttribute>,
}

impl ModuleBuilder {
    pub fn new(isa: TargetIsa) -> Self {
        Self {
            isa,
            funcs: PrimaryMap::default(),
            func_attributes: SecondaryMap::with_default(FuncAttribute {
                linkage: Linkage::External,
            }),
        }
    }

    pub fn declare_function(&mut self, sig: Signature, linkage: Linkage) -> FuncRef {
        let func = Function::new(sig);
        let func_ref = self.funcs.push(func);
        self.func_attributes[func_ref] = FuncAttribute { linkage };
        func_ref
    }

    pub fn func_builder(&mut self, func: FuncRef) -> FunctionBuilder {
        FunctionBuilder::new(self, func)
    }

    pub fn build(self) -> Module {
        Module {
            isa: self.isa,
            funcs: self.funcs,
            func_attributes: self.func_attributes,
        }
    }
}
