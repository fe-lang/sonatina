use cranelift_entity::{PrimaryMap, SecondaryMap};
use fxhash::FxHashMap;

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
    pub isa: TargetIsa,

    pub funcs: PrimaryMap<FuncRef, Function>,

    pub func_attributes: SecondaryMap<FuncRef, FuncAttribute>,

    /// Map function name -> FuncRef to avoid duplicated declaration.
    declared_funcs: FxHashMap<String, FuncRef>,
}

impl ModuleBuilder {
    pub fn new(isa: TargetIsa) -> Self {
        Self {
            isa,
            funcs: PrimaryMap::default(),
            func_attributes: SecondaryMap::with_default(FuncAttribute {
                linkage: Linkage::External,
            }),
            declared_funcs: FxHashMap::default(),
        }
    }

    pub fn declare_function(&mut self, sig: Signature, linkage: Linkage) -> FuncRef {
        if let Some(&func_ref) = self.declared_funcs.get(sig.name()) {
            if self.func_attributes[func_ref].linkage != linkage {
                panic!(
                    "{} is already declared, but linkage is inconsistent.",
                    sig.name()
                )
            }
            func_ref
        } else {
            let func = Function::new(sig);
            let func_ref = self.funcs.push(func);
            self.func_attributes[func_ref] = FuncAttribute { linkage };
            func_ref
        }
    }

    pub fn get_func_ref(&mut self, name: &str) -> Option<FuncRef> {
        self.declared_funcs.get(name).copied()
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
