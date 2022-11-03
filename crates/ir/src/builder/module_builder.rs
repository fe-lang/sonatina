use cranelift_entity::PrimaryMap;
use fxhash::FxHashMap;

use crate::{
    isa::TargetIsa,
    module::{FuncRef, ModuleCtx},
    Function, Module, Signature,
};

use super::FunctionBuilder;

#[derive(Debug)]
pub struct ModuleBuilder {
    pub isa: TargetIsa,

    pub funcs: PrimaryMap<FuncRef, Function>,

    pub ctx: ModuleCtx,

    /// Map function name -> FuncRef to avoid duplicated declaration.
    declared_funcs: FxHashMap<String, FuncRef>,
}

impl ModuleBuilder {
    pub fn new(ctx: ModuleCtx, isa: TargetIsa) -> Self {
        Self {
            isa,
            funcs: PrimaryMap::default(),
            ctx,
            declared_funcs: FxHashMap::default(),
        }
    }

    pub fn declare_function(&mut self, sig: Signature) -> FuncRef {
        if self.declared_funcs.contains_key(sig.name()) {
            panic!("{} is already declared.", sig.name())
        } else {
            let name = sig.name().to_string();
            let func = Function::new(&self.ctx, sig);
            let func_ref = self.funcs.push(func);
            self.declared_funcs.insert(name, func_ref);
            func_ref
        }
    }

    pub fn get_func_ref(&self, name: &str) -> Option<FuncRef> {
        self.declared_funcs.get(name).copied()
    }

    pub fn get_sig(&self, func: FuncRef) -> &Signature {
        &self.funcs[func].sig
    }

    pub fn func_builder(&mut self, func: FuncRef) -> FunctionBuilder {
        FunctionBuilder::new(self, func)
    }

    pub fn build(self) -> Module {
        Module {
            isa: self.isa,
            funcs: self.funcs,
            ctx: self.ctx,
        }
    }
}
