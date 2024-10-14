use cranelift_entity::PrimaryMap;
use rustc_hash::FxHashMap;

use super::FunctionBuilder;
use crate::{
    func_cursor::{CursorLocation, FuncCursor},
    module::{FuncRef, ModuleCtx},
    Function, GlobalVariable, GlobalVariableData, InstSetBase, Module, Signature, Type,
};

pub struct ModuleBuilder {
    pub funcs: PrimaryMap<FuncRef, Function>,

    pub ctx: ModuleCtx,

    /// Map function name -> FuncRef to avoid duplicated declaration.
    declared_funcs: FxHashMap<String, FuncRef>,
}

impl ModuleBuilder {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
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
            let func = Function::new(&self.ctx, sig.clone());
            let func_ref = self.funcs.push(func);
            self.declared_funcs.insert(name, func_ref);
            self.ctx.declared_funcs[func_ref] = sig;
            func_ref
        }
    }

    pub fn sig(&self, func: FuncRef) -> &Signature {
        &self.funcs[func].sig
    }

    pub fn make_global(&self, global: GlobalVariableData) -> GlobalVariable {
        self.ctx.with_gv_store_mut(|s| s.make_gv(global))
    }

    pub fn global_by_name(&self, name: &str) -> Option<GlobalVariable> {
        self.ctx.with_gv_store(|s| s.gv_by_symbol(name))
    }

    pub fn declare_struct_type(&mut self, name: &str, fields: &[Type], packed: bool) -> Type {
        self.ctx
            .with_ty_store_mut(|s| s.make_struct(name, fields, packed))
    }

    pub fn get_struct_type(&self, name: &str) -> Option<Type> {
        self.ctx.with_ty_store(|s| s.struct_type_by_name(name))
    }

    pub fn declare_array_type(&mut self, elem: Type, len: usize) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_array(elem, len))
    }

    pub fn ptr_type(&mut self, ty: Type) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_ptr(ty))
    }

    pub fn get_func_ref(&self, name: &str) -> Option<FuncRef> {
        self.declared_funcs.get(name).copied()
    }

    pub fn get_sig(&self, func: FuncRef) -> &Signature {
        &self.funcs[func].sig
    }

    pub fn build_function<C>(self, func: FuncRef) -> FunctionBuilder<C>
    where
        C: FuncCursor,
    {
        let cursor = C::at_location(CursorLocation::NoWhere);
        FunctionBuilder::new(self, func, cursor)
    }

    pub fn build(self) -> Module {
        Module {
            funcs: self.funcs,
            ctx: self.ctx,
        }
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.ctx.inst_set
    }
}
