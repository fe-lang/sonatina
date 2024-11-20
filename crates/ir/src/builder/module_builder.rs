use std::sync::Arc;

use dashmap::DashMap;

use super::FunctionBuilder;
use crate::{
    func_cursor::{CursorLocation, FuncCursor},
    module::{FuncRef, FuncStore, ModuleCtx},
    Function, GlobalVariable, GlobalVariableData, InstSetBase, Module, Signature, Type,
};

#[derive(Clone)]
pub struct ModuleBuilder {
    pub funcs: Arc<FuncStore>,

    pub ctx: ModuleCtx,

    /// Map function name -> FuncRef to avoid duplicated declaration.
    declared_funcs: Arc<DashMap<String, FuncRef>>,
}

impl ModuleBuilder {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
            funcs: Arc::new(FuncStore::new()),
            ctx,
            declared_funcs: Arc::new(DashMap::default()),
        }
    }

    pub fn declare_function(&mut self, sig: Signature) -> FuncRef {
        if let Some(func_ref) = self.declared_funcs.get(sig.name()) {
            *func_ref
        } else {
            let name = sig.name().to_string();
            let func = Function::new(&self.ctx, sig.clone());
            let func_ref = self.funcs.insert(func);
            self.declared_funcs.insert(name, func_ref);
            self.ctx.declared_funcs[func_ref] = sig;
            func_ref
        }
    }

    pub fn lookup_func(&self, name: &str) -> Option<FuncRef> {
        self.declared_funcs.get(name).map(|func_ref| *func_ref)
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

    pub fn build_function<C>(&mut self, func: FuncRef) -> FunctionBuilder<C>
    where
        C: FuncCursor,
    {
        let cursor = C::at_location(CursorLocation::NoWhere);
        FunctionBuilder::new(self, func, cursor)
    }

    pub fn build(self) -> Module {
        Module {
            funcs: Arc::into_inner(self.funcs).unwrap(),
            ctx: self.ctx,
        }
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.ctx.inst_set
    }
}
