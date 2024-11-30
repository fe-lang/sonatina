use std::sync::Arc;

use dashmap::DashMap;

use super::FunctionBuilder;
use crate::{
    func_cursor::{CursorLocation, FuncCursor},
    module::{FuncRef, FuncStore, ModuleCtx},
    Function, GlobalVariableData, GlobalVariableRef, InstSetBase, Module, Signature, Type,
};

#[derive(Clone)]
pub struct ModuleBuilder {
    pub func_store: Arc<FuncStore>,

    pub ctx: ModuleCtx,

    /// Map function name -> FuncRef to avoid duplicated declaration.
    declared_funcs: Arc<DashMap<String, FuncRef>>,
}

impl ModuleBuilder {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
            func_store: Arc::new(FuncStore::new()),
            ctx,
            declared_funcs: Arc::new(DashMap::default()),
        }
    }

    /// Create a new module builder from a module.
    /// This is used to link multiple modules to a single module for LTO.
    ///
    /// In normal use cases, it's recommended to use `ModuleBuilder::new` to
    /// create a new module.
    pub fn from_module(module: Module) -> Self {
        let store = module.func_store;
        let ctx = module.ctx;
        let declared_funcs = DashMap::new();
        for func_ref in store.funcs() {
            let name = ctx.func_sig(func_ref, |sig| sig.name().to_string());
            declared_funcs.insert(name, func_ref);
        }

        Self {
            func_store: Arc::new(store),
            ctx,
            declared_funcs: Arc::new(declared_funcs),
        }
    }

    // TODO: Return result to check duplicated func declaration.
    pub fn declare_function(&self, sig: Signature) -> FuncRef {
        if let Some(func_ref) = self.declared_funcs.get(sig.name()) {
            *func_ref
        } else {
            let name = sig.name().to_string();
            let func = Function::new(&self.ctx, sig.clone());
            let func_ref = self.func_store.insert(func);
            self.declared_funcs.insert(name, func_ref);
            self.ctx.declared_funcs.insert(func_ref, sig);
            func_ref
        }
    }

    pub fn lookup_func(&self, name: &str) -> Option<FuncRef> {
        self.declared_funcs.get(name).map(|func_ref| *func_ref)
    }

    pub fn sig<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&Signature) -> R,
    {
        self.func_store.view(func_ref, |func| f(&func.sig))
    }

    pub fn make_global(&self, global: GlobalVariableData) -> GlobalVariableRef {
        self.ctx.with_gv_store_mut(|s| s.make_gv(global))
    }

    pub fn lookup_global(&self, name: &str) -> Option<GlobalVariableRef> {
        self.ctx.with_gv_store(|s| s.gv_by_symbol(name))
    }

    pub fn declare_struct_type(&self, name: &str, fields: &[Type], packed: bool) -> Type {
        self.ctx
            .with_ty_store_mut(|s| s.make_struct(name, fields, packed))
    }

    pub fn get_struct_type(&self, name: &str) -> Option<Type> {
        self.ctx.with_ty_store(|s| s.struct_type_by_name(name))
    }

    pub fn declare_array_type(&self, elem: Type, len: usize) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_array(elem, len))
    }

    pub fn declare_func_type(&self, args: &[Type], ret_ty: Type) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_func(args, ret_ty))
    }

    pub fn ptr_type(&self, ty: Type) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_ptr(ty))
    }

    pub fn func_builder<C>(&self, func: FuncRef) -> FunctionBuilder<C>
    where
        C: FuncCursor,
    {
        let cursor = C::at_location(CursorLocation::NoWhere);
        FunctionBuilder::new(self.clone(), func, cursor)
    }

    pub fn build(self) -> Module {
        Module {
            func_store: Arc::into_inner(self.func_store).unwrap(),
            ctx: self.ctx,
        }
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.ctx.inst_set
    }
}
