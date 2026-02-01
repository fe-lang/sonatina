use std::sync::Arc;

use dashmap::DashMap;
use rustc_hash::FxHashMap;
use sonatina_triple::TargetTriple;

use super::FunctionBuilder;
use crate::{
    Function, GlobalVariableData, GlobalVariableRef, InstSetBase, Module, Object, Signature, Type,
    func_cursor::{CursorLocation, FuncCursor},
    module::{FuncRef, FuncStore, ModuleCtx},
    types::{CompoundType, CompoundTypeRef},
};

#[derive(Clone)]
pub struct ModuleBuilder {
    #[doc(hidden)]
    pub func_store: Arc<FuncStore>,

    pub ctx: ModuleCtx,

    pub objects: FxHashMap<String, Object>,

    /// Map function name -> FuncRef to avoid duplicated declaration.
    declared_funcs: Arc<DashMap<String, FuncRef>>,
}

#[derive(Debug, Clone)]
pub enum BuilderError {
    ConflictingFunctionDeclaration,
    DuplicateObjectDefinition { name: String },
}

impl std::fmt::Display for BuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConflictingFunctionDeclaration => {
                write!(f, "conflicting function declaration")
            }
            Self::DuplicateObjectDefinition { name } => {
                write!(f, "duplicate object definition: {name}")
            }
        }
    }
}

impl std::error::Error for BuilderError {}

impl ModuleBuilder {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
            func_store: Arc::new(FuncStore::new()),
            ctx,
            objects: FxHashMap::default(),
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
        let objects = module.objects;
        let declared_funcs = DashMap::new();
        for func_ref in store.funcs() {
            let name = ctx.func_sig(func_ref, |sig| sig.name().to_string());
            declared_funcs.insert(name, func_ref);
        }

        Self {
            func_store: Arc::new(store),
            ctx,
            objects,
            declared_funcs: Arc::new(declared_funcs),
        }
    }

    pub fn triple(&self) -> TargetTriple {
        self.ctx.triple
    }

    pub fn declare_function(&self, sig: Signature) -> Result<FuncRef, BuilderError> {
        if let Some(func_ref) = self.declared_funcs.get(sig.name()) {
            return self.ctx.func_sig(*func_ref, |func_sig| {
                if func_sig.args() == sig.args() && func_sig.ret_ty() == sig.ret_ty() {
                    Ok(*func_ref)
                } else {
                    Err(BuilderError::ConflictingFunctionDeclaration)
                }
            });
        }
        let func = Function::new(&self.ctx, &sig);
        let func_ref = self.func_store.insert(func);
        self.declared_funcs.insert(sig.name().to_string(), func_ref);
        self.ctx.declared_funcs.insert(func_ref, sig);
        Ok(func_ref)
    }

    pub fn declare_gv(&self, global: GlobalVariableData) -> GlobalVariableRef {
        self.ctx.with_gv_store_mut(|s| s.make_gv(global))
    }

    pub fn declare_object(&mut self, object: Object) -> Result<(), BuilderError> {
        let name = object.name.0.to_string();
        if self.objects.contains_key(&name) {
            return Err(BuilderError::DuplicateObjectDefinition { name });
        }
        self.objects.insert(name, object);
        Ok(())
    }

    pub fn lookup_object(&self, name: &str) -> Option<&Object> {
        self.objects.get(name)
    }

    pub fn declare_struct_type(&self, name: &str, fields: &[Type], packed: bool) -> Type {
        self.ctx
            .with_ty_store_mut(|s| s.make_struct(name, fields, packed))
    }

    pub fn declare_array_type(&self, elem: Type, len: usize) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_array(elem, len))
    }

    pub fn declare_func_type(&self, args: &[Type], ret_ty: Type) -> Type {
        self.ctx.with_ty_store_mut(|s| s.make_func(args, ret_ty))
    }

    pub fn lookup_func(&self, name: &str) -> Option<FuncRef> {
        self.declared_funcs.get(name).map(|func_ref| *func_ref)
    }

    pub fn lookup_gv(&self, name: &str) -> Option<GlobalVariableRef> {
        self.ctx.with_gv_store(|s| s.lookup_gv(name))
    }

    pub fn lookup_struct(&self, name: &str) -> Option<CompoundTypeRef> {
        self.ctx.with_ty_store(|s| s.lookup_struct(name))
    }

    pub fn sig<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&Signature) -> R,
    {
        self.ctx.func_sig(func_ref, f)
    }

    /// Update the fields of a struct type. This should be used to update the
    /// fields of a struct type especially when the struct type definition
    /// is involved in an indirect recursive type.
    ///
    /// The corresponding [`Type`] will automatically point to the updated
    /// struct, and old struct definition is removed from the module.
    ///
    /// # Panic
    /// This function panics if the struct type with the given name is not
    /// found.
    pub fn update_struct_fields(&self, name: &str, fields: &[Type]) {
        self.ctx
            .with_ty_store_mut(|s| s.update_struct_fields(name, fields));
    }

    #[doc(hidden)]
    pub fn make_compound(&self, cmpd: CompoundType) -> CompoundTypeRef {
        self.ctx.with_ty_store_mut(|s| s.make_compound(cmpd))
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
            objects: self.objects,
        }
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.ctx.inst_set
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Linkage, ObjectName, builder::test_util::test_module_builder, types::Type}; //, Signature};

    #[test]
    fn test_declare_function_success() {
        let builder = test_module_builder();
        let sig = Signature::new("foo", Linkage::Public, &[], Type::Unit);

        let result = builder.declare_function(sig.clone());
        assert!(result.is_ok());

        // Declaring again with same sig should succeed
        let result2 = builder.declare_function(sig);
        assert!(result2.is_ok());
    }

    #[test]
    fn test_declare_function_conflict() {
        let builder = test_module_builder();

        let sig1 = Signature::new("foo", Linkage::Public, &[Type::I32], Type::I32);
        let sig2 = Signature::new("foo", Linkage::Public, &[Type::I64], Type::I64);

        builder.declare_function(sig1).unwrap();
        let result = builder.declare_function(sig2);

        match result {
            Err(BuilderError::ConflictingFunctionDeclaration) => (),
            _ => panic!("Expected conflicting function declaration error"),
        }
    }

    #[test]
    fn test_declare_object_success() {
        let mut builder = test_module_builder();

        let object = Object {
            name: ObjectName("Factory".into()),
            sections: vec![],
        };

        let result = builder.declare_object(object);
        assert!(result.is_ok());
        assert!(builder.lookup_object("Factory").is_some());
    }

    #[test]
    fn test_declare_object_duplicate_should_fail() {
        let mut builder = test_module_builder();

        let object1 = Object {
            name: ObjectName("Factory".into()),
            sections: vec![],
        };
        let object2 = Object {
            name: ObjectName("Factory".into()),
            sections: vec![],
        };

        builder.declare_object(object1).unwrap();
        let result = builder.declare_object(object2);

        assert!(
            matches!(result, Err(BuilderError::DuplicateObjectDefinition { name }) if name == "Factory"),
            "Expected DuplicateObjectDefinition error for object 'Factory'"
        );
    }
}
