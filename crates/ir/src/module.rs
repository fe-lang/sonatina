use std::sync::{Arc, RwLock};

use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};
use sonatina_triple::TargetTriple;

use super::Linkage;
use crate::{
    global_variable::GlobalVariableStore,
    isa::{Endian, Isa, TypeLayout},
    types::TypeStore,
    Function, InstSetBase, Signature, Type,
};

pub struct Module {
    pub funcs: PrimaryMap<FuncRef, Function>,
    pub ctx: ModuleCtx,
}

impl Module {
    #[doc(hidden)]
    pub fn new<T: Isa>(isa: &T) -> Self {
        Self {
            funcs: PrimaryMap::default(),
            ctx: ModuleCtx::new(isa),
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

#[derive(Clone)]
pub struct ModuleCtx {
    pub triple: TargetTriple,
    pub inst_set: &'static dyn InstSetBase,
    pub type_layout: &'static dyn TypeLayout,
    pub declared_funcs: SecondaryMap<FuncRef, Signature>,
    type_store: Arc<RwLock<TypeStore>>,
    gv_store: Arc<RwLock<GlobalVariableStore>>,
}

impl ModuleCtx {
    pub fn new<T: Isa>(isa: &T) -> Self {
        Self {
            triple: isa.triple(),
            inst_set: isa.inst_set(),
            type_layout: isa.type_layout(),
            type_store: Arc::new(RwLock::new(TypeStore::default())),
            declared_funcs: SecondaryMap::default(),
            gv_store: Arc::new(RwLock::new(GlobalVariableStore::default())),
        }
    }

    pub fn size_of(&self, ty: Type) -> usize {
        self.type_layout.size_of(ty, self)
    }

    pub fn align_of(&self, ty: Type) -> usize {
        self.type_layout.align_of(ty, self)
    }

    pub fn func_sig(&self, func: FuncRef) -> Option<&Signature> {
        self.declared_funcs.get(func)
    }

    pub fn endian(&self) -> Endian {
        self.type_layout.endian()
    }

    pub fn with_ty_store<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&TypeStore) -> R,
    {
        f(&self.type_store.read().unwrap())
    }

    pub fn with_ty_store_mut<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut TypeStore) -> R,
    {
        f(&mut self.type_store.write().unwrap())
    }

    pub fn with_gv_store<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&GlobalVariableStore) -> R,
    {
        f(&self.gv_store.read().unwrap())
    }

    pub fn with_gv_store_mut<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut GlobalVariableStore) -> R,
    {
        f(&mut self.gv_store.write().unwrap())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncRef(u32);
entity_impl!(FuncRef);
