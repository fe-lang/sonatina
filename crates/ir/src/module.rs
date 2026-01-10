use std::sync::{Arc, Mutex, RwLock};

use cranelift_entity::entity_impl;
use dashmap::{DashMap, ReadOnlyView};
use rayon::{iter::IntoParallelIterator, prelude::ParallelIterator};
use sonatina_triple::TargetTriple;

use crate::{
    Function, InstSetBase, Linkage, Signature, Type,
    global_variable::GlobalVariableStore,
    ir_writer::IrWrite,
    isa::{Endian, Isa, TypeLayout, TypeLayoutError},
    types::TypeStore,
};

pub struct Module {
    pub func_store: FuncStore,
    pub ctx: ModuleCtx,
}

impl Module {
    #[doc(hidden)]
    pub fn new<T: Isa>(isa: &T) -> Self {
        Self {
            func_store: FuncStore::new(),
            ctx: ModuleCtx::new(isa),
        }
    }

    pub fn funcs(&self) -> Vec<FuncRef> {
        self.func_store.funcs()
    }
}

pub struct FuncStore {
    funcs: DashMap<FuncRef, Function>,
    _guard: Mutex<()>,
}

impl FuncStore {
    pub fn update(&self, func_ref: FuncRef, func: Function) {
        self.funcs.insert(func_ref, func).unwrap();
    }

    pub fn insert(&self, func: Function) -> FuncRef {
        let _guard = self._guard.lock().unwrap();

        let func_ref = FuncRef::from_u32(self.funcs.len() as u32);
        self.funcs.insert(func_ref, func);
        func_ref
    }

    pub fn view<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&Function) -> R,
    {
        self.funcs.view(&func_ref, |_, func| f(func)).unwrap()
    }

    pub fn modify<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&mut Function) -> R,
    {
        let mut entry = self.funcs.get_mut(&func_ref).unwrap();
        f(entry.value_mut())
    }

    pub fn par_for_each<F>(&self, f: F)
    where
        F: Fn(FuncRef, &mut Function) + Sync + Send,
    {
        self.funcs
            .par_iter_mut()
            .for_each(|mut entry| f(*entry.key(), entry.value_mut()))
    }

    #[doc(hidden)]
    pub fn par_into_for_each<F>(self, f: F)
    where
        F: Fn(FuncRef, Function) + Sync + Send,
    {
        self.funcs
            .into_par_iter()
            .for_each(|(func_ref, function)| f(func_ref, function))
    }

    pub fn funcs(&self) -> Vec<FuncRef> {
        let _guard = self._guard.lock().unwrap();
        let len = self.funcs.len();
        (0..len).map(|n| FuncRef::from_u32(n as u32)).collect()
    }

    pub fn into_read_only(self) -> RoFuncStore {
        self.funcs.into_read_only()
    }

    pub fn from_read_only(ro_fs: RoFuncStore) -> Self {
        Self {
            funcs: ro_fs.into_inner(),
            _guard: Mutex::new(()),
        }
    }

    pub(crate) fn new() -> Self {
        Self {
            funcs: DashMap::new(),
            _guard: Mutex::new(()),
        }
    }
}

pub type RoFuncStore = ReadOnlyView<FuncRef, Function>;

#[derive(Clone)]
pub struct ModuleCtx {
    pub triple: TargetTriple,
    pub inst_set: &'static dyn InstSetBase,
    pub type_layout: &'static dyn TypeLayout,
    pub declared_funcs: Arc<DashMap<FuncRef, Signature>>,
    type_store: Arc<RwLock<TypeStore>>,
    gv_store: Arc<RwLock<GlobalVariableStore>>,
}
impl AsRef<ModuleCtx> for ModuleCtx {
    fn as_ref(&self) -> &ModuleCtx {
        self
    }
}

impl ModuleCtx {
    pub fn new<T: Isa>(isa: &T) -> Self {
        Self {
            triple: isa.triple(),
            inst_set: isa.inst_set(),
            type_layout: isa.type_layout(),
            type_store: Arc::new(RwLock::new(TypeStore::default())),
            declared_funcs: Arc::new(DashMap::new()),
            gv_store: Arc::new(RwLock::new(GlobalVariableStore::default())),
        }
    }

    pub fn size_of(&self, ty: Type) -> Result<usize, TypeLayoutError> {
        self.type_layout.size_of(ty, self)
    }

    pub fn align_of(&self, ty: Type) -> Result<usize, TypeLayoutError> {
        self.type_layout.align_of(ty, self)
    }

    pub fn size_of_unchecked(&self, ty: Type) -> usize {
        self.size_of(ty).unwrap()
    }

    pub fn align_of_unchecked(&self, ty: Type) -> usize {
        self.align_of(ty).unwrap()
    }

    pub fn func_sig<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&Signature) -> R,
    {
        self.declared_funcs
            .view(&func_ref, |_, sig| f(sig))
            .unwrap()
    }

    pub fn func_linkage(&self, func_ref: FuncRef) -> Linkage {
        self.func_sig(func_ref, |sig| sig.linkage())
    }

    /// Updated the function signature with the given linkage.
    ///
    /// # Panics
    /// Panics if the function reference is not declared.
    pub fn update_func_linkage(&self, func_ref: FuncRef, linkage: Linkage) {
        self.declared_funcs
            .get_mut(&func_ref)
            .unwrap()
            .value_mut()
            .update_linkage(linkage);
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

impl FuncRef {
    pub fn as_ptr_ty(self, ctx: &ModuleCtx) -> Type {
        ctx.func_sig(self, |sig| sig.func_ptr_type(ctx))
    }
}

impl<Ctx> IrWrite<Ctx> for FuncRef
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> std::io::Result<()>
    where
        W: std::io::Write + ?Sized,
    {
        ctx.as_ref()
            .func_sig(*self, |sig| write!(w, "%{}", sig.name()))
    }
}
