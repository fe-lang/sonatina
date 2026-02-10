use std::sync::{Arc, Mutex, RwLock};

use bitflags::bitflags;
use cranelift_entity::{SecondaryMap, entity_impl};
use dashmap::{DashMap, ReadOnlyView};
use rayon::{iter::IntoParallelIterator, prelude::ParallelIterator};
use rustc_hash::FxHashMap;
use sonatina_triple::TargetTriple;

use crate::{
    Function, InstSetBase, Linkage, Signature, Type,
    global_variable::GlobalVariableStore,
    ir_writer::IrWrite,
    isa::{Endian, Isa, TypeLayout, TypeLayoutError},
    object::Object,
    types::TypeStore,
};

bitflags! {
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub struct FuncAttrs: u8 {
        const MEM_READ = 1 << 0;
        const MEM_WRITE = 1 << 1;
        const NORETURN = 1 << 2;
        const WILLRETURN = 1 << 3;
        const WILLTERMINATE = 1 << 4;
    }
}

pub struct Module {
    pub func_store: FuncStore,
    pub ctx: ModuleCtx,
    pub objects: FxHashMap<String, Object>,
}

impl Module {
    #[doc(hidden)]
    pub fn new<T: Isa>(isa: &T) -> Self {
        Self {
            func_store: FuncStore::new(),
            ctx: ModuleCtx::new(isa),
            objects: FxHashMap::default(),
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

        let mut next = self.funcs.len() as u32;
        while self.funcs.contains_key(&FuncRef::from_u32(next)) {
            next += 1;
        }

        let func_ref = FuncRef::from_u32(next);
        self.funcs.insert(func_ref, func);
        func_ref
    }

    pub fn remove(&self, func_ref: FuncRef) -> Option<Function> {
        let _guard = self._guard.lock().unwrap();
        self.funcs.remove(&func_ref).map(|(_, func)| func)
    }

    pub fn view<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&Function) -> R,
    {
        self.funcs.view(&func_ref, |_, func| f(func)).unwrap()
    }

    pub fn try_view<F, R>(&self, func_ref: FuncRef, f: F) -> Option<R>
    where
        F: FnOnce(&Function) -> R,
    {
        self.funcs.view(&func_ref, |_, func| f(func))
    }

    pub fn modify<F, R>(&self, func_ref: FuncRef, f: F) -> R
    where
        F: FnOnce(&mut Function) -> R,
    {
        let mut entry = self.funcs.get_mut(&func_ref).unwrap();
        f(entry.value_mut())
    }

    pub fn try_modify<F, R>(&self, func_ref: FuncRef, f: F) -> Option<R>
    where
        F: FnOnce(&mut Function) -> R,
    {
        let mut entry = self.funcs.get_mut(&func_ref)?;
        Some(f(entry.value_mut()))
    }

    pub fn contains(&self, func_ref: FuncRef) -> bool {
        self.funcs.contains_key(&func_ref)
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
        let mut funcs: Vec<_> = self.funcs.iter().map(|entry| *entry.key()).collect();
        funcs.sort_unstable();
        funcs
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
    func_attrs: Arc<RwLock<SecondaryMap<FuncRef, FuncAttrs>>>,
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
            func_attrs: Arc::new(RwLock::new(SecondaryMap::new())),
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

    pub fn get_sig(&self, func_ref: FuncRef) -> Option<Signature> {
        self.declared_funcs.view(&func_ref, |_, sig| sig.clone())
    }

    pub fn func_linkage(&self, func_ref: FuncRef) -> Linkage {
        self.func_sig(func_ref, |sig| sig.linkage())
    }

    pub fn func_attrs(&self, func_ref: FuncRef) -> FuncAttrs {
        self.func_attrs
            .read()
            .unwrap()
            .get(func_ref)
            .copied()
            .unwrap_or_default()
    }

    pub fn set_all_func_attrs(&self, new: SecondaryMap<FuncRef, FuncAttrs>) {
        *self.func_attrs.write().unwrap() = new;
    }

    pub fn set_func_attrs(&self, func_ref: FuncRef, attrs: FuncAttrs) {
        self.func_attrs.write().unwrap()[func_ref] = attrs;
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
