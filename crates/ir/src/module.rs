use std::sync::{Arc, Mutex, RwLock};

use bitflags::bitflags;
use cranelift_entity::entity_impl;
use dashmap::{DashMap, ReadOnlyView};
use rayon::{iter::IntoParallelIterator, prelude::ParallelIterator};
use rustc_hash::FxHashMap;
use sonatina_triple::TargetTriple;

use crate::{
    AddressSpaceInfo, FuncEffectSummary, Function, InstSetBase, Linkage, Signature, Type,
    global_variable::GlobalVariableStore,
    inst::SideEffect,
    ir_writer::IrWrite,
    isa::{Endian, Isa, TypeLayout, TypeLayoutError},
    object::Object,
    types::{CompoundType, TypeStore},
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

bitflags! {
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub struct FuncHints: u16 {
        const NOINLINE = 1 << 0;
        const ALWAYSINLINE = 1 << 1;
        const INLINEHINT = 1 << 2;
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum InlineHint {
    #[default]
    Auto,
    Inline,
    Always,
    Never,
}

impl FuncHints {
    const INLINE_MASK_BITS: u16 =
        Self::NOINLINE.bits() | Self::ALWAYSINLINE.bits() | Self::INLINEHINT.bits();

    fn inline_bits(self) -> Self {
        Self::from_bits_retain(self.bits() & Self::INLINE_MASK_BITS)
    }

    pub fn inline_hint(self) -> InlineHint {
        match self.inline_bits() {
            hints if hints.is_empty() => InlineHint::Auto,
            hints if hints == Self::INLINEHINT => InlineHint::Inline,
            hints if hints == Self::ALWAYSINLINE => InlineHint::Always,
            hints if hints == Self::NOINLINE => InlineHint::Never,
            hints => {
                debug_assert!(
                    false,
                    "conflicting inline hints stored in FuncHints: {hints:?}"
                );
                if hints.contains(Self::NOINLINE) {
                    InlineHint::Never
                } else if hints.contains(Self::ALWAYSINLINE) {
                    InlineHint::Always
                } else {
                    InlineHint::Inline
                }
            }
        }
    }

    pub fn with_inline_hint(mut self, hint: InlineHint) -> Self {
        self.remove(Self::from_bits_retain(Self::INLINE_MASK_BITS));
        match hint {
            InlineHint::Auto => {}
            InlineHint::Inline => self.insert(Self::INLINEHINT),
            InlineHint::Always => self.insert(Self::ALWAYSINLINE),
            InlineHint::Never => self.insert(Self::NOINLINE),
        }
        self
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

    pub fn restore(&self, func_ref: FuncRef, func: Function) {
        let _guard = self._guard.lock().unwrap();
        let prev = self.funcs.insert(func_ref, func);
        assert!(
            prev.is_none(),
            "restore expected vacant slot for {func_ref:?}"
        );
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
    address_spaces: &'static dyn AddressSpaceInfo,
    pub declared_funcs: Arc<DashMap<FuncRef, Signature>>,
    func_effects: Arc<RwLock<FxHashMap<FuncRef, FuncEffectSummary>>>,
    func_hints: Arc<RwLock<FxHashMap<FuncRef, FuncHints>>>,
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
            address_spaces: isa.address_spaces(),
            type_store: Arc::new(RwLock::new(TypeStore::default())),
            declared_funcs: Arc::new(DashMap::new()),
            func_effects: Arc::new(RwLock::new(FxHashMap::default())),
            func_hints: Arc::new(RwLock::new(FxHashMap::default())),
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

    pub fn aggregate_len(&self, aggregate_ty: Type) -> Option<usize> {
        let Type::Compound(cmpd) = aggregate_ty else {
            return None;
        };

        match self.with_ty_store(|store| store.resolve_compound(cmpd).clone()) {
            CompoundType::Array { len, .. } => Some(len),
            CompoundType::Struct(s) => (!s.packed).then_some(s.fields.len()),
            CompoundType::Enum(_)
            | CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => None,
        }
    }

    pub fn aggregate_elem_offset(&self, aggregate_ty: Type, idx: usize) -> Option<(usize, Type)> {
        let Type::Compound(cmpd) = aggregate_ty else {
            return None;
        };

        match self.with_ty_store(|store| store.resolve_compound(cmpd).clone()) {
            CompoundType::Array { elem, len } => {
                (idx < len).then_some((self.size_of(elem).ok()?.checked_mul(idx)?, elem))
            }
            CompoundType::Struct(s) => {
                if s.packed {
                    return None;
                }

                let &field_ty = s.fields.get(idx)?;
                let mut offset = 0usize;
                for &ty in s.fields.iter().take(idx) {
                    offset = align_to(offset, self.align_of(ty).ok()?)?;
                    offset = offset.checked_add(self.size_of(ty).ok()?)?;
                }
                offset = align_to(offset, self.align_of(field_ty).ok()?)?;
                Some((offset, field_ty))
            }
            CompoundType::Enum(_)
            | CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => None,
        }
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
        self.func_effects
            .read()
            .unwrap()
            .get(&func_ref)
            .map(FuncEffectSummary::to_legacy_attrs)
            .unwrap_or_default()
    }

    pub fn has_func_attrs(&self, func_ref: FuncRef) -> bool {
        self.has_func_effects(func_ref)
    }

    pub fn set_all_func_attrs(&self, new: FxHashMap<FuncRef, FuncAttrs>) {
        let effects = new
            .iter()
            .map(|(&func_ref, &attrs)| (func_ref, FuncEffectSummary::from_legacy_attrs(attrs)))
            .collect();
        self.set_all_func_effects(effects);
    }

    pub fn set_func_attrs(&self, func_ref: FuncRef, attrs: FuncAttrs) {
        self.set_func_effects(func_ref, FuncEffectSummary::from_legacy_attrs(attrs));
    }

    pub fn clear_func_attrs(&self, func_ref: FuncRef) {
        self.clear_func_effects(func_ref);
    }

    pub fn func_effects(&self, func_ref: FuncRef) -> FuncEffectSummary {
        self.func_effects
            .read()
            .unwrap()
            .get(&func_ref)
            .cloned()
            .unwrap_or_else(FuncEffectSummary::unknown_call)
    }

    pub fn has_func_effects(&self, func_ref: FuncRef) -> bool {
        self.func_effects.read().unwrap().contains_key(&func_ref)
    }

    pub fn set_all_func_effects(&self, new: FxHashMap<FuncRef, FuncEffectSummary>) {
        *self.func_effects.write().unwrap() = new;
    }

    pub fn set_func_effects(&self, func_ref: FuncRef, effects: FuncEffectSummary) {
        self.func_effects.write().unwrap().insert(func_ref, effects);
    }

    pub fn clear_func_effects(&self, func_ref: FuncRef) {
        self.func_effects.write().unwrap().remove(&func_ref);
    }

    pub fn call_side_effect(&self, func_ref: FuncRef) -> SideEffect {
        self.func_effects(func_ref).to_legacy_side_effect()
    }

    pub fn address_spaces(&self) -> &'static dyn AddressSpaceInfo {
        self.address_spaces
    }

    pub fn func_hints(&self, func_ref: FuncRef) -> FuncHints {
        self.func_hints
            .read()
            .unwrap()
            .get(&func_ref)
            .copied()
            .unwrap_or_default()
    }

    pub fn has_func_hints(&self, func_ref: FuncRef) -> bool {
        self.func_hints.read().unwrap().contains_key(&func_ref)
    }

    pub fn inline_hint(&self, func_ref: FuncRef) -> InlineHint {
        self.func_hints(func_ref).inline_hint()
    }

    pub fn set_all_func_hints(&self, new: FxHashMap<FuncRef, FuncHints>) {
        *self.func_hints.write().unwrap() = new;
    }

    pub fn set_func_hints(&self, func_ref: FuncRef, hints: FuncHints) {
        self.func_hints
            .write()
            .unwrap()
            .entry(func_ref)
            .and_modify(|entry| *entry |= hints)
            .or_insert(hints);
    }

    pub fn set_inline_hint(&self, func_ref: FuncRef, hint: InlineHint) {
        let mut hints = self.func_hints.write().unwrap();
        let remove = {
            let entry = hints.entry(func_ref).or_default();
            *entry = entry.with_inline_hint(hint);
            entry.is_empty()
        };
        if remove {
            hints.remove(&func_ref);
        }
    }

    pub fn clear_func_hints(&self, func_ref: FuncRef) {
        self.func_hints.write().unwrap().remove(&func_ref);
    }

    pub fn clear_inline_hint(&self, func_ref: FuncRef) {
        let mut hints = self.func_hints.write().unwrap();
        let remove = if let Some(entry) = hints.get_mut(&func_ref) {
            *entry = entry.with_inline_hint(InlineHint::Auto);
            entry.is_empty()
        } else {
            false
        };
        if remove {
            hints.remove(&func_ref);
        }
    }

    pub fn clear_func_metadata(&self, func_ref: FuncRef) {
        self.clear_func_attrs(func_ref);
        self.clear_func_hints(func_ref);
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

fn align_to(offset: usize, align: usize) -> Option<usize> {
    if align <= 1 {
        return Some(offset);
    }
    if !align.is_power_of_two() {
        return None;
    }

    let aligned = offset.checked_add(align.checked_sub(1)?)?;
    Some(aligned & !(align - 1))
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
