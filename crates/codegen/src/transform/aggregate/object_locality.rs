use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, InstId, Module, Type, ValueId,
    inst::{cast, control_flow, data, evm},
    module::{FuncRef, ModuleCtx},
    types::EnumVariantRef,
};
use std::ops::ControlFlow;

use super::{
    ObjectEffectSummaryMap, compute_object_effect_summaries, object_abi::OutputBufferContract,
    shape,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RootInit {
    UndefFresh,
    LoadLiveIn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LocalObjectArgInfo {
    Borrowed,
    Output(OutputBufferContract),
}

impl LocalObjectArgInfo {
    pub(crate) fn output_contract(
        self,
        function: &Function,
        index: usize,
    ) -> Option<OutputBufferContract> {
        match self {
            Self::Output(contract) if contract.matches(function, index) => Some(contract),
            _ => None,
        }
    }

    pub(crate) fn is_valid_for(self, function: &Function, index: usize) -> bool {
        match self {
            Self::Borrowed => function.arg_values.get(index).is_some_and(|&argument| {
                function.dfg.value_ty(argument).is_obj_ref(function.ctx())
            }),
            Self::Output(contract) => contract.matches(function, index),
        }
    }

    pub(crate) fn init(self, function: &Function, index: usize) -> Option<RootInit> {
        self.is_valid_for(function, index).then_some(match self {
            Self::Borrowed => RootInit::LoadLiveIn,
            Self::Output(_) => RootInit::UndefFresh,
        })
    }
}

pub(crate) type LocalObjectArgMap = FxHashMap<FuncRef, FxHashMap<usize, LocalObjectArgInfo>>;
pub(crate) type LocalObjectArgs = FxHashMap<FuncRef, FxHashSet<usize>>;

pub(crate) enum SpecialObjectUse<'a> {
    MaterializeStack(Option<ValueId>),
    Call {
        inst: sonatina_ir::InstId,
        value: ValueId,
        call: &'a control_flow::Call,
    },
    Return {
        value: ValueId,
        ret: &'a control_flow::Return,
    },
    /// A reference into the object enters an SSA aggregate or the memory of a
    /// local allocation. Continuing follows it along its access path, through
    /// any nesting of aggregates and allocations: extracting or loading the
    /// carrying position recovers the reference, and the uses of each
    /// allocation that holds it count as uses of the object.
    Carry,
    Unknown,
}

/// One step from a walked value toward a reference into the object.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Step {
    /// A struct field or array element, of an SSA aggregate or in memory;
    /// `None` when the walk cannot read the index.
    Field(Option<u32>),
    /// A field of an enum variant, of an SSA enum or in memory.
    Variant(EnumVariantRef, Option<u32>),
    /// The memory a reference designates.
    Deref,
}

impl Step {
    /// Whether a projection through `self` can reach the position of `other`.
    /// Steps of different kinds never meet in well-typed IR, so they
    /// conservatively match.
    fn may_match(self, other: Self) -> bool {
        let indices_match =
            |lhs: Option<u32>, rhs: Option<u32>| lhs.is_none() || rhs.is_none() || lhs == rhs;
        match (self, other) {
            (Self::Field(lhs), Self::Field(rhs)) => indices_match(lhs, rhs),
            (Self::Variant(lhs_variant, lhs), Self::Variant(rhs_variant, rhs)) => {
                lhs_variant == rhs_variant && indices_match(lhs, rhs)
            }
            _ => true,
        }
    }
}

/// The steps from a walked value to a reference into the object; empty for
/// such a reference itself.
type Path = SmallVec<[Step; 4]>;

/// A longer path is reported as an unknown use, which bounds the walk.
const MAX_PATH_STEPS: usize = 16;

// This walks the full module and must run before any `func_store.modify(...)` loop.
pub(crate) fn collect_local_object_arg_info(module: &Module) -> LocalObjectArgMap {
    let object_effects = compute_object_effect_summaries(module);
    collect_local_object_arg_info_with_effects(module, &object_effects)
}

pub(crate) fn collect_local_object_arg_info_with_effects(
    module: &Module,
    object_effects: &ObjectEffectSummaryMap,
) -> LocalObjectArgMap {
    module
        .funcs()
        .into_iter()
        .filter_map(|func| {
            let args = local_object_arg_info(module, func, object_effects);
            (!args.is_empty()).then_some((func, args))
        })
        .collect()
}

pub(crate) fn local_object_arg_info(
    module: &Module,
    func: FuncRef,
    object_effects: &ObjectEffectSummaryMap,
) -> FxHashMap<usize, LocalObjectArgInfo> {
    let mut args = FxHashMap::default();
    if let Some(sig) = module.ctx.get_sig(func)
        && let Some(summary) = object_effects.get(&func)
    {
        for (idx, &root_ty) in sig.args().iter().enumerate() {
            if root_ty.is_obj_ref(&module.ctx)
                && summary
                    .arg_effects
                    .get(idx)
                    .is_some_and(|effect| effect.local_only)
                && !summary
                    .captures
                    .iter()
                    .any(|capture| capture.src_arg == idx)
            {
                args.insert(idx, LocalObjectArgInfo::Borrowed);
            }
        }
    }
    args
}

pub(crate) fn collect_local_object_args(module: &Module) -> LocalObjectArgs {
    info_to_local_object_args(module, &collect_local_object_arg_info(module))
}

pub(crate) fn info_to_local_object_args(
    module: &Module,
    local_object_args: &LocalObjectArgMap,
) -> LocalObjectArgs {
    module
        .funcs()
        .into_iter()
        .filter_map(|func| {
            let args = local_object_args.get(&func)?;
            let valid = module.func_store.view(func, |function| {
                args.iter()
                    .filter_map(|(&index, info)| {
                        info.is_valid_for(function, index).then_some(index)
                    })
                    .collect()
            });
            Some((func, valid))
        })
        .collect()
}

pub(crate) fn merge_local_object_arg_info(
    module: &Module,
    local_object_args: &mut LocalObjectArgMap,
    extra: &LocalObjectArgMap,
) {
    for func in module.funcs() {
        if let Some(args) = extra.get(&func) {
            module.func_store.view(func, |function| {
                local_object_args
                    .entry(func)
                    .or_default()
                    .extend(args.iter().filter_map(|(&index, &info)| {
                        info.is_valid_for(function, index).then_some((index, info))
                    }));
            });
        }
    }
}

pub(crate) fn call_passes_object_to_local_args(
    ctx: &ModuleCtx,
    call: &control_flow::Call,
    value: ValueId,
    value_ty: Type,
    local_object_args: &LocalObjectArgs,
) -> bool {
    let Some(sig) = ctx.get_sig(*call.callee()) else {
        return false;
    };
    let Some(local_args) = local_object_args.get(call.callee()) else {
        return false;
    };

    let mut saw_value = false;
    for (idx, &arg) in call.args().iter().enumerate() {
        if arg != value {
            continue;
        }
        saw_value = true;
        if sig.args().get(idx) != Some(&value_ty) || !local_args.contains(&idx) {
            return false;
        }
    }

    saw_value
}

fn call_passes_object_to_local_arg_info(
    ctx: &ModuleCtx,
    call: &control_flow::Call,
    value: ValueId,
    value_ty: Type,
    local_object_args: &LocalObjectArgMap,
) -> bool {
    let Some(sig) = ctx.get_sig(*call.callee()) else {
        return false;
    };
    let Some(local_args) = local_object_args.get(call.callee()) else {
        return false;
    };

    let mut saw_value = false;
    for (idx, &arg) in call.args().iter().enumerate() {
        if arg != value {
            continue;
        }
        saw_value = true;
        if sig.args().get(idx) != Some(&value_ty) || !local_args.contains_key(&idx) {
            return false;
        }
    }

    saw_value
}

pub(crate) fn object_root_stays_local(
    function: &Function,
    root: ValueId,
    local_object_args: &LocalObjectArgMap,
    allow_return_root: bool,
) -> bool {
    object_root_stays_local_with(
        function,
        root,
        local_object_args,
        |value| value == root,
        allow_return_root,
    )
}

pub(crate) fn object_root_stays_local_with_effects(
    function: &Function,
    root: ValueId,
    object_effects: &ObjectEffectSummaryMap,
    mut is_allowed_root_value: impl FnMut(ValueId) -> bool,
    allow_return_root: bool,
    allow_carry: bool,
) -> bool {
    walk_object_root_uses_with_effects(function, root, object_effects, |special| match special {
        SpecialObjectUse::MaterializeStack(Some(ptr))
            if raw_pointer_stays_local(function, ptr, true) =>
        {
            ControlFlow::Continue(())
        }
        SpecialObjectUse::Carry if allow_carry => ControlFlow::Continue(()),
        SpecialObjectUse::Return { value, ret }
            if allow_return_root
                && is_allowed_root_value(value)
                && ret.returns_single()
                && ret.arg() == Some(&value) =>
        {
            ControlFlow::Continue(())
        }
        SpecialObjectUse::Call { inst, value, call }
            if is_allowed_root_value(value)
                && call_root_preserves_locality(
                    function,
                    inst,
                    call,
                    value,
                    object_effects,
                    &mut is_allowed_root_value,
                ) =>
        {
            ControlFlow::Continue(())
        }
        _ => ControlFlow::Break(()),
    })
    .is_none()
}

pub(crate) fn object_root_stays_local_with(
    function: &Function,
    root: ValueId,
    local_object_args: &LocalObjectArgMap,
    mut is_allowed_root_value: impl FnMut(ValueId) -> bool,
    allow_return_root: bool,
) -> bool {
    walk_object_root_uses(function, root, |special| match special {
        SpecialObjectUse::MaterializeStack(Some(ptr))
            if raw_pointer_stays_local(function, ptr, true) =>
        {
            ControlFlow::Continue(())
        }
        SpecialObjectUse::Return { value, ret }
            if allow_return_root
                && is_allowed_root_value(value)
                && ret.returns_single()
                && ret.arg() == Some(&value) =>
        {
            ControlFlow::Continue(())
        }
        SpecialObjectUse::Call { value, call, .. }
            if is_allowed_root_value(value)
                && call_passes_object_to_local_arg_info(
                    function.ctx(),
                    call,
                    value,
                    function.dfg.value_ty(value),
                    local_object_args,
                ) =>
        {
            ControlFlow::Continue(())
        }
        _ => ControlFlow::Break(()),
    })
    .is_none()
}

/// Whether a raw pointer to an object, `root`, and the pointers derived from
/// it only address the object. Without `allow_reads` it must not be read
/// through either, as when the object holds a reference the caller tracks.
pub(crate) fn raw_pointer_stays_local(
    function: &Function,
    root: ValueId,
    allow_reads: bool,
) -> bool {
    let mut worklist = vec![root];
    let mut seen = FxHashSet::default();

    while let Some(value) = worklist.pop() {
        if !seen.insert(value) {
            continue;
        }

        for &user in function.dfg.users(value) {
            if !function.layout.is_inst_inserted(user) {
                continue;
            }

            if let Some(gep) = function.dfg.downcast::<&data::Gep>(user)
                && gep.values().first() == Some(&value)
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(bitcast) = function.dfg.downcast::<&cast::Bitcast>(user)
                && *bitcast.from() == value
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(phi) = function.dfg.downcast::<&control_flow::Phi>(user)
                && phi.args().iter().any(|(arg, _)| *arg == value)
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(load) = function.dfg.downcast::<&data::Mload>(user)
                && *load.addr() == value
            {
                if allow_reads {
                    continue;
                }
                return false;
            }

            if let Some(store) = function.dfg.downcast::<&data::Mstore>(user) {
                if *store.addr() == value {
                    continue;
                }
                if *store.value() == value {
                    return false;
                }
            }

            if let Some(copy) = function.dfg.downcast::<&evm::EvmCodeCopy>(user) {
                if *copy.dst_addr() == value && *copy.code_offset() != value && *copy.len() != value
                {
                    continue;
                }
                return false;
            }

            if let Some(copy) = function.dfg.downcast::<&evm::EvmMcopy>(user) {
                if (*copy.dest() == value || *copy.addr() == value)
                    && (allow_reads || *copy.addr() != value)
                    && *copy.len() != value
                {
                    continue;
                }
                return false;
            }

            if function.dfg.downcast::<&control_flow::Call>(user).is_some()
                || function
                    .dfg
                    .downcast::<&control_flow::Return>(user)
                    .is_some_and(|ret| ret.args().iter().any(|arg| *arg == value))
                || function
                    .dfg
                    .downcast::<&cast::PtrToInt>(user)
                    .is_some_and(|ptr_to_int| *ptr_to_int.from() == value)
            {
                return false;
            }

            return false;
        }
    }

    true
}

pub(crate) fn walk_object_root_uses<T>(
    function: &Function,
    root: ValueId,
    mut on_special: impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
) -> Option<T> {
    walk_object_root_uses_impl(function, root, None, &mut on_special)
}

pub(crate) fn walk_object_root_uses_with_effects<T>(
    function: &Function,
    root: ValueId,
    object_effects: &ObjectEffectSummaryMap,
    mut on_special: impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
) -> Option<T> {
    walk_object_root_uses_impl(function, root, Some(object_effects), &mut on_special)
}

fn walk_object_root_uses_impl<T>(
    function: &Function,
    root: ValueId,
    object_effects: Option<&ObjectEffectSummaryMap>,
    on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
) -> Option<T> {
    let mut worklist = vec![(root, Path::new())];
    let mut seen = FxHashSet::default();

    while let Some((value, path)) = worklist.pop() {
        if !seen.insert((value, path.clone())) {
            continue;
        }

        for &user in function.dfg.users(value) {
            if !function.layout.is_inst_inserted(user) {
                continue;
            }
            let walk = Walk {
                function,
                user,
                value,
                path: &path,
            };
            if let ControlFlow::Break(result) =
                walk.walk_use(object_effects, &mut worklist, on_special)
            {
                return Some(result);
            }
        }
    }

    None
}

/// Whether the reference `value`, which `inst` packs into an SSA aggregate,
/// stays packed: no use recovers it, by extracting it or by loading it from a
/// local allocation that holds the aggregate, and neither the aggregate nor
/// such an allocation leaves the function.
pub(crate) fn packed_reference_stays_packed(
    function: &Function,
    inst: InstId,
    value: ValueId,
) -> bool {
    let mut worklist = Vec::new();
    let mut packed = |special: SpecialObjectUse<'_>| match special {
        SpecialObjectUse::Carry => ControlFlow::Continue(()),
        _ => ControlFlow::Break(()),
    };
    let pack = Walk {
        function,
        user: inst,
        value,
        path: &Path::new(),
    };
    if pack.walk_use(None, &mut worklist, &mut packed).is_break() {
        return false;
    }
    let mut seen = FxHashSet::default();
    while let Some((value, path)) = worklist.pop() {
        // An empty path leads to the reference itself.
        if path.is_empty() {
            return false;
        }
        if !seen.insert((value, path.clone())) {
            continue;
        }
        for &user in function.dfg.users(value) {
            let walk = Walk {
                function,
                user,
                value,
                path: &path,
            };
            if function.layout.is_inst_inserted(user)
                && walk.walk_use(None, &mut worklist, &mut packed).is_break()
            {
                return false;
            }
        }
    }
    true
}

/// One use, `user`, of a walked `value` that reaches the object along `path`.
struct Walk<'a> {
    function: &'a Function,
    user: InstId,
    value: ValueId,
    path: &'a Path,
}

impl Walk<'_> {
    fn walk_use<T>(
        &self,
        object_effects: Option<&ObjectEffectSummaryMap>,
        worklist: &mut Vec<(ValueId, Path)>,
        on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
    ) -> ControlFlow<T> {
        let Self {
            function,
            value,
            path,
            ..
        } = *self;

        // Storing the value, or packing it into an aggregate, carries the
        // object one step further away, whatever the value is.
        if let Some(store) = function.dfg.downcast::<&data::ObjStore>(self.user)
            && *store.value() == value
        {
            return carry_into(
                function,
                *store.object(),
                path.clone(),
                worklist,
                on_special,
            );
        }
        if let Some(write) = function.dfg.downcast::<&data::EnumWriteVariant>(self.user)
            && write.values().contains(&value)
        {
            for field in positions(write.values(), value) {
                let step = Step::Variant(*write.variant(), Some(field));
                carry_into(
                    function,
                    *write.object(),
                    prepend(step, path),
                    worklist,
                    on_special,
                )?;
            }
            return ControlFlow::Continue(());
        }
        if let Some(insert) = function.dfg.downcast::<&data::InsertValue>(self.user)
            && (*insert.dest() == value || *insert.value() == value)
        {
            let index = shape::const_u32(&function.dfg, *insert.idx());
            if *insert.value() == value {
                on_special(SpecialObjectUse::Carry)?;
                self.follow(prepend(Step::Field(index), path), worklist, on_special)?;
            }
            // Overwriting the field that carries the object drops it.
            if *insert.dest() == value
                && (index.is_none() || path.first() != Some(&Step::Field(index)))
            {
                self.follow(path.clone(), worklist, on_special)?;
            }
            return ControlFlow::Continue(());
        }
        if let Some(make) = function.dfg.downcast::<&data::EnumMake>(self.user)
            && make.values().contains(&value)
        {
            on_special(SpecialObjectUse::Carry)?;
            for field in positions(make.values(), value) {
                let step = Step::Variant(*make.variant(), Some(field));
                self.follow(prepend(step, path), worklist, on_special)?;
            }
            return ControlFlow::Continue(());
        }
        if function
            .dfg
            .downcast::<&control_flow::Phi>(self.user)
            .is_some_and(|phi| phi.args().iter().any(|(arg, _)| *arg == value))
        {
            return self.follow(path.clone(), worklist, on_special);
        }

        match path.first() {
            None => self.reference_use(object_effects, worklist, on_special),
            Some(Step::Deref) => self.holder_use(object_effects, worklist, on_special),
            Some(_) => self.aggregate_use(worklist, on_special),
        }
    }

    /// Walks a use of a reference into the object.
    fn reference_use<T>(
        &self,
        object_effects: Option<&ObjectEffectSummaryMap>,
        worklist: &mut Vec<(ValueId, Path)>,
        on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
    ) -> ControlFlow<T> {
        let Self {
            function, value, ..
        } = *self;

        if function
            .dfg
            .downcast::<&data::ObjProj>(self.user)
            .is_some_and(|proj| proj.values().first() == Some(&value))
            || function
                .dfg
                .downcast::<&data::ObjIndex>(self.user)
                .is_some_and(|index| *index.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumProj>(self.user)
                .is_some_and(|enum_proj| *enum_proj.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumAssertVariantRef>(self.user)
                .is_some_and(|enum_assert_ref| *enum_assert_ref.object() == value)
        {
            return self.follow(Path::new(), worklist, on_special);
        }
        if function
            .dfg
            .downcast::<&data::ObjLoad>(self.user)
            .is_some_and(|load| *load.object() == value)
            || function
                .dfg
                .downcast::<&data::ObjStore>(self.user)
                .is_some_and(|store| *store.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumGetTag>(self.user)
                .is_some_and(|enum_get_tag| *enum_get_tag.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumSetTag>(self.user)
                .is_some_and(|enum_set_tag| *enum_set_tag.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumWriteVariant>(self.user)
                .is_some_and(|enum_write_variant| *enum_write_variant.object() == value)
        {
            return ControlFlow::Continue(());
        }
        if function
            .dfg
            .downcast::<&data::ObjMaterializeStack>(self.user)
            .is_some_and(|mat_stack| *mat_stack.object() == value)
        {
            return on_special(SpecialObjectUse::MaterializeStack(
                function.dfg.inst_result(self.user),
            ));
        }
        if let Some(call) = function.dfg.downcast::<&control_flow::Call>(self.user)
            && call.args().contains(&value)
        {
            return self.call_use(call, object_effects, worklist, on_special);
        }
        if let Some(ret) = function.dfg.downcast::<&control_flow::Return>(self.user)
            && ret.args().iter().any(|arg| *arg == value)
        {
            return on_special(SpecialObjectUse::Return { value, ret });
        }

        on_special(SpecialObjectUse::Unknown)
    }

    /// Walks a use of a reference into memory that reaches the object along
    /// the rest of the path. Projections move toward the carried position and
    /// loads read what lies there; anything that lets the memory's contents
    /// leave the walk is unknown.
    fn holder_use<T>(
        &self,
        object_effects: Option<&ObjectEffectSummaryMap>,
        worklist: &mut Vec<(ValueId, Path)>,
        on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
    ) -> ControlFlow<T> {
        let Self {
            function,
            value,
            path,
            ..
        } = *self;
        let index = |value: ValueId| shape::const_u32(&function.dfg, value);

        let projection: Option<Path> = if let Some(proj) =
            function.dfg.downcast::<&data::ObjProj>(self.user)
            && proj.values().first() == Some(&value)
        {
            Some(
                proj.values()[1..]
                    .iter()
                    .map(|&field| Step::Field(index(field)))
                    .collect(),
            )
        } else if let Some(obj_index) = function.dfg.downcast::<&data::ObjIndex>(self.user)
            && *obj_index.object() == value
        {
            Some(smallvec![Step::Field(index(*obj_index.index()))])
        } else if let Some(enum_proj) = function.dfg.downcast::<&data::EnumProj>(self.user)
            && *enum_proj.object() == value
        {
            Some(smallvec![Step::Variant(
                *enum_proj.variant(),
                index(*enum_proj.field())
            )])
        } else {
            function
                .dfg
                .downcast::<&data::EnumAssertVariantRef>(self.user)
                .is_some_and(|enum_assert_ref| *enum_assert_ref.object() == value)
                .then(Path::new)
        };
        if let Some(projection) = projection {
            return match project(path, &projection) {
                Some(path) => self.follow(path, worklist, on_special),
                None => ControlFlow::Continue(()),
            };
        }
        if function
            .dfg
            .downcast::<&data::ObjLoad>(self.user)
            .is_some_and(|load| *load.object() == value)
        {
            return self.follow(path[1..].into(), worklist, on_special);
        }
        if function
            .dfg
            .downcast::<&data::ObjStore>(self.user)
            .is_some_and(|store| *store.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumGetTag>(self.user)
                .is_some_and(|enum_get_tag| *enum_get_tag.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumSetTag>(self.user)
                .is_some_and(|enum_set_tag| *enum_set_tag.object() == value)
            || function
                .dfg
                .downcast::<&data::EnumWriteVariant>(self.user)
                .is_some_and(|enum_write_variant| *enum_write_variant.object() == value)
        {
            return ControlFlow::Continue(());
        }
        // A raw pointer into the memory can carry the object out only through
        // a read, which would recover the held reference as untracked bits.
        if function
            .dfg
            .downcast::<&data::ObjMaterializeStack>(self.user)
            .is_some_and(|mat_stack| *mat_stack.object() == value)
            && function
                .dfg
                .inst_result(self.user)
                .is_none_or(|ptr| raw_pointer_stays_local(function, ptr, false))
        {
            return ControlFlow::Continue(());
        }
        if let Some(call) = function.dfg.downcast::<&control_flow::Call>(self.user)
            && call.args().contains(&value)
        {
            return self.call_use(call, object_effects, worklist, on_special);
        }

        on_special(SpecialObjectUse::Unknown)
    }

    /// Walks a use of an SSA aggregate that reaches the object along the rest
    /// of the path. Only extracting the carrying field keeps the object within
    /// reach of the walk.
    fn aggregate_use<T>(
        &self,
        worklist: &mut Vec<(ValueId, Path)>,
        on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
    ) -> ControlFlow<T> {
        let Self {
            function,
            value,
            path,
            ..
        } = *self;
        let index = |value: ValueId| shape::const_u32(&function.dfg, value);

        let extracted = if let Some(extract) =
            function.dfg.downcast::<&data::ExtractValue>(self.user)
            && *extract.dest() == value
        {
            Some(Step::Field(index(*extract.idx())))
        } else if let Some(extract) = function.dfg.downcast::<&data::EnumExtract>(self.user)
            && *extract.value() == value
        {
            Some(Step::Variant(*extract.variant(), index(*extract.field())))
        } else {
            None
        };
        if let Some(step) = extracted {
            return if step.may_match(path[0]) {
                self.follow(path[1..].into(), worklist, on_special)
            } else {
                ControlFlow::Continue(())
            };
        }
        if function
            .dfg
            .downcast::<&data::EnumTag>(self.user)
            .is_some_and(|tag| *tag.value() == value)
            || function
                .dfg
                .downcast::<&data::EnumIsVariant>(self.user)
                .is_some_and(|is_variant| *is_variant.value() == value)
            || function
                .dfg
                .downcast::<&data::EnumAssertVariant>(self.user)
                .is_some_and(|assert| *assert.value() == value)
        {
            return ControlFlow::Continue(());
        }

        on_special(SpecialObjectUse::Unknown)
    }

    /// Reports a call taking a reference into the object or into memory that
    /// reaches it; callee summaries cover what the callee does with references
    /// it loads through an argument. A result borrowing the argument may be
    /// any projection of it, so the walk follows each. It is never a reference
    /// loaded through the argument: such a reference has unknown provenance,
    /// which the summary reports as an escape of every argument instead.
    fn call_use<T>(
        &self,
        call: &control_flow::Call,
        object_effects: Option<&ObjectEffectSummaryMap>,
        worklist: &mut Vec<(ValueId, Path)>,
        on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
    ) -> ControlFlow<T> {
        let flow = on_special(SpecialObjectUse::Call {
            inst: self.user,
            value: self.value,
            call,
        });
        if call_result_borrows(self.function, self.user, call, self.value, object_effects) {
            // A projection skips some of the fields after the leading `Deref`.
            let (deref, rest) = self.path.split_at(self.path.len().min(1));
            let fields = rest.iter().take_while(|step| **step != Step::Deref).count();
            for skipped in 0..=fields {
                let path = deref.iter().chain(&rest[skipped..]).copied().collect();
                self.follow(path, worklist, on_special)?;
            }
        }
        flow
    }

    /// Continues the walk at this use's result along `path`. A reference
    /// holds no SSA fields, so a path that starts with one cannot be how a
    /// reference reaches the object.
    fn follow<T>(
        &self,
        path: Path,
        worklist: &mut Vec<(ValueId, Path)>,
        on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
    ) -> ControlFlow<T> {
        // Only single-result instructions are asked for their result.
        let Some(result) = self.function.dfg.inst_result(self.user) else {
            return ControlFlow::Continue(());
        };
        if !matches!(path.first(), None | Some(Step::Deref))
            && self
                .function
                .dfg
                .value_ty(result)
                .is_obj_ref(self.function.ctx())
        {
            return ControlFlow::Continue(());
        }
        if path.len() > MAX_PATH_STEPS {
            return on_special(SpecialObjectUse::Unknown);
        }
        worklist.push((result, path));
        ControlFlow::Continue(())
    }
}

/// Follows a value stored into `object`, whose memory then reaches the object
/// along `path`: every local allocation `object` may point into does, through
/// the projections that lead from it to `object`. A store into anything but
/// this function's allocations is unknown.
fn carry_into<T>(
    function: &Function,
    object: ValueId,
    path: Path,
    worklist: &mut Vec<(ValueId, Path)>,
    on_special: &mut impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
) -> ControlFlow<T> {
    on_special(SpecialObjectUse::Carry)?;
    let index = |value: ValueId| shape::const_u32(&function.dfg, value);
    let mut pending = vec![(object, path)];
    let mut seen = FxHashSet::default();
    while let Some((value, path)) = pending.pop() {
        if path.len() >= MAX_PATH_STEPS {
            return on_special(SpecialObjectUse::Unknown);
        }
        if !seen.insert((value, path.clone())) {
            continue;
        }
        let Some(inst) = function.dfg.value_inst(value) else {
            return on_special(SpecialObjectUse::Unknown);
        };
        if function.dfg.downcast::<&data::ObjAlloc>(inst).is_some() {
            worklist.push((value, prepend(Step::Deref, &path)));
        } else if let Some(proj) = function.dfg.downcast::<&data::ObjProj>(inst) {
            let fields = proj.values()[1..]
                .iter()
                .map(|&field| Step::Field(index(field)));
            pending.push((proj.values()[0], fields.chain(path).collect()));
        } else if let Some(obj_index) = function.dfg.downcast::<&data::ObjIndex>(inst) {
            let step = Step::Field(index(*obj_index.index()));
            pending.push((*obj_index.object(), prepend(step, &path)));
        } else if let Some(enum_proj) = function.dfg.downcast::<&data::EnumProj>(inst) {
            let step = Step::Variant(*enum_proj.variant(), index(*enum_proj.field()));
            pending.push((*enum_proj.object(), prepend(step, &path)));
        } else if let Some(enum_assert_ref) =
            function.dfg.downcast::<&data::EnumAssertVariantRef>(inst)
        {
            pending.push((*enum_assert_ref.object(), path));
        } else if let Some(phi) = function.dfg.downcast::<&control_flow::Phi>(inst) {
            pending.extend(phi.args().iter().map(|(arg, _)| (*arg, path.clone())));
        } else {
            return on_special(SpecialObjectUse::Unknown);
        }
    }
    ControlFlow::Continue(())
}

/// The path a projection by `projection` leaves of a reference into memory
/// that reaches the object along `path`, or `None` when the projection moves
/// away from the carried position.
fn project(path: &Path, projection: &[Step]) -> Option<Path> {
    let mut rest = &path[1..];
    for &step in projection {
        // A projection cannot pass a reference held in memory, so in
        // well-typed IR it stops before running out of steps or meeting one.
        let Some((&next, tail)) = rest.split_first().filter(|(next, _)| **next != Step::Deref)
        else {
            break;
        };
        if !step.may_match(next) {
            return None;
        }
        rest = tail;
    }
    Some(prepend(Step::Deref, &rest.into()))
}

fn prepend(step: Step, path: &Path) -> Path {
    std::iter::once(step).chain(path.iter().copied()).collect()
}

/// The positions of `value` among `values`.
fn positions(values: &[ValueId], value: ValueId) -> impl Iterator<Item = u32> + '_ {
    values
        .iter()
        .enumerate()
        .filter(move |(_, candidate)| **candidate == value)
        .map(|(position, _)| position as u32)
}

fn call_root_preserves_locality(
    function: &Function,
    inst: sonatina_ir::InstId,
    call: &control_flow::Call,
    value: ValueId,
    object_effects: &ObjectEffectSummaryMap,
    is_allowed_root_value: &mut impl FnMut(ValueId) -> bool,
) -> bool {
    let Some(sig) = function.ctx().get_sig(*call.callee()) else {
        return false;
    };
    let Some(summary) = object_effects.get(call.callee()) else {
        return false;
    };

    // The walker follows projections, so the argument can have a different type
    // from the allocation whose lifetime is being checked.
    let value_ty = function.dfg.value_ty(value);
    let mut saw_value = false;
    for (idx, &arg) in call.args().iter().enumerate() {
        if arg != value {
            continue;
        }
        saw_value = true;
        let Some(effect) = summary.arg_effects.get(idx) else {
            return false;
        };
        if sig.args().get(idx) != Some(&value_ty)
            || effect.needs_unknown_object_barrier()
            || summary
                .captures
                .iter()
                .any(|capture| capture.src_arg == idx)
        {
            return false;
        }
        if effect.local_only {
            continue;
        }

        let &[result] = function.dfg.inst_results(inst) else {
            return false;
        };
        if !summary.ret_effect.borrows_arg(idx) || !is_allowed_root_value(result) {
            return false;
        }
    }

    saw_value
}

/// Whether the single result of `call` borrows its argument `value`.
fn call_result_borrows(
    function: &Function,
    inst: InstId,
    call: &control_flow::Call,
    value: ValueId,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> bool {
    function.dfg.inst_results(inst).len() == 1
        && object_effects
            .and_then(|effects| effects.get(call.callee()))
            .is_some_and(|summary| {
                call.args()
                    .iter()
                    .enumerate()
                    .any(|(index, &arg)| arg == value && summary.ret_effect.borrows_arg(index))
            })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{lookup_func, parse_test_module};

    #[test]
    fn projected_call_arguments_preserve_locality_without_retention() {
        for (ty, projection) in [
            ("i64", ""),
            ("[i64; 2]", "v2.objref<i64> = obj.index v1 1.i64;"),
            ("@pair", "v2.objref<i64> = obj.proj v1 1.i64;"),
            (
                "@nested",
                "v3.objref<[@pair; 2]> = obj.proj v1 0.i64;\n\
                 v4.objref<@pair> = obj.index v3 1.i64;\n\
                 v2.objref<i64> = obj.proj v4 1.i64;",
            ),
        ] {
            let argument = if projection.is_empty() { "v1" } else { "v2" };
            for retains in [false, true] {
                let operation = if retains {
                    "obj.store v1 v0;"
                } else {
                    "obj.store v0 42.i64;"
                };
                let module = parse_test_module(&format!(
                    r#"
target = "aarch64-unknown-native"
type @pair = {{ i64, i64 }};
type @nested = {{ [@pair; 2] }};
func private %helper(v0.objref<i64>, v1.objref<objref<i64>>) {{
block0:
    {operation}
    return;
}}
func public %probe(v0.objref<objref<i64>>) {{
block0:
    v1.objref<{ty}> = obj.alloc {ty};
    {projection}
    call %helper {argument} v0;
    return;
}}
"#
                ));
                let effects = compute_object_effect_summaries(&module);
                let local_args = collect_local_object_arg_info_with_effects(&module, &effects);
                let probe = lookup_func(&module, "probe");
                module.func_store.view(probe, |function| {
                    let root = ValueId::from_u32(1);
                    assert_eq!(
                        object_root_stays_local_with_effects(
                            function,
                            root,
                            &effects,
                            |_| true,
                            false,
                            false,
                        ),
                        !retains,
                        "effect-summary locality: {ty}, retains={retains}",
                    );
                    assert_eq!(
                        object_root_stays_local_with(function, root, &local_args, |_| true, false),
                        !retains,
                        "local-argument locality: {ty}, retains={retains}",
                    );
                });
            }
        }
    }

    #[test]
    fn collect_local_object_arg_info_allows_enum_object_ops() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @option_i256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.objref<@option_i256>) {
block0:
    enum.write_variant v0 #Some (7.i256);
    v1.enumtag(@option_i256) = enum.get_tag v0;
    v2.objref<@option_i256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    v4.i256 = obj.load v3;
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert_eq!(
            local.get(&func).and_then(|args| args.get(&0)),
            Some(&LocalObjectArgInfo::Borrowed)
        );
    }

    #[test]
    fn object_root_stays_local_rejects_enum_write_variant_payload_escape() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256 };
type @option_pair = enum {
    #None,
    #Some(objref<@pair>),
};

func private %f(v0.objref<@pair>, v1.objref<@option_pair>) {
block0:
    enum.write_variant v1 #Some (v0);
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let stays_local = module.func_store.view(func, |function| {
            let root = function.arg_values[0];
            object_root_stays_local(function, root, &LocalObjectArgMap::default(), false)
        });
        assert!(
            !stays_local,
            "enum.write_variant payload use should make the root non-local"
        );
    }

    #[test]
    fn object_root_stays_local_through_enum_proj_phi_web() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = enum {
    #Off,
    #On(i256),
};

type @outer = enum {
    #None,
    #Some(objref<@inner>),
};

func private %f(v0.objref<@outer>, v1.i1) {
block0:
    v2.objref<@outer> = enum.assert_variant_ref v0 #Some;
    v3.objref<@inner> = enum.proj v2 #Some 0.i8;
    br v1 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    v4.objref<@inner> = phi (v3 block1) (v3 block2);
    enum.set_tag v4 #Off;
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert!(
            local.get(&func).is_some_and(|args| args.contains_key(&0)),
            "enum.proj + phi + nested enum op should keep the outer enum root local"
        );
    }

    #[test]
    fn collect_local_object_arg_info_follows_same_root_call_results() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %id(v0.objref<@pair>) -> objref<@pair> {
block0:
    return v0;
}

func private %f(v0.objref<@pair>, v1.i256) {
block0:
    v2.objref<@pair> = call %id v0;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v1;
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert!(
            local.get(&func).is_some_and(|args| args.contains_key(&0)),
            "same-root helper return should keep the arg local"
        );
    }

    #[test]
    fn collect_local_object_arg_info_rejects_returned_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.objref<@pair>) -> objref<@pair> {
block0:
    return v0;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert!(
            !local.get(&func).is_some_and(|args| args.contains_key(&0)),
            "returned arg should not stay local"
        );
    }

    #[test]
    fn collect_local_object_arg_info_rejects_phi_escape_for_all_roots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.objref<@pair>, v1.objref<@pair>, v2.i1) {
block0:
    br v2 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    v3.objref<@pair> = phi (v0 block1) (v1 block2);
    obj.materialize.stack v3;
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert!(
            !local
                .get(&func)
                .is_some_and(|args| args.contains_key(&0) || args.contains_key(&1)),
            "phi-merged escape should block local-object classification for every root"
        );
    }

    #[test]
    fn collect_local_object_arg_info_rejects_escaping_callee() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %escape(v0.objref<@pair>) {
block0:
    obj.materialize.stack v0;
    return;
}

func private %f(v0.objref<@pair>) {
block0:
    call %escape v0;
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert!(
            !local.get(&func).is_some_and(|args| args.contains_key(&0)),
            "escaping callee should block local-object classification"
        );
    }

    #[test]
    fn collect_local_object_arg_info_rejects_stack_materialized_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.objref<@pair>) {
block0:
    v1.*@pair = obj.materialize.stack v0;
    v2.*i256 = gep v1 0.i64 0.i8;
    mstore v2 7.i256 i256;
    return;
}
"#,
        );

        let func = lookup_func(&module, "f");
        let local = collect_local_object_arg_info(&module);
        assert!(
            !local.get(&func).is_some_and(|args| args.contains_key(&0)),
            "stack-materialized args should not be treated as local-only"
        );
    }
}
