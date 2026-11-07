//! Arguments a callee owns. A private function whose by-reference aggregate
//! argument initializes a whole local object at the top of its entry block,
//! which no branch returns to, and is otherwise only read for fields held in
//! registers before anything can change that object, builds the object in
//! the argument's storage instead of copying the argument into a slot of its
//! own. A function that passes its own argument on in a tail call, to an
//! argument its callee owns, gives that storage away, so it owns the
//! argument too. Callers pass an owned argument in storage they do not use
//! after the call and that no other argument shares, copying it into a
//! temporary otherwise; a tail call passes its caller's own owned argument.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Module, ValueId,
    inst::{InstId, inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
    module::FuncRef,
};

use super::{tail::TailCalls, uses_indirect_value_representation};

/// An owned argument: its index, the object built in its storage, and the
/// store that would have copied it there.
#[derive(Clone, Copy)]
pub(super) struct OwnedArg {
    pub index: usize,
    pub object: ValueId,
    pub store: InstId,
}

#[derive(Default)]
pub(super) struct Ownership {
    by_func: FxHashMap<FuncRef, Vec<OwnedArg>>,
    /// Arguments owned to pass on in tail calls, by function and index.
    passed_on: FxHashSet<(FuncRef, usize)>,
}

impl Ownership {
    pub(super) fn new(module: &Module, tail_calls: &TailCalls) -> Self {
        let mut ownership = Self::default();
        for func_ref in module.funcs() {
            let linkage = module.ctx.func_linkage(func_ref);
            if !linkage.is_private() || !linkage.has_definition() {
                continue;
            }
            let owned = module.func_store.view(func_ref, owned_args);
            if !owned.is_empty() {
                ownership.by_func.insert(func_ref, owned);
            }
        }
        // Tail calls only pass the caller's own aggregate arguments on, so
        // each owned argument they reach makes the caller own its argument.
        let mut changed = true;
        while changed {
            changed = false;
            for (func_ref, sites) in tail_calls.sites() {
                module.func_store.view(func_ref, |function| {
                    for &site in sites {
                        let NativeInstKind::Call(call) =
                            native_inst_set().resolve_inst(function.dfg.inst(site))
                        else {
                            continue;
                        };
                        for (index, &arg) in call.args().iter().enumerate() {
                            if ownership.owns(*call.callee(), index)
                                && let Some(own) =
                                    function.arg_values.iter().position(|&value| value == arg)
                                && !ownership.owns(func_ref, own)
                            {
                                ownership.passed_on.insert((func_ref, own));
                                changed = true;
                            }
                        }
                    }
                });
            }
        }
        ownership
    }

    /// The arguments `func` owns.
    pub(super) fn owned(&self, func: FuncRef) -> &[OwnedArg] {
        self.by_func.get(&func).map_or(&[], Vec::as_slice)
    }

    /// Whether `func` owns its argument `index`.
    pub(super) fn owns(&self, func: FuncRef, index: usize) -> bool {
        self.passed_on.contains(&(func, index))
            || self.owned(func).iter().any(|arg| arg.index == index)
    }
}

fn owned_args(function: &Function) -> Vec<OwnedArg> {
    let dfg = &function.dfg;
    let ctx = function.ctx();
    // The object starts from the argument's value only if the entry block
    // runs once: a branch back to it would rebuild the object from storage
    // the last pass changed.
    let Some(entry) = function.layout.entry_block().filter(|&entry| {
        !function
            .layout
            .iter_block()
            .filter_map(|block| dfg.branch_info(function.layout.last_inst_of(block)?))
            .any(|branch| branch.dests().contains(&entry))
    }) else {
        return Vec::new();
    };
    function
        .arg_values
        .iter()
        .enumerate()
        .filter_map(|(index, &arg)| {
            let ty = dfg.value_ty(arg);
            if !uses_indirect_value_representation(ctx, ty) {
                return None;
            }
            // One store, and reads of fields held in registers.
            let mut stores = dfg.users(arg).copied().filter(|&user| {
                !matches!(
                    native_inst_set().resolve_inst(dfg.inst(user)),
                    NativeInstKind::ExtractValue(_)
                )
            });
            let (Some(store), None) = (stores.next(), stores.next()) else {
                return None;
            };
            let NativeInstKind::ObjStore(info) = native_inst_set().resolve_inst(dfg.inst(store))
            else {
                return None;
            };
            let object = *info.object();
            let alloc = dfg.value_inst(object)?;
            let NativeInstKind::ObjAlloc(alloc_info) =
                native_inst_set().resolve_inst(dfg.inst(alloc))
            else {
                return None;
            };
            // The store comes first among the object's uses, in the entry
            // block, which dominates the rest.
            let first_use = function
                .layout
                .iter_inst(entry)
                .find(|&inst| dfg.users(object).any(|&user| user == inst));
            // Every read comes before anything after the store may change
            // the object.
            let unchanged: Vec<_> =
                std::iter::successors(Some(store), |&inst| function.layout.next_inst_of(inst))
                    .take_while(|&inst| inst == store || !dfg.may_mutate_state(inst))
                    .collect();
            let reads_first = dfg.users(arg).all(|&user| {
                user == store
                    || dfg.inst_result(user).is_some_and(|field| {
                        !uses_indirect_value_representation(ctx, dfg.value_ty(field))
                    }) && (function.layout.inst_block(user) == entry
                        && function
                            .layout
                            .iter_inst(entry)
                            .position(|inst| inst == user)
                            < function
                                .layout
                                .iter_inst(entry)
                                .position(|inst| inst == store)
                        || unchanged.contains(&user))
            });
            (*info.value() == arg
                && *alloc_info.ty() == ty
                && function.layout.inst_block(store) == entry
                && function.layout.inst_block(alloc) == entry
                && first_use == Some(store)
                && reads_first)
                .then_some(OwnedArg {
                    index,
                    object,
                    store,
                })
        })
        .collect()
}
