//! Object copy coalescing: a local object that is a whole copy of another,
//! written by nothing but that copy, reads the original instead, when no
//! write of the original can follow the copy.
//!
//! Passing an aggregate by value to an inlined callee that indexes it copies
//! the caller's object into the callee's own: a log's topics are built in
//! one array, then copied into the array the log buffer reads them from.
//!
//! A reference to either object that reaches anything but a load, a store
//! into it or a projection (a call, a phi, a materialized pointer, a store
//! of the reference itself) may write the object through an alias at any
//! later point, so the copy stays. So does a copy used where the original
//! is not yet allocated.

use std::collections::VecDeque;

use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, ValueId,
    inst::data::{ObjAlloc, ObjIndex, ObjLoad, ObjProj, ObjStore},
};

use crate::{domtree::DomTree, optim::compare_sub_fusion::dominates};

#[derive(Default)]
pub struct CoalesceObjectCopies;

impl CoalesceObjectCopies {
    pub fn run(&mut self, func: &mut Function, cfg: &ControlFlowGraph, domtree: &DomTree) -> bool {
        let mut changed = false;
        while let Some((store, copy, original)) = find_copy(func, cfg, domtree) {
            let load = func
                .dfg
                .value_inst(*func.dfg.downcast::<&ObjStore>(store).unwrap().value());
            let alloc = func.dfg.value_inst(copy).unwrap();
            func.layout.remove_inst(store);
            func.erase_inst(store);
            func.dfg.change_to_alias(copy, original);
            func.layout.remove_inst(alloc);
            func.erase_inst(alloc);
            if let Some(load) = load
                && func
                    .dfg
                    .inst_result(load)
                    .is_some_and(|loaded| func.dfg.users_num(loaded) == 0)
            {
                func.layout.remove_inst(load);
                func.erase_inst(load);
            }
            changed = true;
        }
        changed
    }
}

/// A store copying a whole local object into another that it alone writes,
/// with the copy and the original, when nothing can write the original after
/// the copy's load of it and the original's allocation dominates every use
/// of the copy.
fn find_copy(
    func: &Function,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
) -> Option<(InstId, ValueId, ValueId)> {
    func.layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .find_map(|inst| {
            let store = func.dfg.downcast::<&ObjStore>(inst)?;
            let (copy, value) = (*store.object(), *store.value());
            let load_inst = func.dfg.value_inst(value)?;
            let original = *func.dfg.downcast::<&ObjLoad>(load_inst)?.object();
            let alloc = func.dfg.value_inst(original)?;
            (copy != original
                && is_local_object(func, copy)
                && is_local_object(func, original)
                && func.dfg.value_ty(copy) == func.dfg.value_ty(original)
                && stores(func, copy).is_some_and(|stores| stores == [inst])
                && stores(func, original).is_some_and(|stores| {
                    !stores
                        .into_iter()
                        .any(|store| reachable_after(func, cfg, load_inst, store))
                })
                && func
                    .dfg
                    .users(copy)
                    .filter(|&&user| func.layout.is_inst_inserted(user))
                    .all(|&user| dominates(func, domtree, alloc, user)))
            .then_some((inst, copy, original))
        })
}

fn is_local_object(func: &Function, value: ValueId) -> bool {
    func.dfg
        .value_inst(value)
        .is_some_and(|inst| func.dfg.downcast::<&ObjAlloc>(inst).is_some())
}

/// The stores into `object` or a part of it, unless a reference to it
/// reaches anything but a load, such a store or a projection.
fn stores(func: &Function, object: ValueId) -> Option<Vec<InstId>> {
    let mut stores = Vec::new();
    let mut refs = vec![object];
    while let Some(reference) = refs.pop() {
        for &user in func.dfg.users(reference) {
            if !func.layout.is_inst_inserted(user) || func.dfg.downcast::<&ObjLoad>(user).is_some()
            {
                continue;
            }
            if func
                .dfg
                .downcast::<&ObjStore>(user)
                .is_some_and(|store| *store.object() == reference && *store.value() != reference)
            {
                stores.push(user);
                continue;
            }
            let derived = func
                .dfg
                .downcast::<&ObjProj>(user)
                .is_some_and(|proj| proj.values()[0] == reference)
                || func
                    .dfg
                    .downcast::<&ObjIndex>(user)
                    .is_some_and(|index| *index.object() == reference);
            if !derived {
                return None;
            }
            refs.push(func.dfg.inst_result(user)?);
        }
    }
    Some(stores)
}

/// Whether `later` can run after `inst`: later in its block, or in a block
/// a path from `inst`'s block reaches.
fn reachable_after(func: &Function, cfg: &ControlFlowGraph, inst: InstId, later: InstId) -> bool {
    let block = func.layout.inst_block(inst);
    let later_block = func.layout.inst_block(later);
    if later_block == block
        && std::iter::successors(func.layout.next_inst_of(inst), |&next| {
            func.layout.next_inst_of(next)
        })
        .any(|next| next == later)
    {
        return true;
    }
    let mut seen = SecondaryMap::<BlockId, bool>::default();
    let mut queue: VecDeque<_> = cfg.succs_of(block).copied().collect();
    while let Some(next) = queue.pop_front() {
        if std::mem::replace(&mut seen[next], true) {
            continue;
        }
        if next == later_block {
            return true;
        }
        queue.extend(cfg.succs_of(next).copied());
    }
    false
}
