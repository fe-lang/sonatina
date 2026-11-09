//! Insert chain placement: an `insert_value` chain that builds an aggregate
//! from undef moves up to just after the last of the values it inserts,
//! when its result only fills a field of another chain or is returned, and
//! down to just before the store, when its result is only stored into an
//! object later in its block with no call between.
//!
//! A native backend builds such a chain in memory: in the field of the chain
//! it fills, or in the return buffer. Its scalar inputs would otherwise stay
//! in registers, or spill, until the chain's original position, typically a
//! struct literal after everything its fields need is computed. The chain's
//! values are the same wherever it runs, so it may run as soon as its inputs
//! exist, though not inside a loop it was outside of, nor outside one it was
//! inside.
//!
//! A stored chain is built at the store's destination when that object's
//! address exists before the chain starts. A struct literal pushed onto a
//! vector, `v.push(S { .. })`, comes before the address of its slot, so it
//! moves down to the store instead of being built aside and copied. The
//! chains embedded in it are built there too, but only from its block and
//! with nothing that reads memory between them and the store: they stay in
//! that block, and move down to the store with it, past a load of the old
//! value in `core::mem::replace(mut x, S { .. })`.
//!
//! A value stored in a later block than the one building it, which may also
//! be used elsewhere, is built again right before each use outside its
//! block, as a push builds an element before learning whether its slot
//! exists and hands it back when it does not. Each copy then has its own
//! uses, and the stored one is built at its destination. The construction
//! is an `insert_value` chain on undef or an `enum.make`, with the
//! constructions only it uses, all in its block. It is not built again in a
//! loop it was outside of, and goes once its block has no use of it left.

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, Value, ValueId,
    inst::{
        control_flow::Return,
        data::{EnumMake, InsertValue, ObjStore},
    },
};

use crate::{cfg_edit::clone_inst_before, domtree::DomTree, loop_analysis::LoopTree};

/// The most instructions a construction built again at its uses may have.
const MAX_REBUILT_INSTS: usize = 16;

#[derive(Default)]
pub struct HoistInsertChains;

impl HoistInsertChains {
    pub fn run(&mut self, func: &mut Function, domtree: &DomTree, lpt: &LoopTree) -> bool {
        let heads: Vec<InstId> = domtree
            .rpo()
            .iter()
            .flat_map(|&block| func.layout.iter_inst(block))
            .filter(|&inst| is_undef_head(func, inst))
            .collect();
        let mut order = SecondaryMap::default();
        for &block in domtree.rpo() {
            number(func, block, &mut order);
        }
        let mut changed = false;
        for head in heads {
            let chain = chain(func, head);
            if let Some(after) = hoisted_position(func, domtree, lpt, &order, &chain) {
                let mut previous = after;
                for &inst in &chain {
                    func.layout.remove_inst(inst);
                    func.layout.insert_inst_after(inst, previous);
                    previous = inst;
                }
                number(func, func.layout.inst_block(after), &mut order);
                changed = true;
            } else if let Some(store) = sunk_position(func, &chain) {
                for &inst in &chain {
                    func.layout.remove_inst(inst);
                    func.layout.insert_inst_before(inst, store);
                }
                number(func, func.layout.inst_block(store), &mut order);
                changed = true;
            }
        }

        let stores: Vec<InstId> = func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .filter(|&inst| func.dfg.downcast::<&ObjStore>(inst).is_some())
            .collect();
        for &store in &stores {
            let Some(tree) = stored_tree(func, store) else {
                continue;
            };
            for &inst in &tree {
                func.layout.remove_inst(inst);
                func.layout.insert_inst_before(inst, store);
            }
            changed = true;
        }
        for store in stores {
            changed |= rebuild_at_uses(func, lpt, store);
        }
        changed
    }
}

/// Builds the value `store` stores again right before its first use in each
/// other block of its loop, when an earlier block builds it, and removes the
/// original once nothing uses it.
fn rebuild_at_uses(func: &mut Function, lpt: &LoopTree, store: InstId) -> bool {
    let Some(stored) = func.dfg.downcast::<&ObjStore>(store) else {
        return false;
    };
    let value = *stored.value();
    let Some(def) = func.dfg.value_inst(value) else {
        return false;
    };
    let block = func.layout.inst_block(def);
    let mut tree = Vec::new();
    if func.layout.inst_block(store) == block
        || func.dfg.users(value).any(|&user| func.dfg.is_phi(user))
        || !construction(func, value, None, block, &mut tree)
        || tree.len() > MAX_REBUILT_INSTS
    {
        return false;
    }
    let users: FxHashSet<InstId> = func.dfg.users(value).copied().collect();
    let mut user_blocks: Vec<BlockId> = users
        .iter()
        .map(|&user| func.layout.inst_block(user))
        .filter(|&user_block| {
            user_block != block && lpt.loop_of_block(user_block) == lpt.loop_of_block(block)
        })
        .collect();
    user_blocks.sort_unstable();
    user_blocks.dedup();
    if !user_blocks.contains(&func.layout.inst_block(store)) {
        return false;
    }
    for user_block in user_blocks {
        let block_users: Vec<InstId> = func
            .layout
            .iter_inst(user_block)
            .filter(|inst| users.contains(inst))
            .collect();
        let mut rebuilt = FxHashMap::default();
        for &inst in &tree {
            clone_inst_before(func, inst, block_users[0], &mut rebuilt);
        }
        let copy = rebuilt[&value];
        for user in block_users {
            let mut inst = func.dfg.clone_inst(user);
            inst.for_each_value_mut(&mut |operand| {
                if *operand == value {
                    *operand = copy;
                }
            });
            func.dfg.replace_inst(user, inst);
        }
    }
    if func.dfg.users_num(value) == 0 {
        for &inst in &tree {
            func.layout.remove_inst(inst);
        }
        func.erase_insts(&tree);
    }
    true
}

/// Appends to `tree` the instructions building `value` in `block`, after
/// those of the constructions embedded in it: an `insert_value` chain on
/// undef or an `enum.make`. An embedded construction is used only by `user`,
/// the instruction embedding it; another value it takes is an input, which
/// the construction leaves where it is.
fn construction(
    func: &Function,
    value: ValueId,
    user: Option<InstId>,
    block: BlockId,
    tree: &mut Vec<InstId>,
) -> bool {
    let Some(def) = func.dfg.value_inst(value) else {
        return false;
    };
    if func.layout.inst_block(def) != block
        || user.is_some_and(|user| sole_user(func, value) != Some(user))
    {
        return false;
    }
    if let Some(make) = func.dfg.downcast::<&EnumMake>(def) {
        // A construction filling several fields is built once.
        let mut fields = FxHashSet::default();
        for &field in make.values() {
            if fields.insert(field) {
                construction(func, field, Some(def), block, tree);
            }
        }
        tree.push(def);
        return true;
    }
    let mut head = def;
    loop {
        let Some(insert) = func.dfg.downcast::<&InsertValue>(head) else {
            return false;
        };
        let dest = *insert.dest();
        if matches!(func.dfg.value(dest), Value::Undef { .. }) {
            break;
        }
        let Some(dest_def) = func.dfg.value_inst(dest) else {
            return false;
        };
        if sole_user(func, dest) != Some(head) || func.layout.inst_block(dest_def) != block {
            return false;
        }
        head = dest_def;
    }
    let chain = chain(func, head);
    if chain.last() != Some(&def) {
        return false;
    }
    for &inst in &chain {
        let insert = func
            .dfg
            .downcast::<&InsertValue>(inst)
            .expect("a chain holds inserts");
        construction(func, *insert.value(), Some(inst), block, tree);
    }
    tree.extend_from_slice(&chain);
    true
}

/// The chains `store` stores, when its value is a chain in its block that
/// embeds others there: each chain's instructions, those it embeds first,
/// when they are not already right before `store` in that order and no call
/// comes between the first of them and `store`.
fn stored_tree(func: &Function, store: InstId) -> Option<Vec<InstId>> {
    let value = *func.dfg.downcast::<&ObjStore>(store)?.value();
    let block = func.layout.inst_block(store);
    let root = embedded_chain(func, value, store, block)?;
    let mut tree = Vec::new();
    collect_tree(func, &root, block, &mut tree);
    if tree.len() == root.len() {
        return None;
    }
    let members: FxHashSet<InstId> = tree.iter().copied().collect();
    let before: Vec<InstId> = std::iter::successors(func.layout.prev_inst_of(store), |&inst| {
        func.layout.prev_inst_of(inst)
    })
    .take_while(|inst| members.contains(inst) || !func.dfg.is_call(*inst))
    .collect();
    let in_place = before.iter().zip(tree.iter().rev()).all(|(a, b)| a == b);
    let reached = before.iter().filter(|inst| members.contains(inst)).count() == tree.len();
    (!in_place && reached).then_some(tree)
}

/// Appends to `tree` the chains embedded in `chain`, in `block`, then `chain`.
fn collect_tree(func: &Function, chain: &[InstId], block: BlockId, tree: &mut Vec<InstId>) {
    for &inst in chain {
        let insert = func
            .dfg
            .downcast::<&InsertValue>(inst)
            .expect("a chain holds inserts");
        if let Some(embedded) = embedded_chain(func, *insert.value(), inst, block) {
            collect_tree(func, &embedded, block, tree);
        }
    }
    tree.extend_from_slice(chain);
}

/// The chain on undef in `block` whose result is `value`, when `user` is
/// its one use.
fn embedded_chain(
    func: &Function,
    value: ValueId,
    user: InstId,
    block: BlockId,
) -> Option<Vec<InstId>> {
    if sole_user(func, value)? != user {
        return None;
    }
    let mut head = func.dfg.value_inst(value)?;
    loop {
        let insert = func.dfg.downcast::<&InsertValue>(head)?;
        if func.layout.inst_block(head) != block {
            return None;
        }
        let dest = *insert.dest();
        if matches!(func.dfg.value(dest), Value::Undef { .. }) {
            break;
        }
        if sole_user(func, dest)? != head {
            return None;
        }
        head = func.dfg.value_inst(dest)?;
    }
    let chain = chain(func, head);
    (func.dfg.inst_result(*chain.last()?) == Some(value)).then_some(chain)
}

/// Numbers `block`'s instructions in layout order.
fn number(func: &Function, block: BlockId, order: &mut SecondaryMap<InstId, u32>) {
    for (index, inst) in func.layout.iter_inst(block).enumerate() {
        order[inst] = index as u32;
    }
}

/// Whether `inst` starts an `insert_value` chain on an undef aggregate.
fn is_undef_head(func: &Function, inst: InstId) -> bool {
    func.dfg
        .downcast::<&InsertValue>(inst)
        .is_some_and(|insert| matches!(func.dfg.value(*insert.dest()), Value::Undef { .. }))
}

/// The chain starting at `head`: each insert the sole user of the one
/// before, in the same block.
fn chain(func: &Function, head: InstId) -> Vec<InstId> {
    let block = func.layout.inst_block(head);
    std::iter::successors(Some(head), |&inst| {
        let result = func.dfg.inst_result(inst)?;
        let user = sole_user(func, result)?;
        let insert = func.dfg.downcast::<&InsertValue>(user)?;
        (*insert.dest() == result && func.layout.inst_block(user) == block).then_some(user)
    })
    .collect()
}

/// The store of `chain`'s result into an object, when it is the result's
/// one use, later in the chain's block with no call between, and not right
/// after the chain already.
fn sunk_position(func: &Function, chain: &[InstId]) -> Option<InstId> {
    let tail_inst = *chain.last()?;
    let tail = func.dfg.inst_result(tail_inst)?;
    let store = sole_user(func, tail)?;
    let store_info = func.dfg.downcast::<&ObjStore>(store)?;
    let between: Vec<InstId> =
        std::iter::successors(func.layout.next_inst_of(tail_inst), |&inst| {
            func.layout.next_inst_of(inst)
        })
        .take_while(|&inst| inst != store)
        .collect();
    (*store_info.value() == tail
        && func.layout.inst_block(store) == func.layout.inst_block(tail_inst)
        && !between.is_empty()
        && func.layout.next_inst_of(*between.last()?) == Some(store)
        && between.iter().all(|&inst| !func.dfg.is_call(inst)))
    .then_some(store)
}

/// The instruction after which `chain` can run instead, if earlier than its
/// head: the last definition of a value it inserts, or the last phi of that
/// definition's block.
fn hoisted_position(
    func: &Function,
    domtree: &DomTree,
    lpt: &LoopTree,
    order: &SecondaryMap<InstId, u32>,
    chain: &[InstId],
) -> Option<InstId> {
    let tail = func.dfg.inst_result(*chain.last()?)?;
    let user = sole_user(func, tail)?;
    let fills_field = func
        .dfg
        .downcast::<&InsertValue>(user)
        .is_some_and(|insert| *insert.value() == tail && *insert.dest() != tail);
    if !fills_field && func.dfg.downcast::<&Return>(user).is_none() {
        return None;
    }

    let head = chain[0];
    let block = func.layout.inst_block(head);
    let mut latest: Option<(BlockId, InstId)> = None;
    for &inst in chain {
        let insert = func.dfg.downcast::<&InsertValue>(inst)?;
        let Some(def) = func.dfg.value_inst(*insert.value()) else {
            continue;
        };
        let def_block = func.layout.inst_block(def);
        let later = match latest {
            None => true,
            Some((latest_block, latest_inst)) if latest_block == def_block => {
                order[latest_inst] < order[def]
            }
            Some((latest_block, _)) => domtree.dominates(latest_block, def_block),
        };
        if later {
            latest = Some((def_block, def));
        }
    }
    let (def_block, def) = latest?;
    if def_block != block && embedded_in_stored_chain(func, tail) {
        return None;
    }
    let after = if func.dfg.is_phi(def) {
        func.layout
            .iter_inst(def_block)
            .take_while(|&inst| func.dfg.is_phi(inst))
            .last()?
    } else {
        def
    };
    let earlier = def_block != block || order[after] + 1 < order[head];
    (earlier && lpt.loop_of_block(def_block) == lpt.loop_of_block(block)).then_some(after)
}

/// Whether `value`, a chain's result, fills a field of a chain that is only
/// stored into an object, directly or through further chains.
fn embedded_in_stored_chain(func: &Function, mut value: ValueId) -> bool {
    loop {
        let Some(user) = sole_user(func, value) else {
            return false;
        };
        if let Some(store) = func.dfg.downcast::<&ObjStore>(user) {
            return *store.value() == value;
        }
        let Some(insert) = func.dfg.downcast::<&InsertValue>(user) else {
            return false;
        };
        if *insert.value() != value || *insert.dest() == value {
            return false;
        }
        // The rest of the chain `value` fills ends at its own result.
        value = func.dfg.inst_result(user).expect("an insert has a result");
        while let Some(next) = sole_user(func, value)
            && func
                .dfg
                .downcast::<&InsertValue>(next)
                .is_some_and(|insert| *insert.dest() == value)
        {
            value = func.dfg.inst_result(next).expect("an insert has a result");
        }
    }
}

/// The one user of `value`, if it has exactly one.
fn sole_user(func: &Function, value: ValueId) -> Option<InstId> {
    let mut users = func.dfg.users(value).copied();
    match (users.next(), users.next()) {
        (Some(user), None) => Some(user),
        _ => None,
    }
}
