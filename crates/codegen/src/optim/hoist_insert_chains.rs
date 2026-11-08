//! Insert chain hoisting: an `insert_value` chain that builds an aggregate
//! from undef moves up to just after the last of the values it inserts,
//! when its result only fills a field of another chain or is returned.
//!
//! A native backend builds such a chain in memory: in the field of the chain
//! it fills, or in the return buffer. Its scalar inputs would otherwise stay
//! in registers, or spill, until the chain's original position, typically a
//! struct literal after everything its fields need is computed. The chain's
//! values are the same wherever it runs, so it may run as soon as its inputs
//! exist, though not inside a loop it was outside of, nor outside one it was
//! inside.

use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    BlockId, Function, InstId, Value,
    inst::{control_flow::Return, data::InsertValue},
};

use crate::{domtree::DomTree, loop_analysis::LoopTree};

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
            }
        }
        changed
    }
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
        let mut users = func.dfg.users(result).copied();
        let (Some(user), None) = (users.next(), users.next()) else {
            return None;
        };
        let insert = func.dfg.downcast::<&InsertValue>(user)?;
        (*insert.dest() == result && func.layout.inst_block(user) == block).then_some(user)
    })
    .collect()
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
    let mut users = func.dfg.users(tail).copied();
    let (Some(user), None) = (users.next(), users.next()) else {
        return None;
    };
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
