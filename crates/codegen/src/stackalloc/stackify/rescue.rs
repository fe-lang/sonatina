//! Purely local, bounded-effort stack cleanups run before operand preparation:
//!
//! - dead-prefix cleanup (`clean_dead_stack_prefix`): pop dead values off the top and swap a live
//!   top past a contiguous dead chain beneath it;
//! - reachability rescue (`improve_reachability_before_operands`): when an operand sits just past
//!   `DUP16` reach, evict a bounded number of dead / cheap / duplicate stack items to bring it
//!   back into range.
//!
//! Both are opportunistic heuristics; the bounds below keep them from generating pathological swap
//! chains.

use sonatina_ir::{Function, ValueId};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, isa::evm::immediate_materialization_code_len, stackalloc::Actions};

use super::{
    builder::StackifyReachability,
    sym_stack::{StackItem, SymStack},
    uses::UseTracker,
};

/// Reachability rescue looks slightly past `SWAP16` reach (e.g. an operand at depth 18-20) when
/// deciding whether an aggressive cleanup can bring it back into `DUP16` range.
const AGGRESSIVE_REACHABILITY_DEPTH: usize = 20;

/// Upper bound on evictions per instruction, to avoid pathological swap chains.
const MAX_DELETIONS: usize = 8;

fn pop_dead_tops(
    stack: &mut SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
    actions: &mut Actions,
) {
    while let Some(StackItem::Value(v)) = stack.top() {
        if live_future.contains(*v) || live_out.contains(*v) {
            break;
        }
        stack.pop(actions);
    }
}

pub(super) fn clean_dead_stack_prefix(
    reach: StackifyReachability,
    stack: &mut SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
    actions: &mut Actions,
) {
    // Two local cleanups:
    // - pop any dead values that reach the top
    // - if a live value is on top and there is a contiguous dead chain directly beneath it,
    //   swap the live value down and pop the dead chain off the top.
    loop {
        let before_len = stack.len();
        pop_dead_tops(stack, live_future, live_out, actions);

        // If the top is not a normal value, don't try to reorder under it.
        let Some(StackItem::Value(top)) = stack.top() else {
            break;
        };
        // `pop_dead_tops` only stops on a live value (or a non-`Value`, handled above).
        debug_assert!(
            live_future.contains(*top) || live_out.contains(*top),
            "pop_dead_tops left a dead value on top"
        );

        let is_dead = |v: ValueId| !live_future.contains(v) && !live_out.contains(v);
        let dead_run = stack
            .iter()
            .skip(1)
            .take_while(|&v| matches!(v, StackItem::Value(v) if is_dead(*v)))
            .count();
        if dead_run == 0 {
            break;
        }

        // Swap the top live value with the deepest dead value in the contiguous chain (within
        // SWAP16 reach), then pop that chunk off. Repeat until the chain is gone.
        let mut remaining = dead_run;
        while remaining > 0 {
            let swap_depth = remaining.min(reach.swap_max.saturating_sub(1));
            stack.swap(swap_depth, actions);
            stack.pop_n(swap_depth, actions);
            remaining -= swap_depth;
        }

        if stack.len() == before_len {
            break;
        }
    }
}

pub(super) fn improve_reachability_before_operands(
    func: &Function,
    args: &[ValueId],
    reach: StackifyReachability,
    stack: &mut SymStack,
    uses: &UseTracker,
    actions: &mut Actions,
) {
    let mut protected_args: BitSet<ValueId> = BitSet::default();
    for &arg in args.iter() {
        if !func.dfg.value_is_imm(arg) {
            protected_args.insert(arg);
        }
    }

    // If at least one operand is on the stack but unreachable by `DUP16`, attempt a more
    // aggressive cleanup to bring it back into reach. This extends slightly past `SWAP16` reach
    // by allowing deletions that shift the stack (e.g. popping dead/cheap values above an
    // operand at depth 18-20).
    let mut needs_aggressive = false;
    for &arg in args.iter() {
        if !func.dfg.value_is_imm(arg)
            && stack.find_reachable_value(arg, reach.dup_max).is_none()
            && stack
                .find_reachable_value(arg, AGGRESSIVE_REACHABILITY_DEPTH)
                .is_some()
        {
            needs_aggressive = true;
            break;
        }
    }
    if !needs_aggressive {
        return;
    }

    let mut deletions: usize = 0;

    while deletions < MAX_DELETIONS {
        let mut progressed = false;

        for &arg in args.iter() {
            if !func.dfg.value_is_imm(arg)
                && stack.find_reachable_value(arg, reach.dup_max).is_none()
                && let Some(pos) = stack.find_reachable_value(arg, AGGRESSIVE_REACHABILITY_DEPTH)
                && let Some(victim) =
                    choose_reachability_victim(func, stack, pos, &protected_args, reach, uses)
            {
                stack.stable_delete_at_depth(victim + 1, actions);
                deletions += 1;
                progressed = true;
                break;
            }
        }

        if !progressed {
            break;
        }
    }
}

fn choose_reachability_victim(
    func: &Function,
    stack: &SymStack,
    above: usize,
    protected_args: &BitSet<ValueId>,
    reach: StackifyReachability,
    uses: &UseTracker,
) -> Option<usize> {
    let limit = stack.len_above_func_ret().min(reach.swap_max);
    let above = above.min(limit);

    // 1) Prefer deleting dead values, starting from the shallowest depth to minimize `SWAP*`
    // chains. This includes immediates: if they're dead, removing them cannot introduce new
    // rematerialization cost.
    for (i, item) in stack.iter().take(above).enumerate() {
        if let StackItem::Value(v) = item
            && !protected_args.contains(*v)
            && uses.is_dead(*v)
        {
            return Some(i);
        }
    }

    // 2) Then evict "cheap" immediates (they are always rematerializable).
    for (i, item) in stack.iter().take(above).enumerate() {
        if let StackItem::Value(v) = item
            && !protected_args.contains(*v)
            && func.dfg.value_is_imm(*v)
            && is_evictable_imm(func, *v)
        {
            return Some(i);
        }
    }

    // 3) Then delete redundant duplicates of non-operands (keeping the shallowest copy).
    let mut first_index: BTreeMap<ValueId, usize> = BTreeMap::new();
    for (i, item) in stack.iter().take(above).enumerate() {
        let StackItem::Value(v) = item else {
            continue;
        };
        first_index.entry(*v).or_insert(i);
    }

    for (i, item) in stack.iter().take(above).enumerate() {
        if let StackItem::Value(v) = item
            && !protected_args.contains(*v)
            && let Some(&first) = first_index.get(v)
            && first != i
        {
            return Some(i);
        }
    }

    None
}

fn is_evictable_imm(func: &Function, v: ValueId) -> bool {
    const MAX_MATERIALIZATION_BYTES: usize = 3; // PUSH2 or smaller.
    let Some(imm) = func.dfg.value_imm(v) else {
        return false;
    };
    immediate_materialization_code_len(imm) <= MAX_MATERIALIZATION_BYTES
}
