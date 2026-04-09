use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    BlockId, Function, InstDowncast, InstId, Value, ValueId,
    inst::{control_flow, control_flow::BranchKind, evm},
};

use crate::bitset::BitSet;

use super::{builder::StackifyContext, templates::BlockTemplate};

pub(super) fn compute_terminal_chain_blocks(
    ctx: &StackifyContext<'_>,
    templates: &SecondaryMap<BlockId, BlockTemplate>,
) -> SecondaryMap<BlockId, bool> {
    let mut terminal_chain_blocks = SecondaryMap::new();

    for &block in ctx.dom.rpo().iter().rev() {
        if !ctx.dom.is_reachable(block)
            || block == ctx.entry
            || !ctx.phi_results[block].is_empty()
            || !templates[block].params.is_empty()
            || !templates[block].transfer.is_empty()
            || ctx
                .scc
                .scc_of(block)
                .is_some_and(|scc| ctx.scc.scc_data(scc).is_cycle)
            || !block_uses_only_local_values(ctx.func, block, &ctx.value_aliases)
        {
            continue;
        }

        let Some(term) = ctx.func.layout.last_inst_of(block) else {
            continue;
        };
        let is = ctx.func.inst_set();
        let inst = ctx.func.dfg.inst(term);

        terminal_chain_blocks[block] =
            <&evm::EvmRevert as InstDowncast>::downcast(is, inst).is_some()
                || <&evm::EvmReturn as InstDowncast>::downcast(is, inst).is_some()
                || <&evm::EvmStop as InstDowncast>::downcast(is, inst).is_some()
                || <&evm::EvmInvalid as InstDowncast>::downcast(is, inst).is_some()
                || <&evm::EvmSelfDestruct as InstDowncast>::downcast(is, inst).is_some()
                || <&control_flow::Unreachable as InstDowncast>::downcast(is, inst)
                    .is_some_and(|_| unreachable_stays_terminating(ctx.func, block, term))
                || ctx.func.dfg.branch_info(term).is_some_and(|branch| {
                    match branch.branch_kind() {
                        BranchKind::Jump(_) | BranchKind::Br(_) | BranchKind::BrTable(_) => branch
                            .dests()
                            .iter()
                            .copied()
                            .all(|dest| terminal_chain_blocks[dest]),
                    }
                });
    }

    terminal_chain_blocks
}

fn block_uses_only_local_values(
    func: &Function,
    block: BlockId,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> bool {
    let mut local_values = BitSet::default();

    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            continue;
        }

        if !func
            .dfg
            .inst(inst)
            .collect_values()
            .into_iter()
            .all(|value| {
                let value = value_aliases[value].unwrap_or(value);
                local_values.contains(value)
                    || matches!(
                        func.dfg.value(value),
                        Value::Immediate { .. } | Value::Global { .. } | Value::Undef { .. }
                    )
            })
        {
            return false;
        }

        for &result in func.dfg.inst_results(inst) {
            local_values.insert(value_aliases[result].unwrap_or(result));
        }
    }

    true
}

fn unreachable_stays_terminating(func: &Function, block: BlockId, term: InstId) -> bool {
    let Some(prev) = prev_non_phi_inst(func, block, term) else {
        return false;
    };
    let Some(call) = func.dfg.call_info(prev) else {
        return false;
    };
    let effects = func.ctx().func_effects(call.callee());
    effects.never_returns() && effects.always_terminates()
}

fn prev_non_phi_inst(func: &Function, block: BlockId, before: InstId) -> Option<InstId> {
    let mut inst = func.layout.prev_inst_of(before);
    while let Some(prev) = inst {
        if !func.dfg.is_phi(prev) {
            return Some(prev);
        }
        inst = func.layout.prev_inst_of(prev);
    }
    debug_assert_eq!(func.layout.first_inst_of(block), Some(before));
    None
}
