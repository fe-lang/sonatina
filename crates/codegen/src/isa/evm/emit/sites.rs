use std::borrow::Cow;

use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt,
    inst::evm::machine_inst_set::EvmMachineInstKind,
    isa::{Isa, evm::EvmMachine},
};

use super::split_at_continuation;
use crate::stackalloc::{ActionSite, Actions, Allocator};

/// The action lists `alloc` runs in `block`, with their sites, in the order
/// emission runs them (`Lower::lower`, `lower_insn`): the function's entry
/// actions in its entry block, then for each instruction other than a phi the
/// actions before it, before each `br_table` case compare, and after it if code
/// follows it.
pub(crate) fn block_action_sites<'a, A: Allocator + ?Sized>(
    function: &'a Function,
    alloc: &'a A,
    block: BlockId,
) -> impl Iterator<Item = (ActionSite, Cow<'a, Actions>)> {
    let inst_set = EvmMachine::new(function.dfg.ctx.triple).inst_set();
    let entry = (function.layout.entry_block() == Some(block)).then(|| {
        (
            ActionSite::Entry,
            Cow::Owned(alloc.enter_function(function)),
        )
    });
    let insts = function.layout.iter_inst(block).flat_map(move |inst| {
        let data = inst_set.resolve_inst(function.dfg.inst(inst));
        let before = !matches!(data, EvmMachineInstKind::Phi(_));
        let after = emits_after(alloc, inst, &data);
        let cases = match data {
            EvmMachineInstKind::BrTable(br) => br.table().len(),
            _ => 0,
        };
        before
            .then(|| {
                (
                    ActionSite::Before(inst),
                    Cow::Borrowed(alloc.pre_inst(inst)),
                )
            })
            .into_iter()
            .chain((0..cases).map(move |case| {
                (
                    ActionSite::Case(inst, case),
                    Cow::Borrowed(alloc.br_table_case(inst, case)),
                )
            }))
            .chain(after.then(|| {
                (
                    ActionSite::After(inst),
                    Cow::Borrowed(alloc.post_inst(inst)),
                )
            }))
    });
    entry.into_iter().chain(insts)
}

/// Whether emission runs `inst`'s actions after it. No code follows a
/// terminator or a call without a continuation, and phis emit nothing.
pub(crate) fn emits_after<A: Allocator + ?Sized>(
    alloc: &A,
    inst: InstId,
    data: &EvmMachineInstKind,
) -> bool {
    match data {
        EvmMachineInstKind::Phi(_)
        | EvmMachineInstKind::Jump(_)
        | EvmMachineInstKind::Br(_)
        | EvmMachineInstKind::BrTable(_)
        | EvmMachineInstKind::Unreachable(_)
        | EvmMachineInstKind::Return(_) => false,
        EvmMachineInstKind::Call(_) => split_at_continuation(alloc.pre_inst(inst)).is_some(),
        _ => true,
    }
}
