use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Module,
    cfg::ControlFlowGraph,
    inst::{control_flow::BranchKind, data::SymbolRef, evm::inst_set::EvmInstKind},
    isa::{Isa, evm::Evm},
    module::FuncRef,
};

use crate::{
    domtree::DomTree,
    loop_analysis::LoopTree,
    machinst::vcode::{Label, VCode, VCodeFixup, VCodeInst},
    stackalloc::{Allocator, StackifyAlloc},
};
use cranelift_entity::{EntityList, SecondaryMap};

use super::super::{FrameSummary, OpCode, lazy_frame::FrameSite};

pub(crate) fn compute_function_entry_jump_targets(
    module: &Module,
    funcs: &[FuncRef],
) -> FxHashSet<FuncRef> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let mut targets = FxHashSet::default();
    let evm_inst_set = Evm::new(module.ctx.triple).inst_set();

    for &func_ref in funcs {
        module.func_store.view(func_ref, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    match evm_inst_set.resolve_inst(function.dfg.inst(inst)) {
                        EvmInstKind::Call(call) => {
                            let callee = *call.callee();
                            if funcs_set.contains(&callee) {
                                targets.insert(callee);
                            }
                        }
                        EvmInstKind::GetFunctionPtr(get_fn) => {
                            let func = *get_fn.func();
                            if funcs_set.contains(&func) {
                                targets.insert(func);
                            }
                        }
                        EvmInstKind::SymAddr(sym_addr) => {
                            if let SymbolRef::Func(func) = sym_addr.sym()
                                && funcs_set.contains(func)
                            {
                                targets.insert(*func);
                            }
                        }
                        _ => {}
                    }
                }
            }
        });
    }

    targets
}

pub(crate) fn referenced_insn_label_targets(vcode: &VCode<OpCode>) -> FxHashSet<VCodeInst> {
    let mut targets = FxHashSet::default();
    for (_, fixup) in vcode.fixups.values() {
        let VCodeFixup::Label(label) = fixup else {
            continue;
        };
        if let Label::Insn(inst) = vcode.labels[*label] {
            targets.insert(inst);
        }
    }
    targets
}

fn referenced_block_label_targets(vcode: &VCode<OpCode>) -> FxHashSet<BlockId> {
    let mut targets = FxHashSet::default();
    for (_, fixup) in vcode.fixups.values() {
        let VCodeFixup::Label(label) = fixup else {
            continue;
        };
        if let Label::Block(block) = vcode.labels[*label] {
            targets.insert(block);
        }
    }
    targets
}

fn prepend_block_inst(vcode: &mut VCode<OpCode>, block: BlockId, op: OpCode) -> VCodeInst {
    let inst = vcode.insts.push(op);
    vcode.inst_ir[inst] = None.into();

    let existing: Vec<_> = vcode.block_insns(block).collect();
    let mut list: EntityList<VCodeInst> = Default::default();
    list.push(inst, &mut vcode.insts_pool);
    for inst in existing {
        list.push(inst, &mut vcode.insts_pool);
    }
    vcode.blocks[block] = list;

    inst
}

fn ensure_block_starts_with_jumpdest(vcode: &mut VCode<OpCode>, block: BlockId) {
    if vcode
        .block_insns(block)
        .next()
        .is_some_and(|inst| (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
    {
        return;
    }

    prepend_block_inst(vcode, block, OpCode::JUMPDEST);
}

pub(crate) fn materialize_jumpdests(
    vcode: &mut VCode<OpCode>,
    function: &Function,
    block_order: &[BlockId],
    function_entry_jumpdest: bool,
) {
    let jump_targets = referenced_block_label_targets(vcode);
    let entry = function.layout.entry_block();

    for &block in block_order {
        if jump_targets.contains(&block) || (Some(block) == entry && function_entry_jumpdest) {
            ensure_block_starts_with_jumpdest(vcode, block);
        }
    }
}

#[derive(Default)]
pub(crate) struct LateBlockAliasPlan {
    pub(crate) aliases: FxHashMap<BlockId, BlockId>,
    pub(crate) emitted_block_order: Vec<BlockId>,
}

pub(crate) fn compute_late_block_alias_plan(
    function: &Function,
    alloc: &StackifyAlloc,
    frame_summary: &FrameSummary,
    block_order: &[BlockId],
) -> LateBlockAliasPlan {
    let mut raw_alias_targets: SecondaryMap<BlockId, Option<BlockId>> = SecondaryMap::new();
    let entry = function.layout.entry_block();

    for &block in block_order {
        let Some(term) = block_trampoline_jump_inst(function, block) else {
            continue;
        };

        if Some(block) == entry
            || !alloc.read(term, &[]).is_empty()
            || !alloc.write(term, &[]).is_empty()
            || lazy_frame_mentions_trampoline_site(frame_summary, block, term)
        {
            continue;
        }

        let dest = match function
            .dfg
            .branch_info(term)
            .expect("trampoline jump missing branch info")
            .branch_kind()
        {
            BranchKind::Jump(jump) => *jump.dest(),
            BranchKind::Br(_) | BranchKind::BrTable(_) => unreachable!("non-jump trampoline"),
        };
        raw_alias_targets[block] = Some(dest);
    }

    let mut aliases = FxHashMap::default();
    for &block in block_order {
        if raw_alias_targets[block].is_none() {
            continue;
        }

        let mut seen = FxHashSet::default();
        let mut cur = block;
        let canonical = loop {
            if !seen.insert(cur) {
                break None;
            }

            match raw_alias_targets[cur] {
                Some(next) => cur = next,
                None => break Some(cur),
            }
        };

        if let Some(canonical) = canonical
            && canonical != block
        {
            aliases.insert(block, canonical);
        }
    }

    let emitted_block_order = block_order
        .iter()
        .copied()
        .filter(|block| !aliases.contains_key(block))
        .collect();

    LateBlockAliasPlan {
        aliases,
        emitted_block_order,
    }
}

pub(crate) fn rewrite_evm_local_fallthrough_layout(
    function: &Function,
    aliases: &FxHashMap<BlockId, BlockId>,
    mut emitted_block_order: Vec<BlockId>,
) -> Vec<BlockId> {
    if emitted_block_order.len() < 3 {
        return emitted_block_order;
    }

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let mut loops = LoopTree::new();
    loops.compute(&cfg, &dom);

    let mut idx = 0;
    while idx + 2 < emitted_block_order.len() {
        let header = emitted_block_order[idx];
        let exit = emitted_block_order[idx + 1];
        let body = emitted_block_order[idx + 2];
        if is_hot_loop_header_fallthrough_candidate(
            function, &cfg, &loops, aliases, header, exit, body,
        ) {
            tracing::trace!(
                header = header.0,
                body = body.0,
                exit = exit.0,
                "rewrote local EVM fallthrough layout"
            );
            emitted_block_order.swap(idx + 1, idx + 2);
            idx += 3;
        } else {
            idx += 1;
        }
    }

    emitted_block_order
}

fn is_hot_loop_header_fallthrough_candidate(
    function: &Function,
    cfg: &ControlFlowGraph,
    loops: &LoopTree,
    aliases: &FxHashMap<BlockId, BlockId>,
    header: BlockId,
    exit: BlockId,
    body: BlockId,
) -> bool {
    if [header, exit, body]
        .into_iter()
        .any(|block| canonical_late_alias_target(aliases, block) != block)
    {
        return false;
    }

    let Some(lp) = loops.loop_of_block(header) else {
        return false;
    };
    if loops.loop_header(lp) != header
        || !loops.is_in_loop(body, lp)
        || loops.is_in_loop(exit, lp)
        || cfg.pred_num_of(body) != 1
        || cfg.preds_as_slice(body) != [header]
    {
        return false;
    }

    let Some(header_term) = function.layout.last_inst_of(header) else {
        return false;
    };
    let Some(body_term) = function.layout.last_inst_of(body) else {
        return false;
    };
    let Some(exit_term) = function.layout.last_inst_of(exit) else {
        return false;
    };
    if !function.dfg.is_exit(exit_term)
        || function
            .layout
            .iter_inst(body)
            .any(|inst| function.dfg.is_phi(inst))
    {
        return false;
    }

    let Some(header_branch) = function.dfg.branch_info(header_term) else {
        return false;
    };
    let BranchKind::Br(br) = header_branch.branch_kind() else {
        return false;
    };
    if canonical_late_alias_target(aliases, *br.nz_dest()) != exit
        || canonical_late_alias_target(aliases, *br.z_dest()) != body
    {
        return false;
    }

    let Some(body_branch) = function.dfg.branch_info(body_term) else {
        return false;
    };
    let BranchKind::Jump(jump) = body_branch.branch_kind() else {
        return false;
    };

    canonical_late_alias_target(aliases, *jump.dest()) == header
}

fn canonical_late_alias_target(aliases: &FxHashMap<BlockId, BlockId>, block: BlockId) -> BlockId {
    let mut block = block;
    while let Some(&next) = aliases.get(&block) {
        if next == block {
            break;
        }
        block = next;
    }
    block
}

fn block_trampoline_jump_inst(function: &Function, block: BlockId) -> Option<InstId> {
    let term = function.layout.last_inst_of(block)?;
    if !matches!(
        function.dfg.branch_info(term)?.branch_kind(),
        BranchKind::Jump(_)
    ) {
        return None;
    }
    if function
        .layout
        .iter_inst(block)
        .any(|inst| function.dfg.is_phi(inst))
    {
        return None;
    }
    if function
        .layout
        .iter_inst(block)
        .filter(|&inst| !function.dfg.is_phi(inst))
        .count()
        != 1
    {
        return None;
    }

    Some(term)
}

fn lazy_frame_mentions_trampoline_site(
    frame_summary: &FrameSummary,
    block: BlockId,
    term: InstId,
) -> bool {
    let Some(plan) = frame_summary.lowering.as_ref() else {
        return false;
    };

    [
        FrameSite::BlockEntry(block),
        FrameSite::PreInst(term),
        FrameSite::Inst(term),
        FrameSite::PostInst(term),
    ]
    .into_iter()
    .any(|site| {
        plan.enter_before_site(site) || plan.exit_before_site(site) || plan.exit_after_site(site)
    })
}
