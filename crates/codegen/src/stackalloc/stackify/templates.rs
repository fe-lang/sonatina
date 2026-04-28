use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};

use crate::{bitset::BitSet, domtree::DomTree, liveness::Liveness};

use super::{
    builder::StackifyContext,
    spill::SpillSet,
    sym_stack::{StackItem, SymStack},
};

pub(super) type TransferOrder = SmallVec<[ValueId; 8]>;

#[derive(Clone, Copy, Debug)]
pub(super) struct DefInfo {
    def_block: BlockId,
    /// Monotone per-block index; larger means "later".
    def_index: u32,
}

#[derive(Clone, Debug, Default)]
pub(super) struct BlockTemplate {
    /// Stack-resident parameter prefix (entry args; non-spilled phi results elsewhere).
    pub(super) params: SmallVec<[ValueId; 4]>,
    /// Transfer region (top-first).
    transfer: Option<TransferOrder>,
}

impl BlockTemplate {
    pub(super) fn new(params: SmallVec<[ValueId; 4]>) -> Self {
        Self {
            params,
            transfer: None,
        }
    }

    pub(super) fn transfer(&self) -> &TransferOrder {
        self.transfer.as_ref().expect("block template is frozen")
    }

    pub(super) fn freeze_transfer(&mut self, transfer: TransferOrder) {
        self.transfer.get_or_insert(transfer);
    }
}

pub(super) struct BlockInterfaces {
    pub(super) params: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    pub(super) carry_in: SecondaryMap<BlockId, BitSet<ValueId>>,
}

pub(super) fn compute_block_interfaces(
    ctx: &StackifyContext<'_>,
    spill: SpillSet<'_>,
) -> BlockInterfaces {
    let mut params: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> = SecondaryMap::new();
    let mut carry_in: SecondaryMap<BlockId, BitSet<ValueId>> = SecondaryMap::new();

    for block in ctx.func.layout.iter_block() {
        let mut block_params = SmallVec::<[ValueId; 4]>::new();
        if block == ctx.entry {
            block_params.extend(ctx.func.arg_values.iter().copied());
        }
        block_params.extend(
            ctx.phi_results[block]
                .iter()
                .copied()
                .filter(|v| !spill.contains(*v)),
        );

        let carry = live_in_non_params(
            ctx.liveness,
            ctx.func,
            block,
            ctx.entry,
            &ctx.phi_results,
            spill,
        );
        params[block] = block_params;
        carry_in[block] = carry;
    }

    BlockInterfaces { params, carry_in }
}

pub(super) fn project_transfer(stack: &SymStack, carry_in: &BitSet<ValueId>) -> TransferOrder {
    let mut out = TransferOrder::new();
    let mut seen: BitSet<ValueId> = BitSet::default();

    let limit = stack.len_above_func_ret();
    for i in 0..limit {
        let Some(StackItem::Value(v)) = stack.item_at(i) else {
            continue;
        };
        if carry_in.contains(*v) && seen.insert(*v) {
            out.push(*v);
        }
    }

    out
}

pub(super) fn choose_transfer(
    ctx: &StackifyContext<'_>,
    block: BlockId,
    candidates: &[(BlockId, TransferOrder)],
) -> TransferOrder {
    debug_assert!(!candidates.is_empty());

    let first = &candidates[0].1;
    if candidates.iter().all(|(_, cand)| cand == first) {
        return first.clone();
    }

    if let Some((_pred, cand)) = candidates
        .iter()
        .filter(|(pred, _)| ctx.dom.dominates(block, *pred))
        .min_by_key(|(pred, _)| pred.as_u32())
    {
        return cand.clone();
    }

    candidates
        .iter()
        .min_by(|(a_pred, a), (b_pred, b)| {
            lex_cmp(a, b).then_with(|| a_pred.as_u32().cmp(&b_pred.as_u32()))
        })
        .map(|(_, cand)| cand.clone())
        .unwrap_or_default()
}

fn lex_cmp(a: &[ValueId], b: &[ValueId]) -> std::cmp::Ordering {
    a.iter()
        .map(|v| v.as_u32())
        .cmp(b.iter().map(|v| v.as_u32()))
}

pub(super) fn compute_dom_depth(dom: &DomTree, entry: BlockId) -> SecondaryMap<BlockId, u32> {
    let mut depth = SecondaryMap::<BlockId, u32>::new();
    depth[entry] = 0;
    for &b in dom.rpo().iter().skip(1) {
        let d = dom
            .idom_of(b)
            .and_then(|idom| depth.get(idom).copied())
            .unwrap_or(0);
        depth[b] = d.saturating_add(1);
    }
    depth
}

pub(super) fn compute_def_info(
    func: &Function,
    entry: BlockId,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> SecondaryMap<ValueId, Option<DefInfo>> {
    let mut info: SecondaryMap<ValueId, Option<DefInfo>> = SecondaryMap::new();

    // Treat function arguments as "defined" in the entry block, before any instruction.
    for (idx, &arg_orig) in func.arg_values.iter().enumerate() {
        let arg = value_aliases[arg_orig].unwrap_or(arg_orig);
        if arg != arg_orig {
            continue;
        }
        info[arg] = Some(DefInfo {
            def_block: entry,
            def_index: idx as u32,
        });
    }

    for block in func.layout.iter_block() {
        let mut idx: u32 = if block == entry {
            func.arg_values.len() as u32
        } else {
            0
        };
        for inst in func.layout.iter_inst(block) {
            for &res_orig in func.dfg.inst_results(inst) {
                let res = value_aliases[res_orig].unwrap_or(res_orig);
                if res != res_orig {
                    continue;
                }
                info[res] = Some(DefInfo {
                    def_block: block,
                    def_index: idx,
                });
                idx = idx.saturating_add(1);
            }
        }
    }

    info
}

pub(super) fn compute_phi_results(
    func: &Function,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> {
    let mut phi_results: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> = SecondaryMap::new();
    for block in func.layout.iter_block() {
        let mut results = SmallVec::<[ValueId; 4]>::new();
        let mut seen: BitSet<ValueId> = BitSet::default();
        for inst in func.layout.iter_inst(block) {
            if !func.dfg.is_phi(inst) {
                break;
            }
            if let Some(res) = func.dfg.inst_result(inst) {
                let res = value_aliases[res].unwrap_or(res);
                if seen.insert(res) {
                    results.push(res);
                }
            }
        }
        phi_results[block] = results;
    }
    phi_results
}

pub(super) fn canonical_transfer_order(
    carry: &BitSet<ValueId>,
    dom_depth: &SecondaryMap<BlockId, u32>,
    def_info: &SecondaryMap<ValueId, Option<DefInfo>>,
) -> SmallVec<[ValueId; 8]> {
    sort_values_desc(carry.iter().collect(), dom_depth, def_info)
        .into_iter()
        .collect()
}

pub(super) fn live_in_non_params(
    liveness: &Liveness,
    func: &Function,
    block: BlockId,
    entry: BlockId,
    phi_results: &SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    spill: SpillSet<'_>,
) -> BitSet<ValueId> {
    let mut set = liveness.block_live_ins(block).clone();
    // Remove parameters (phi results; and args for the entry block).
    for &p in phi_results[block].iter() {
        set.remove(p);
    }
    if block == entry {
        for &a in func.arg_values.iter() {
            set.remove(a);
        }
    }
    // Exclude memory-only values.
    set.difference_with(spill.bitset());
    set
}

fn value_key(
    v: ValueId,
    dom_depth: &SecondaryMap<BlockId, u32>,
    def_info: &SecondaryMap<ValueId, Option<DefInfo>>,
) -> (u32, u32, u32, u32) {
    let Some(info) = def_info[v] else {
        return (0, 0, 0, v.as_u32());
    };
    let dd = dom_depth.get(info.def_block).copied().unwrap_or(0);
    (dd, info.def_block.as_u32(), info.def_index, v.as_u32())
}

pub(super) fn function_has_internal_return(func: &Function) -> bool {
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if func.dfg.is_return(inst) {
                return true;
            }
        }
    }
    false
}

fn sort_values_desc(
    mut values: Vec<ValueId>,
    dom_depth: &SecondaryMap<BlockId, u32>,
    def_info: &SecondaryMap<ValueId, Option<DefInfo>>,
) -> Vec<ValueId> {
    values.sort_by(|a, b| {
        value_key(*b, dom_depth, def_info).cmp(&value_key(*a, dom_depth, def_info))
    });
    values
}

pub(super) fn compute_phi_out_sources(
    func: &Function,
    cfg: &ControlFlowGraph,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> SecondaryMap<BlockId, BitSet<ValueId>> {
    let mut sets: SecondaryMap<BlockId, BitSet<ValueId>> = SecondaryMap::new();
    for block in func.layout.iter_block() {
        let mut set: BitSet<ValueId> = BitSet::default();
        for succ in cfg.succs_of(block) {
            for v in phi_args_for_edge(func, block, *succ) {
                let v = value_aliases[v].unwrap_or(v);
                if !func.dfg.value_is_imm(v) {
                    set.insert(v);
                }
            }
        }
        sets[block] = set;
    }
    sets
}

pub(super) fn phi_args_for_edge(
    func: &Function,
    pred: BlockId,
    succ: BlockId,
) -> SmallVec<[ValueId; 4]> {
    func.layout
        .iter_inst(succ)
        .map_while(|inst| {
            func.dfg.cast_phi(inst).and_then(|phi| {
                phi.args()
                    .iter()
                    .find_map(|(val, block)| (*block == pred).then_some(*val))
            })
        })
        .collect()
}
