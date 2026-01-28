use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};

use crate::{bitset::BitSet, domtree::DomTree, liveness::Liveness};

use super::spill::SpillSet;

#[derive(Clone, Copy, Debug)]
pub(super) struct DefInfo {
    def_block: BlockId,
    /// Monotone per-block index; larger means "later".
    def_index: u32,
}

#[derive(Clone, Debug, Default)]
pub(super) struct BlockTemplate {
    /// Parameter prefix (phi results; plus function args for the entry block).
    pub(super) params: SmallVec<[ValueId; 4]>,
    /// Canonical transfer region (top-first).
    pub(super) transfer: SmallVec<[ValueId; 8]>,
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
) -> SecondaryMap<ValueId, Option<DefInfo>> {
    let mut info: SecondaryMap<ValueId, Option<DefInfo>> = SecondaryMap::new();

    // Treat function arguments as "defined" in the entry block, before any instruction.
    for (idx, &arg) in func.arg_values.iter().enumerate() {
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
            let Some(res) = func.dfg.inst_result(inst) else {
                continue;
            };
            info[res] = Some(DefInfo {
                def_block: block,
                def_index: idx,
            });
            idx = idx.saturating_add(1);
        }
    }

    info
}

pub(super) fn compute_phi_results(
    func: &Function,
) -> SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> {
    let mut phi_results: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> = SecondaryMap::new();
    for block in func.layout.iter_block() {
        let mut results = SmallVec::<[ValueId; 4]>::new();
        for inst in func.layout.iter_inst(block) {
            if !func.dfg.is_phi(inst) {
                break;
            }
            if let Some(res) = func.dfg.inst_result(inst) {
                results.push(res);
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
    // Exclude memory-only (spilled) values. These will be loaded from memory when needed,
    // not carried on the stack.
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
) -> SecondaryMap<BlockId, BitSet<ValueId>> {
    let mut sets: SecondaryMap<BlockId, BitSet<ValueId>> = SecondaryMap::new();
    for block in func.layout.iter_block() {
        let mut set: BitSet<ValueId> = BitSet::default();
        for succ in cfg.succs_of(block) {
            for v in phi_args_for_edge(func, block, *succ) {
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
