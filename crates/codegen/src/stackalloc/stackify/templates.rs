use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};
use std::collections::VecDeque;

use crate::{bitset::BitSet, domtree::DomTree, liveness::Liveness};

use super::{StackifyContext, spill::SpillSet};

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

pub(super) fn compute_templates(
    ctx: &StackifyContext<'_>,
    spill: SpillSet<'_>,
) -> SecondaryMap<BlockId, BlockTemplate> {
    // Compute per-block entry templates:
    //   StackIn(B) = P(B) ++ T(B)
    //
    // `P(B)` is the parameter prefix (phis; plus args at entry).
    //
    // `T(B)` is the transfer region (live-in non-params, excluding `spill_set`), but it is not
    // enforced as a global canonical order. Instead:
    // - along single-predecessor chains we inherit the predecessor's outgoing layout
    // - at join points we use the inherited layout iff all incoming layouts match; otherwise
    //   pick one predecessor layout (preferring loop backedges)
    let mut templates: SecondaryMap<BlockId, BlockTemplate> = SecondaryMap::new();

    // Restrict layout propagation to blocks reachable from `entry`.
    let mut rpo: Vec<BlockId> = ctx.cfg.post_order().collect();
    rpo.reverse();
    let reachable: BitSet<BlockId> = rpo.iter().copied().collect();

    // Precompute `P(B)` and carried live-in sets (non-params, excluding `spill_set`).
    let mut params_map: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> = SecondaryMap::new();
    let mut carry_in_sets: SecondaryMap<BlockId, BitSet<ValueId>> = SecondaryMap::new();
    for block in ctx.func.layout.iter_block() {
        let mut params = SmallVec::<[ValueId; 4]>::new();
        if block == ctx.entry {
            params.extend(ctx.func.arg_values.iter().copied());
        }
        params.extend((&ctx.phi_results)[block].iter().copied());
        params_map[block] = params;

        carry_in_sets[block] = live_in_non_params(
            ctx.liveness,
            ctx.func,
            block,
            ctx.entry,
            &ctx.phi_results,
            spill,
        );
    }

    // Precompute carried live-out sets per block (union of successor carry-in sets).
    let mut carry_out_sets: SecondaryMap<BlockId, BitSet<ValueId>> = SecondaryMap::new();
    for block in ctx.func.layout.iter_block() {
        let mut set: BitSet<ValueId> = BitSet::default();
        for succ in ctx.cfg.succs_of(block) {
            set.union_with(&carry_in_sets[*succ]);
        }
        carry_out_sets[block] = set;
    }

    // Precompute local defs that must be carried out of each block (non-phi instruction results),
    // ordered top-first (later defs nearer the top).
    let mut defs_out_rev: SecondaryMap<BlockId, Vec<ValueId>> = SecondaryMap::new();
    for block in ctx.func.layout.iter_block() {
        let carry_out = &carry_out_sets[block];
        let mut defs: Vec<ValueId> = Vec::new();
        for inst in ctx.func.layout.iter_inst(block) {
            if !ctx.func.dfg.is_phi(inst)
                && let Some(res) = ctx.func.dfg.inst_result(inst)
                && !spill.contains(res)
                && carry_out.contains(res)
            {
                defs.push(res);
            }
        }
        defs.sort_by(|a, b| {
            value_key(*b, &ctx.dom_depth, &ctx.def_info).cmp(&value_key(
                *a,
                &ctx.dom_depth,
                &ctx.def_info,
            ))
        });
        defs_out_rev[block] = defs;
    }

    fn canonical_transfer(
        carry: &BitSet<ValueId>,
        dom_depth: &SecondaryMap<BlockId, u32>,
        def_info: &SecondaryMap<ValueId, Option<DefInfo>>,
    ) -> Vec<ValueId> {
        sort_values_desc(carry.iter().collect(), dom_depth, def_info)
    }

    fn filter_order(order: &[ValueId], keep: &BitSet<ValueId>) -> Vec<ValueId> {
        let mut out: Vec<ValueId> = Vec::new();
        let mut seen: BitSet<ValueId> = BitSet::default();
        for &v in order.iter() {
            if keep.contains(v) && seen.insert(v) {
                out.push(v);
            }
        }
        out
    }

    // Current `T(B)` candidate per block (top-first).
    let mut transfers: SecondaryMap<BlockId, Vec<ValueId>> = SecondaryMap::new();
    for block in ctx.func.layout.iter_block() {
        transfers[block] = canonical_transfer(&carry_in_sets[block], &ctx.dom_depth, &ctx.def_info);
    }

    // Current outgoing order per block (top-first), used to derive inherited layouts for successors.
    let mut out_orders: SecondaryMap<BlockId, Vec<ValueId>> = SecondaryMap::new();
    for &block in rpo.iter() {
        let carry_out = &carry_out_sets[block];
        let mut base: Vec<ValueId> = Vec::new();
        base.extend(params_map[block].iter().copied());
        base.extend(transfers[block].iter().copied());

        let mut out: Vec<ValueId> = Vec::new();
        out.extend(defs_out_rev[block].iter().copied());
        out.extend(filter_order(&base, carry_out));
        out_orders[block] = out;
    }

    // Fixed-point over layouts: propagate transfer orders through the CFG and resolve join
    // disagreements by choosing a predecessor layout (preferring loop backedges).
    // Process blocks in RPO order (dominators before dominated blocks) to improve convergence.
    // `VecDeque` provides FIFO semantics (`pop_front`), avoiding the accidental reverse-RPO
    // schedule we'd get from `Vec::pop`.
    let mut worklist: VecDeque<BlockId> = rpo.iter().copied().collect();
    let mut in_worklist: BitSet<BlockId> = rpo.iter().copied().collect();
    while let Some(block) = worklist.pop_front() {
        in_worklist.remove(block);

        let reachable_preds: Vec<BlockId> = ctx
            .cfg
            .preds_of(block)
            .copied()
            .filter(|pred| reachable.contains(*pred))
            .collect();

        // Entry blocks do not inherit.
        let new_transfer = if block == ctx.entry || reachable_preds.is_empty() {
            canonical_transfer(&carry_in_sets[block], &ctx.dom_depth, &ctx.def_info)
        } else {
            let keep = &carry_in_sets[block];

            // If all incoming layouts match, inherit it directly.
            let mut inherited: Option<Vec<ValueId>> = None;
            let mut conflict = false;
            for &pred in &reachable_preds {
                let cand = filter_order(&out_orders[pred], keep);
                match inherited.as_ref() {
                    None => inherited = Some(cand),
                    Some(first) => {
                        if *first != cand {
                            conflict = true;
                            break;
                        }
                    }
                }
            }
            if !conflict {
                inherited.unwrap_or_default()
            } else {
                // Choose one incoming layout as the "version" for this join point and normalize
                // other edges to it. Prefer loop backedges so the loop body can stabilize its
                // own layout across iterations.
                let preferred_pred = reachable_preds
                    .iter()
                    .copied()
                    .find(|pred| ctx.dom.dominates(block, *pred))
                    .unwrap_or(reachable_preds[0]);
                filter_order(&out_orders[preferred_pred], keep)
            }
        };

        if transfers[block] == new_transfer {
            continue;
        }

        transfers[block] = new_transfer;

        // Update this block's outgoing order and revisit successors.
        let carry_out = &carry_out_sets[block];
        let mut base: Vec<ValueId> = Vec::new();
        base.extend(params_map[block].iter().copied());
        base.extend(transfers[block].iter().copied());

        let mut out: Vec<ValueId> = Vec::new();
        out.extend(defs_out_rev[block].iter().copied());
        out.extend(filter_order(&base, carry_out));
        out_orders[block] = out;

        for succ in ctx.cfg.succs_of(block) {
            if reachable.contains(*succ) && in_worklist.insert(*succ) {
                worklist.push_back(*succ);
            }
        }
    }

    // Build final templates, falling back to canonical for unreachable blocks (for determinism).
    for block in ctx.func.layout.iter_block() {
        let params = params_map[block].clone();
        let transfer = if reachable.contains(block) {
            transfers[block].clone()
        } else {
            canonical_transfer(&carry_in_sets[block], &ctx.dom_depth, &ctx.def_info)
        };

        templates[block] = BlockTemplate {
            params,
            transfer: transfer.into_iter().collect(),
        };
    }

    templates
}

fn live_in_non_params(
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
