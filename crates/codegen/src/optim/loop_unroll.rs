//! Full unrolling of loops that run a few times. A loop whose blocks form a
//! chain from its header to its latch, as rotation makes of a simple loop,
//! and whose exit test folds to a constant on every iteration given its
//! phis' values on entry, runs a known number of times. When that many
//! copies of its body stay small, they run in sequence, without the back
//! edge:
//!
//! ```text
//! pre:  jump loop                              pre:  jump first
//!                                              first: <body, i = 1>
//! loop: i = phi (1 pre) (i1 loop)              loop: <body, i = 2>
//!       <body>                         =>            jump exit
//!       i1 = add i 1; c = lt i1 3
//!       br c loop exit
//! ```
//!
//! A block of the chain may also branch out of the loop to a block that
//! leaves the function, such as a failed bounds check's panic; each copy
//! keeps its own branch there.
//!
//! Each copy sees its iteration's values: constants where the iteration
//! fixes them, so an index into an array becomes a constant the object and
//! aggregate passes can resolve. The loop's blocks stay as the last
//! iteration, so the values they define keep their uses after the loop; the
//! iterations before them go in new blocks between the preheader and them.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Immediate, InstId, ValueId,
    inst::control_flow::{Br, Jump},
};

use super::simplify_expr::{
    ConstantFacts, ExprFactProvider, SimplifiedResult, simplify_inst_with_facts,
};
use crate::cfg_edit::{clone_inst_before, iter_phis_in_block};

/// The most iterations unrolled.
const MAX_TRIPS: usize = 16;

/// The most instructions all the copies of a body take together.
const MAX_UNROLLED_INSTS: usize = 384;

/// The most blocks in a loop's chain.
const MAX_CHAIN: usize = 8;

#[derive(Default)]
pub struct LoopUnroll;

impl LoopUnroll {
    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let blocks: Vec<_> = func.layout.iter_block().collect();
        let mut changed = false;
        for block in blocks {
            if func.layout.is_block_inserted(block)
                && let Some(plan) = plan(func, &cfg, block)
            {
                unroll(func, &plan);
                cfg.compute(func);
                changed = true;
            }
        }
        changed
    }
}

/// A loop to unroll.
struct Plan {
    /// The chain of the loop's blocks, header first and latch last.
    chain: Vec<BlockId>,
    preheader: BlockId,
    /// The latch's exit.
    exit: BlockId,
    /// The preheader's edge into the loop.
    entry_edge: usize,
    /// Each phi of the header, with its values on entry and around the back
    /// edge.
    phis: Vec<(InstId, ValueId, ValueId, ValueId)>,
    /// The instructions of each block of the chain, but its phis and
    /// terminator.
    bodies: Vec<Vec<InstId>>,
    trips: usize,
}

fn plan(func: &Function, cfg: &ControlFlowGraph, header: BlockId) -> Option<Plan> {
    let (chain, exit, loops_on_nonzero) = loop_chain(func, cfg, header)?;
    let latch = *chain.last()?;
    let mut entries = cfg.preds_of(header).filter(|&&pred| pred != latch);
    let (Some(&preheader), None) = (entries.next(), entries.next()) else {
        return None;
    };
    let entry_term = func.layout.last_inst_of(preheader)?;
    let mut entry_edges = func
        .dfg
        .branch_info(entry_term)?
        .dests()
        .into_iter()
        .enumerate()
        .filter(|&(_, dest)| dest == header)
        .map(|(edge, _)| edge);
    let (Some(entry_edge), None) = (entry_edges.next(), entry_edges.next()) else {
        return None;
    };

    let phis = iter_phis_in_block(func, header)
        .map(|phi| {
            let args = func.dfg.cast_phi(phi)?.args();
            let incoming = |from| args.iter().find(|(_, pred)| *pred == from).map(|&(v, _)| v);
            Some((
                phi,
                func.dfg.inst_result(phi)?,
                incoming(preheader)?,
                incoming(latch)?,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let bodies: Vec<Vec<_>> = chain
        .iter()
        .map(|&block| {
            let term = func.layout.last_inst_of(block);
            func.layout
                .iter_inst(block)
                .filter(|&inst| !func.dfg.is_phi(inst) && Some(inst) != term)
                .collect()
        })
        .collect();
    let cond = *func
        .dfg
        .downcast::<&Br>(func.layout.last_inst_of(latch)?)?
        .cond();

    // Iterate the exit test on constants until it leaves the loop.
    let mut facts = ConstantFacts {
        func,
        known: phis
            .iter()
            .filter_map(|&(_, result, entry, _)| Some((result, func.dfg.value_imm(entry)?)))
            .collect(),
    };
    let trips = (1..=MAX_TRIPS).find_map(|trip| {
        for &inst in bodies.iter().flatten() {
            let &[result] = func.dfg.inst_results(inst) else {
                continue;
            };
            let imm = match simplify_inst_with_facts(func, inst, &facts).result(0) {
                SimplifiedResult::Const(imm) => Some(imm),
                SimplifiedResult::Copy(value) => facts.known_imm(value),
                SimplifiedResult::NoChange => None,
            };
            match imm {
                Some(imm) => facts.known.insert(result, imm),
                None => facts.known.remove(&result),
            };
        }
        let Some(cond) = facts.known_imm(cond) else {
            return Some(None);
        };
        if cond.is_zero() == loops_on_nonzero {
            return Some(Some(trip));
        }
        let next: Vec<(ValueId, Option<Immediate>)> = phis
            .iter()
            .map(|&(_, result, _, back)| (result, facts.known_imm(back)))
            .collect();
        for (result, imm) in next {
            match imm {
                Some(imm) => facts.known.insert(result, imm),
                None => facts.known.remove(&result),
            };
        }
        None
    })??;
    let insts: usize = bodies.iter().map(Vec::len).sum();
    (trips * insts <= MAX_UNROLLED_INSTS).then_some(Plan {
        chain,
        preheader,
        exit,
        entry_edge,
        phis,
        bodies,
        trips,
    })
}

/// The blocks of the loop headed by `header` when they form a chain to a
/// latch that branches back to it or to the exit: each block but the latch
/// continues to the next, which has no other predecessor and no phis, or
/// leaves the function through a side exit (see `side_exit`). Also the
/// exit, and whether the latch loops when its condition is nonzero.
fn loop_chain(
    func: &Function,
    cfg: &ControlFlowGraph,
    header: BlockId,
) -> Option<(Vec<BlockId>, BlockId, bool)> {
    let mut chain = vec![header];
    loop {
        let block = *chain.last()?;
        let term = func.layout.last_inst_of(block)?;
        let dests = func.dfg.branch_info(term)?.dests();
        if let Some(br) = func.dfg.downcast::<&Br>(term) {
            let (nz_dest, z_dest) = (*br.nz_dest(), *br.z_dest());
            match (nz_dest == header, z_dest == header) {
                (true, false) if !chain.contains(&z_dest) => return Some((chain, z_dest, true)),
                (false, true) if !chain.contains(&nz_dest) => {
                    return Some((chain, nz_dest, false));
                }
                (true, true) => return None,
                _ => {}
            }
        }
        let mut next = dests.iter().copied().filter(|&dest| {
            let mut preds = cfg.preds_of(dest);
            !side_exit(func, dest)
                && preds.next() == Some(&block)
                && preds.next().is_none()
                && iter_phis_in_block(func, dest).next().is_none()
                && !chain.contains(&dest)
        });
        let (Some(next), None) = (next.next(), next.next()) else {
            return None;
        };
        if chain.len() == MAX_CHAIN
            || !dests
                .iter()
                .all(|&dest| dest == next || side_exit(func, dest))
        {
            return None;
        }
        chain.push(next);
        // A side exit uses no value of the loop, which its copies leave.
        let defined: FxHashSet<_> = chain
            .iter()
            .flat_map(|&block| func.layout.iter_inst(block))
            .flat_map(|inst| func.dfg.inst_results(inst).iter().copied())
            .collect();
        if dests.iter().filter(|&&dest| dest != next).any(|&dest| {
            func.layout.iter_inst(dest).any(|inst| {
                let mut uses = false;
                func.dfg
                    .inst(inst)
                    .for_each_value(&mut |value| uses |= defined.contains(&value));
                uses
            })
        }) {
            return None;
        }
    }
}

/// Whether `block` leaves the function without branching anywhere and has
/// no phis, so more predecessors change nothing about it.
fn side_exit(func: &Function, block: BlockId) -> bool {
    func.layout
        .last_inst_of(block)
        .is_some_and(|term| func.dfg.branch_info(term).is_none())
        && iter_phis_in_block(func, block).next().is_none()
}

/// Runs the first `trips - 1` iterations in new blocks before the loop's,
/// which run the last.
fn unroll(func: &mut Function, plan: &Plan) {
    let header = plan.chain[0];
    // The phis' values on entry to each iteration.
    let mut values: FxHashMap<ValueId, ValueId> = plan
        .phis
        .iter()
        .map(|&(_, result, entry, _)| (result, entry))
        .collect();
    if plan.trips > 1 {
        let copies: Vec<Vec<BlockId>> = (1..plan.trips)
            .map(|_| {
                plan.chain
                    .iter()
                    .map(|_| {
                        let block = func.dfg.make_block();
                        func.layout.insert_block_before(block, header);
                        block
                    })
                    .collect()
            })
            .collect();
        for (iteration, copy) in copies.iter().enumerate() {
            let mut map = values.clone();
            let next_header = copies.get(iteration + 1).map_or(header, |next| next[0]);
            for (index, (&block, &original)) in copy.iter().zip(&plan.chain).enumerate() {
                // The latch's copy goes on to the next iteration; any other
                // block's to the next block's copy, or out to its side exit,
                // once the copied body defines what its branch tests.
                let term = func
                    .dfg
                    .make_inst(Jump::new_unchecked(func.inst_set(), next_header));
                func.layout.append_inst(term, block);
                for &inst in &plan.bodies[index] {
                    clone_inst_before(func, inst, term, &mut map);
                }
                let Some(&next) = plan.chain.get(index + 1) else {
                    continue;
                };
                let mut branch = func
                    .dfg
                    .clone_inst(func.layout.last_inst_of(original).unwrap());
                branch.for_each_value_mut(&mut |value| {
                    if let Some(&mapped) = map.get(value) {
                        *value = mapped;
                    }
                });
                func.dfg.replace_inst(term, branch);
                let dests = func.dfg.branch_info(term).unwrap().dests();
                for (edge, dest) in dests.into_iter().enumerate() {
                    if dest == next {
                        func.dfg
                            .rewrite_branch_edge_dest(term, edge, copy[index + 1]);
                    }
                }
            }
            values = plan
                .phis
                .iter()
                .map(|&(_, result, _, back)| (result, *map.get(&back).unwrap_or(&back)))
                .collect();
        }
        let entry_term = func.layout.last_inst_of(plan.preheader).unwrap();
        func.dfg
            .rewrite_branch_edge_dest(entry_term, plan.entry_edge, copies[0][0]);
    }

    for &(phi, result, _, _) in &plan.phis {
        func.dfg.change_to_alias(result, values[&result]);
        func.layout.remove_inst(phi);
        func.erase_inst(phi);
    }
    let latch = *plan.chain.last().unwrap();
    let term = func.layout.last_inst_of(latch).unwrap();
    let exit = Jump::new_unchecked(func.inst_set(), plan.exit);
    func.dfg.replace_inst(term, Box::new(exit));
}
