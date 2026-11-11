//! Full unrolling of loops that run a few times. A loop whose blocks form a
//! chain from its header to its latch, and whose exit test folds to a
//! constant on every iteration given its phis' values on entry, runs a known
//! number of times. When that many copies of its body stay small, they run
//! in sequence, without the back edge:
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
//! The test ends the latch, as rotation leaves a loop, or the header, as a
//! size pipeline, which doesn't rotate, leaves it. A header test runs once
//! more than the body. Its last run stays in the header, which jumps to the
//! exit, and the body's blocks go:
//!
//! ```text
//! pre:  jump loop                              pre:   jump first
//!                                              first: <test, i = 0>
//! loop: i = phi (0 pre) (i1 body)                     jump copy
//!       c = lt i 1                             copy:  <body, i = 0>
//!       br c body exit                 =>             jump loop
//! body: <body>                                 loop:  <test, i = 1>
//!       i1 = add i 1                                  jump exit
//!       jump loop
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
//!
//! A size pipeline unrolls a loop only when its copies, but the instructions
//! and branches that fold to constants in them, take no more instructions
//! than the loop with its phis and terminators.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Immediate, InstId, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
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
pub struct LoopUnroll {
    /// Whether to unroll only the loops that unrolling makes no larger, as
    /// size pipelines do.
    small: bool,
}

impl LoopUnroll {
    /// Unrolls only the loops whose copies, once their constants fold, take
    /// no more instructions than the loop.
    pub fn small() -> Self {
        Self { small: true }
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let blocks: Vec<_> = func.layout.iter_block().collect();
        let mut changed = false;
        for block in blocks {
            if func.layout.is_block_inserted(block)
                && let Some(plan) = plan(func, &cfg, block, self.small)
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
    /// The test's exit.
    exit: BlockId,
    /// Whether the header tests whether to leave the loop, not the latch.
    tested_at_header: bool,
    /// The preheader's edge into the loop.
    entry_edge: usize,
    /// Each phi of the header, with its values on entry and around the back
    /// edge.
    phis: Vec<(InstId, ValueId, ValueId, ValueId)>,
    /// The instructions of each block of the chain, but its phis and
    /// terminator.
    bodies: Vec<Vec<InstId>>,
    /// How many times the test runs.
    trips: usize,
}

/// The blocks of a loop that form a chain (see `loop_chain`).
struct Chain {
    blocks: Vec<BlockId>,
    exit: BlockId,
    /// Whether the test stays in the loop when its condition is nonzero.
    loops_on_nonzero: bool,
    tested_at_header: bool,
}

fn plan(func: &Function, cfg: &ControlFlowGraph, header: BlockId, small: bool) -> Option<Plan> {
    let Chain {
        blocks: chain,
        exit,
        loops_on_nonzero,
        tested_at_header,
    } = loop_chain(func, cfg, header)?;
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
    let test = if tested_at_header { 0 } else { chain.len() - 1 };
    let cond = *func
        .dfg
        .downcast::<&Br>(func.layout.last_inst_of(chain[test])?)?
        .cond();

    // Iterate the loop on constants until its test leaves it, counting the
    // instructions and branches of its copies that don't fold.
    let mut facts = ConstantFacts {
        func,
        known: phis
            .iter()
            .filter_map(|&(_, result, entry, _)| Some((result, func.dfg.value_imm(entry)?)))
            .collect(),
    };
    let mut kept = 0;
    let trips = (1..=MAX_TRIPS).find_map(|trip| {
        for (index, body) in bodies.iter().enumerate() {
            for &inst in body {
                let &[result] = func.dfg.inst_results(inst) else {
                    kept += 1;
                    continue;
                };
                let simplified = simplify_inst_with_facts(func, inst, &facts).result(0);
                let imm = match simplified {
                    SimplifiedResult::Const(imm) => Some(imm),
                    SimplifiedResult::Copy(value) => facts.known_imm(value),
                    SimplifiedResult::NoChange => None,
                };
                kept += usize::from(simplified.is_no_change());
                match imm {
                    Some(imm) => facts.known.insert(result, imm),
                    None => facts.known.remove(&result),
                };
            }
            if index == test {
                let Some(cond) = facts.known_imm(cond) else {
                    return Some(None);
                };
                if cond.is_zero() == loops_on_nonzero {
                    return Some(Some(trip));
                }
            } else if let Some(term) = func.layout.last_inst_of(chain[index])
                && let Some(br) = func.dfg.downcast::<&Br>(term)
                && facts.known_imm(*br.cond()).is_none()
            {
                // A branch to a side exit stays in its copy.
                kept += 1;
            }
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
    let fits = if small {
        kept <= insts + phis.len() + chain.len()
    } else {
        trips * insts <= MAX_UNROLLED_INSTS
    };
    fits.then_some(Plan {
        chain,
        preheader,
        exit,
        tested_at_header,
        entry_edge,
        phis,
        bodies,
        trips,
    })
}

/// The blocks of the loop headed by `header` when they form a chain from it
/// to a latch: each block but the latch continues to the next, which has no
/// other predecessor and no phis, or leaves the function through a side exit
/// (see `side_exit`). The loop's one test of whether to leave ends the latch,
/// which branches back to the header or to the exit, or the header, which
/// branches to the next block or to the exit, and then the latch jumps back.
fn loop_chain(func: &Function, cfg: &ControlFlowGraph, header: BlockId) -> Option<Chain> {
    if let Some(chain) = extend_chain(func, cfg, vec![header], None) {
        return Some(chain);
    }
    let br = func
        .dfg
        .downcast::<&Br>(func.layout.last_inst_of(header)?)?;
    let (nz_dest, z_dest) = (*br.nz_dest(), *br.z_dest());
    [(nz_dest, z_dest, true), (z_dest, nz_dest, false)]
        .into_iter()
        .find_map(|(next, exit, loops_on_nonzero)| {
            if next == exit || exit == header || !continues(func, cfg, header, next, &[header]) {
                return None;
            }
            extend_chain(
                func,
                cfg,
                vec![header, next],
                Some((exit, loops_on_nonzero)),
            )
        })
}

/// Extends `chain` to its latch. With a header test, its exit and whether it
/// stays in the loop on nonzero, the latch jumps back to the header;
/// otherwise the latch holds the test.
fn extend_chain(
    func: &Function,
    cfg: &ControlFlowGraph,
    mut chain: Vec<BlockId>,
    header_test: Option<(BlockId, bool)>,
) -> Option<Chain> {
    let header = chain[0];
    loop {
        let block = *chain.last()?;
        let term = func.layout.last_inst_of(block)?;
        let dests = func.dfg.branch_info(term)?.dests();
        match header_test {
            Some((exit, loops_on_nonzero)) => {
                if func
                    .dfg
                    .downcast::<&Jump>(term)
                    .is_some_and(|jump| *jump.dest() == header)
                {
                    return Some(Chain {
                        blocks: chain,
                        exit,
                        loops_on_nonzero,
                        tested_at_header: true,
                    });
                }
            }
            None => {
                if let Some(br) = func.dfg.downcast::<&Br>(term) {
                    let (nz_dest, z_dest) = (*br.nz_dest(), *br.z_dest());
                    let chain_end = |exit, loops_on_nonzero| Chain {
                        blocks: chain.clone(),
                        exit,
                        loops_on_nonzero,
                        tested_at_header: false,
                    };
                    match (nz_dest == header, z_dest == header) {
                        (true, false) if !chain.contains(&z_dest) => {
                            return Some(chain_end(z_dest, true));
                        }
                        (false, true) if !chain.contains(&nz_dest) => {
                            return Some(chain_end(nz_dest, false));
                        }
                        (true, true) => return None,
                        _ => {}
                    }
                }
            }
        }
        let mut next = dests
            .iter()
            .copied()
            .filter(|&dest| continues(func, cfg, block, dest, &chain));
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

/// Whether the chain can continue from `block` to `dest`: `dest` is entered
/// only from `block`, has no phis, isn't a side exit and isn't in `chain`.
fn continues(
    func: &Function,
    cfg: &ControlFlowGraph,
    block: BlockId,
    dest: BlockId,
    chain: &[BlockId],
) -> bool {
    let mut preds = cfg.preds_of(dest);
    !side_exit(func, dest)
        && preds.next() == Some(&block)
        && preds.next().is_none()
        && iter_phis_in_block(func, dest).next().is_none()
        && !chain.contains(&dest)
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
                // The latch's copy goes on to the next iteration, and a header
                // test's copy, which stays in the loop, to the next block's;
                // any other block's to the next block's copy, or out to its
                // side exit, once the copied body defines what its branch
                // tests.
                let tests = plan.tested_at_header && index == 0;
                let dest = if tests { copy[1] } else { next_header };
                let term = func
                    .dfg
                    .make_inst(Jump::new_unchecked(func.inst_set(), dest));
                func.layout.append_inst(term, block);
                for &inst in &plan.bodies[index] {
                    clone_inst_before(func, inst, term, &mut map);
                }
                let Some(&next) = plan.chain.get(index + 1).filter(|_| !tests) else {
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
    let test = if plan.tested_at_header {
        header
    } else {
        *plan.chain.last().unwrap()
    };
    let term = func.layout.last_inst_of(test).unwrap();
    let exit = Jump::new_unchecked(func.inst_set(), plan.exit);
    func.dfg.replace_inst(term, Box::new(exit));
    // The header's last test leaves the loop, so its body doesn't run again.
    // A block's values are used only by the blocks after it.
    if plan.tested_at_header {
        for &block in plan.chain[1..].iter().rev() {
            InstInserter::at_location(CursorLocation::BlockTop(block)).remove_block(func);
        }
    }
}
