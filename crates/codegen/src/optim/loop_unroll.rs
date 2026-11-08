//! Full unrolling of loops that run a few times. A loop of one block, which
//! rotation makes of a simple loop, whose exit test folds to a constant on
//! every iteration given its phis' values on entry, runs a known number of
//! times. When that many copies of its body stay small, they run in
//! sequence, without the back edge:
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
//! Each copy sees its iteration's values: constants where the iteration
//! fixes them, so an index into an array becomes a constant the object and
//! aggregate passes can resolve. The loop block stays as the last
//! iteration, so the values it defines keep their uses after the loop; the
//! iterations before it go in a new block between the preheader and it.

use rustc_hash::FxHashMap;
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

#[derive(Default)]
pub struct LoopUnroll;

impl LoopUnroll {
    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let blocks: Vec<_> = func.layout.iter_block().collect();
        let mut changed = false;
        for block in blocks {
            if let Some(plan) = plan(func, &cfg, block) {
                unroll(func, &plan);
                cfg.compute(func);
                changed = true;
            }
        }
        changed
    }
}

/// A loop block to unroll.
struct Plan {
    block: BlockId,
    preheader: BlockId,
    exit: BlockId,
    /// The preheader's edge into the loop.
    entry_edge: usize,
    /// Each phi, with its values on entry and around the back edge.
    phis: Vec<(InstId, ValueId, ValueId, ValueId)>,
    body: Vec<InstId>,
    trips: usize,
}

fn plan(func: &Function, cfg: &ControlFlowGraph, block: BlockId) -> Option<Plan> {
    let term = func.layout.last_inst_of(block)?;
    let br = func.dfg.downcast::<&Br>(term)?;
    let (cond, nz_dest, z_dest) = (*br.cond(), *br.nz_dest(), *br.z_dest());
    let (exit, loops_on_nonzero) = match (nz_dest == block, z_dest == block) {
        (true, false) => (z_dest, true),
        (false, true) => (nz_dest, false),
        _ => return None,
    };
    let mut entries = cfg.preds_of(block).filter(|&&pred| pred != block);
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
        .filter(|&(_, dest)| dest == block)
        .map(|(edge, _)| edge);
    let (Some(entry_edge), None) = (entry_edges.next(), entry_edges.next()) else {
        return None;
    };

    let phis = iter_phis_in_block(func, block)
        .map(|phi| {
            let args = func.dfg.cast_phi(phi)?.args();
            let incoming = |from| args.iter().find(|(_, pred)| *pred == from).map(|&(v, _)| v);
            Some((
                phi,
                func.dfg.inst_result(phi)?,
                incoming(preheader)?,
                incoming(block)?,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let body: Vec<_> = func
        .layout
        .iter_inst(block)
        .filter(|&inst| !func.dfg.is_phi(inst) && inst != term)
        .collect();

    // Iterate the exit test on constants until it leaves the loop.
    let mut facts = ConstantFacts {
        func,
        known: phis
            .iter()
            .filter_map(|&(_, result, entry, _)| Some((result, func.dfg.value_imm(entry)?)))
            .collect(),
    };
    let trips = (1..=MAX_TRIPS).find_map(|trip| {
        for &inst in &body {
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
    (trips * body.len() <= MAX_UNROLLED_INSTS).then_some(Plan {
        block,
        preheader,
        exit,
        entry_edge,
        phis,
        body,
        trips,
    })
}

/// Runs the first `trips - 1` iterations in a new block before the loop
/// block, which runs the last.
fn unroll(func: &mut Function, plan: &Plan) {
    // The phis' values on entry to each iteration.
    let mut values: FxHashMap<ValueId, ValueId> = plan
        .phis
        .iter()
        .map(|&(_, result, entry, _)| (result, entry))
        .collect();
    if plan.trips > 1 {
        let first = func.dfg.make_block();
        func.layout.insert_block_before(first, plan.block);
        let jump = func
            .dfg
            .make_inst(Jump::new_unchecked(func.inst_set(), plan.block));
        func.layout.append_inst(jump, first);
        for _ in 1..plan.trips {
            let mut map = values.clone();
            for &inst in &plan.body {
                clone_inst_before(func, inst, jump, &mut map);
            }
            values = plan
                .phis
                .iter()
                .map(|&(_, result, _, back)| (result, *map.get(&back).unwrap_or(&back)))
                .collect();
        }
        let entry_term = func.layout.last_inst_of(plan.preheader).unwrap();
        func.dfg
            .rewrite_branch_edge_dest(entry_term, plan.entry_edge, first);
    }

    for &(phi, result, _, _) in &plan.phis {
        func.dfg.change_to_alias(result, values[&result]);
        func.layout.remove_inst(phi);
        func.erase_inst(phi);
    }
    let term = func.layout.last_inst_of(plan.block).unwrap();
    let exit = Jump::new_unchecked(func.inst_set(), plan.exit);
    func.dfg.replace_inst(term, Box::new(exit));
}
