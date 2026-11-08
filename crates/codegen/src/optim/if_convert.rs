//! If-conversion: a branch whose two paths meet at once becomes a jump, and
//! each phi of the join a `select` on the branch's condition. Each path goes
//! straight to the join or through a block of its own holding a few
//! instructions that can run on either path, which run before the jump.
//!
//! What both paths run is bounded in 64-bit word operations: a division, a
//! multiplication wider than a word or an EVM arithmetic operation never
//! runs where its path would not, and a select costs a move per word.
//!
//! A native target chooses with a conditional move instead of a branch that
//! mispredicts when the condition depends on data: a modular reduction keeps
//! a sum or its difference from the modulus, `if borrow { t } else { d }`,
//! about half the time each. This runs at the end of native pipelines, after
//! the passes that use branches: jump threading, boolean phi folding (a phi
//! of 1 and 0 is better as `zext c`) and switch formation.

use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        BinaryInstKind, InstClassKind,
        control_flow::{Br, Jump},
        logic::Select,
    },
};

use super::simplify_expr::integral_bit_width;
use crate::cfg_edit::iter_phis_in_block;

/// The most word operations run on both paths from one block of a path.
const MAX_ARM_COST: usize = 4;

/// The most words a join's selects choose.
const MAX_SELECT_WORDS: usize = 8;

#[derive(Default)]
pub struct IfConvert;

impl IfConvert {
    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            if func.layout.is_block_inserted(block) && convert(func, &cfg, block).is_some() {
                cfg.compute(func);
                changed = true;
            }
        }
        changed
    }
}

/// Converts the branch ending `block`, if its paths meet at once.
fn convert(func: &mut Function, cfg: &ControlFlowGraph, block: BlockId) -> Option<()> {
    let term = func.layout.last_inst_of(block)?;
    let br = func.dfg.downcast::<&Br>(term)?;
    let (cond, nz_dest, z_dest) = (*br.cond(), *br.nz_dest(), *br.z_dest());
    if nz_dest == z_dest {
        return None;
    }

    // Each path enters the join from `block` or from a block of its own, so
    // `block`, and with it `cond`, dominates the join.
    let (join, nz_from, z_from) = match (
        arm_join(func, cfg, block, nz_dest),
        arm_join(func, cfg, block, z_dest),
    ) {
        (Some(nz_join), Some(z_join)) if nz_join == z_join => (nz_join, nz_dest, z_dest),
        (Some(join), None) if join == z_dest => (join, nz_dest, block),
        (None, Some(join)) if join == nz_dest => (join, block, z_dest),
        _ => return None,
    };
    if join == block || cfg.preds_of(join).count() != 2 {
        return None;
    }

    let phis: SmallVec<[InstId; 8]> = iter_phis_in_block(func, join).collect();
    let selects = phis
        .iter()
        .map(|&phi| {
            let result = func.dfg.inst_result(phi)?;
            let ty = func.dfg.value_ty(result);
            let args = func.dfg.cast_phi(phi)?.args();
            let incoming = |from| args.iter().find(|(_, pred)| *pred == from).map(|&(v, _)| v);
            (ty.is_integral() || ty.is_pointer(func.ctx())).then_some((
                phi,
                result,
                incoming(nz_from)?,
                incoming(z_from)?,
            ))
        })
        .collect::<Option<SmallVec<[_; 8]>>>()?;
    let words: usize = selects
        .iter()
        .map(|&(_, result, _, _)| words(func.dfg.value_ty(result)))
        .sum();
    if selects.is_empty() || words > MAX_SELECT_WORDS {
        return None;
    }

    let has_select = func.inst_set().has_select()?;
    for arm in [nz_from, z_from] {
        if arm == block {
            continue;
        }
        let body: SmallVec<[InstId; MAX_ARM_COST]> = func.layout.iter_inst(arm).collect();
        for &inst in &body[..body.len() - 1] {
            func.layout.remove_inst(inst);
            func.layout.insert_inst_before(inst, term);
        }
    }
    let before = func.layout.first_inst_of(join)?;
    let before = match phis.last() {
        Some(&last) => func.layout.next_inst_of(last).unwrap_or(before),
        None => before,
    };
    for (phi, result, on_nz, on_z) in selects {
        let value = if on_nz == on_z {
            on_nz
        } else {
            insert_select(
                func,
                phi,
                before,
                Select::new(has_select, cond, on_nz, on_z),
            )
        };
        func.dfg.change_to_alias(result, value);
        func.layout.remove_inst(phi);
        func.erase_inst(phi);
    }

    let jump = Jump::new_unchecked(func.inst_set(), join);
    func.dfg.replace_inst(term, Box::new(jump));
    for arm in [nz_from, z_from] {
        if arm != block {
            InstInserter::at_location(CursorLocation::BlockTop(arm)).remove_block(func);
        }
    }
    Some(())
}

fn insert_select(func: &mut Function, phi: InstId, before: InstId, select: Select) -> ValueId {
    let ty = func.dfg.value_ty(*select.then_value());
    let inst = func.dfg.make_inst(select);
    func.layout.insert_inst_before(inst, before);
    func.propagate_inst_attribution(inst, phi);
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    func.dfg.attach_results(inst, &[value]);
    value
}

/// The join `dest` jumps to, when `dest` is entered only from `from` and
/// holds, besides that jump, no phis and instructions that compute values,
/// can run on either path and cost at most `MAX_ARM_COST`.
fn arm_join(
    func: &Function,
    cfg: &ControlFlowGraph,
    from: BlockId,
    dest: BlockId,
) -> Option<BlockId> {
    let mut preds = cfg.preds_of(dest);
    if preds.next() != Some(&from) || preds.next().is_some() {
        return None;
    }
    let jump = func.layout.last_inst_of(dest)?;
    let target = *func.dfg.downcast::<&Jump>(jump)?.dest();
    let mut cost = 0;
    for inst in func.layout.iter_inst(dest).take_while(|&inst| inst != jump) {
        if func.dfg.is_phi(inst)
            || !func.dfg.has_value_semantics(inst)
            || !func.dfg.can_speculate(inst)
        {
            return None;
        }
        cost += speculation_cost(func, inst)?;
    }
    (target != dest && cost <= MAX_ARM_COST).then_some(target)
}

/// What running `inst` where its path would not costs, in word operations:
/// nothing for a division, a multiplication wider than a word, an EVM
/// arithmetic operation or an aggregate, which are too costly.
fn speculation_cost(func: &Function, inst: InstId) -> Option<usize> {
    let ty = func.dfg.value_ty(*func.dfg.inst_results(inst).first()?);
    let wide = !ty.is_integral() || words(ty) > 1;
    match func.dfg.inst(inst).kind() {
        InstClassKind::Binary(
            BinaryInstKind::Sdiv
            | BinaryInstKind::Udiv
            | BinaryInstKind::Umod
            | BinaryInstKind::Smod
            | BinaryInstKind::EvmUdiv
            | BinaryInstKind::EvmSdiv
            | BinaryInstKind::EvmUdivo
            | BinaryInstKind::EvmSdivo
            | BinaryInstKind::EvmUmod
            | BinaryInstKind::EvmSmod
            | BinaryInstKind::EvmUmodo
            | BinaryInstKind::EvmSmodo
            | BinaryInstKind::EvmUmulsat
            | BinaryInstKind::EvmSmulsat
            | BinaryInstKind::EvmExp,
        ) => None,
        InstClassKind::Binary(
            BinaryInstKind::Mul
            | BinaryInstKind::Umulo
            | BinaryInstKind::Umulsat
            | BinaryInstKind::Smulo
            | BinaryInstKind::Smulsat,
        ) => (!wide).then_some(3),
        InstClassKind::Opaque if func.dfg.inst(inst).as_text().starts_with("evm_") => None,
        _ if ty.is_integral() => Some(words(ty)),
        _ if ty.is_pointer(func.ctx()) => Some(1),
        _ => None,
    }
}

/// The 64-bit words a value of integral type `ty` takes; one otherwise.
fn words(ty: Type) -> usize {
    integral_bit_width(ty).map_or(1, |bits| bits.div_ceil(64))
}
