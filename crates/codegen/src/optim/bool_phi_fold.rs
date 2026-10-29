//! Boolean phi folding: at the join of a branch on `c`, a phi that takes 1
//! (`true` for an `i1`) from one arm and 0 from the other becomes `zext c`, or
//! `zext (is_zero c)` when the arms are the other way around. A branch whose
//! join is left with no phis, and whose arms hold nothing but their jumps,
//! becomes a jump.
//!
//! Fe lowers `if c { 1 } else { 0 }` to such a diamond. Cranelift keeps it as
//! a branch and materializes each constant, four registers for an `i256`,
//! where a `zext` is a `setcc` and a move. Jump threading needs the diamond
//! when the join branches on the phi again, so this pass runs after it, at
//! the end of native pipelines.

use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Immediate, Inst, InstId, Type, Value,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        cast::Zext,
        cmp::IsZero,
        control_flow::{Br, Jump},
    },
};

use crate::cfg_edit::iter_phis_in_block;

#[derive(Default)]
pub struct BoolPhiFold;

impl BoolPhiFold {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            if func.layout.is_block_inserted(block) && fold_branch(func, &cfg, block).is_some() {
                cfg.compute(func);
                changed = true;
            }
        }
        changed
    }
}

/// Folds the boolean phis at the join of the branch ending `block`, and the
/// branch itself if no other phi is left there.
fn fold_branch(func: &mut Function, cfg: &ControlFlowGraph, block: BlockId) -> Option<()> {
    let term = func.layout.last_inst_of(block)?;
    let br = func.dfg.downcast::<&Br>(term)?;
    let (cond, nz_dest, z_dest) = (*br.cond(), *br.nz_dest(), *br.z_dest());
    if nz_dest == z_dest {
        return None;
    }

    // Each arm enters the join from `block` or from an empty block of its own,
    // so `block`, and with it `cond`, dominates the join.
    let (join, nz_from, z_from) = match (
        forwarded_dest(func, cfg, block, nz_dest),
        forwarded_dest(func, cfg, block, z_dest),
    ) {
        (Some(nz_join), Some(z_join)) if nz_join == z_join => (nz_join, nz_dest, z_dest),
        (Some(join), None) if join == z_dest => (join, nz_dest, block),
        (None, Some(join)) if join == nz_dest => (join, block, z_dest),
        _ => return None,
    };
    if join == block || cfg.preds_of(join).count() != 2 {
        return None;
    }

    let phis: Vec<_> = iter_phis_in_block(func, join).collect();
    let folds: Vec<_> = phis
        .iter()
        .filter_map(|&phi| {
            let args = func.dfg.cast_phi(phi)?.args();
            let incoming = |from| {
                let (value, _) = args.iter().find(|(_, pred)| *pred == from)?;
                func.dfg.value_imm(*value)
            };
            let (on_nz, on_z) = (incoming(nz_from)?, incoming(z_from)?);
            let result = func.dfg.inst_result(phi)?;
            let one = |imm: Immediate| imm.is_one() || imm == Immediate::I1(true);
            let boolean = one(on_nz) && on_z.is_zero() || on_nz.is_zero() && one(on_z);
            (boolean && func.dfg.value_ty(result).is_integral()).then_some((
                phi,
                result,
                on_nz.is_zero(),
            ))
        })
        .collect();
    if folds.is_empty() {
        return None;
    }

    let is = func.inst_set();
    let (has_zext, has_is_zero) = (is.has_zext()?, is.has_is_zero()?);
    let before = func.layout.next_inst_of(*phis.last()?)?;
    let insert = |func: &mut Function, source: InstId, data: Box<dyn Inst>, ty: Type| {
        let inst = func.dfg.make_inst_dyn(data);
        func.layout.insert_inst_before(inst, before);
        func.propagate_inst_attribution(inst, source);
        let value = func.dfg.make_value(Value::Inst {
            inst,
            result_idx: 0,
            ty,
        });
        func.dfg.attach_results(inst, &[value]);
        value
    };
    let mut negation = None;
    for &(phi, result, negated) in &folds {
        let bit = if negated {
            *negation.get_or_insert_with(|| {
                insert(
                    func,
                    phi,
                    Box::new(IsZero::new(has_is_zero, cond)),
                    Type::I1,
                )
            })
        } else {
            cond
        };
        let ty = func.dfg.value_ty(result);
        let value = if ty == Type::I1 {
            bit
        } else {
            insert(func, phi, Box::new(Zext::new(has_zext, bit, ty)), ty)
        };
        func.dfg.change_to_alias(result, value);
        func.layout.remove_inst(phi);
        func.erase_inst(phi);
    }

    if folds.len() == phis.len() {
        let jump = Jump::new_unchecked(func.inst_set(), join);
        func.dfg.replace_inst(term, Box::new(jump));
        for arm in [nz_from, z_from] {
            if arm != block {
                InstInserter::at_location(CursorLocation::BlockTop(arm)).remove_block(func);
            }
        }
    }
    Some(())
}

/// The block `dest` jumps to, if `dest` holds only that jump and is entered
/// only from `from`.
fn forwarded_dest(
    func: &Function,
    cfg: &ControlFlowGraph,
    from: BlockId,
    dest: BlockId,
) -> Option<BlockId> {
    let jump = func.layout.first_inst_of(dest)?;
    let target = *func.dfg.cast_jump(jump)?.dest();
    let mut preds = cfg.preds_of(dest);
    (preds.next() == Some(&from) && preds.next().is_none() && target != dest).then_some(target)
}
