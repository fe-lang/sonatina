//! Compare-subtract fusion: an unsigned comparison `a < b` and the `sub a b`
//! instructions it dominates become one `usubo a b` in its place, whose borrow
//! is the comparison and whose difference is each subtraction.
//!
//! A guard like `if cost > gas { .. } gas - cost` otherwise leaves the
//! subtraction free to move. Cranelift places a pure instruction at its uses,
//! so a difference used on every edge out of a dispatch block is recomputed on
//! each edge, and its operands stay live across the branch. `usub_overflow`
//! has two results and stays where the branch needs its borrow. LLVM's
//! CodeGenPrepare forms `usub.with.overflow` for the same reason. The EVM
//! backend legalizes `usubo` back into a subtraction and a comparison, so this
//! pass belongs in native pipelines.
//!
//! A difference used in only a few blocks stays apart: Cranelift computes it
//! in each and branches on the comparison's flags, where `usub_overflow`'s
//! borrow would take a `setb` and a `test` before the branch. A guard that
//! exits a loop, for example, uses its difference on the back edge and on
//! the exit.

use std::iter;

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    inst::{BinaryInstKind, InstClassKind, arith::Usubo},
};

use crate::domtree::DomTree;

/// The fewest blocks using a difference for which one `usubo` is cheaper
/// than a subtraction in each.
const MIN_USE_BLOCKS: usize = 4;

#[derive(Default)]
pub struct CompareSubFusion;

impl CompareSubFusion {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function, dom: &DomTree) -> bool {
        let mut subs = FxHashMap::<(ValueId, ValueId), Vec<InstId>>::default();
        let mut compares = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                let InstClassKind::Binary(kind) = func.dfg.inst(inst).kind() else {
                    continue;
                };
                let [lhs, rhs] = func.dfg.inst(inst).collect_values()[..] else {
                    continue;
                };
                match kind {
                    BinaryInstKind::Sub => subs.entry((lhs, rhs)).or_default().push(inst),
                    BinaryInstKind::Lt => compares.push((inst, lhs, rhs)),
                    BinaryInstKind::Gt => compares.push((inst, rhs, lhs)),
                    _ => {}
                }
            }
        }

        let mut changed = false;
        for (compare, lhs, rhs) in compares {
            let fused: Vec<_> = subs
                .get(&(lhs, rhs))
                .into_iter()
                .flatten()
                .copied()
                .filter(|&sub| {
                    func.layout.is_inst_inserted(sub) && dominates(func, dom, compare, sub)
                })
                .collect();
            let use_blocks: FxHashSet<_> = fused
                .iter()
                .flat_map(|&sub| {
                    let result = func.dfg.inst_result(sub).expect("a sub has a result");
                    use_blocks(func, result)
                })
                .collect();
            if use_blocks.len() < MIN_USE_BLOCKS {
                continue;
            }

            let usubo = func
                .dfg
                .make_inst(Usubo::new_unchecked(func.inst_set(), lhs, rhs));
            let difference = func.dfg.make_value(Value::Inst {
                inst: usubo,
                result_idx: 0,
                ty: func.dfg.value_ty(lhs),
            });
            let borrow = func.dfg.make_value(Value::Inst {
                inst: usubo,
                result_idx: 1,
                ty: Type::I1,
            });
            func.dfg.attach_results(usubo, &[difference, borrow]);
            func.layout.insert_inst_before(usubo, compare);
            func.propagate_inst_attribution(usubo, compare);

            let condition = func
                .dfg
                .inst_result(compare)
                .expect("a comparison has a result");
            func.dfg.change_to_alias(condition, borrow);
            func.layout.remove_inst(compare);
            func.erase_inst(compare);
            for sub in fused {
                let result = func.dfg.inst_result(sub).expect("a sub has a result");
                func.dfg.change_to_alias(result, difference);
                func.layout.remove_inst(sub);
                func.erase_inst(sub);
            }
            changed = true;
        }
        changed
    }
}

/// The blocks that use `value`, counting a phi argument as a use in its
/// incoming block, which passes it on the edge.
fn use_blocks(func: &Function, value: ValueId) -> Vec<BlockId> {
    func.dfg
        .users(value)
        .flat_map(|&user| match func.dfg.cast_phi(user) {
            Some(phi) => phi
                .args()
                .iter()
                .filter(|(arg, _)| *arg == value)
                .map(|&(_, block)| block)
                .collect(),
            None => vec![func.layout.inst_block(user)],
        })
        .collect()
}

/// Whether `inst` comes before `user` in its block or `inst`'s block
/// dominates `user`'s.
fn dominates(func: &Function, dom: &DomTree, inst: InstId, user: InstId) -> bool {
    let block = func.layout.inst_block(inst);
    if func.layout.inst_block(user) != block {
        return dom.dominates(block, func.layout.inst_block(user));
    }
    iter::successors(func.layout.next_inst_of(inst), |&next| {
        func.layout.next_inst_of(next)
    })
    .any(|next| next == user)
}
