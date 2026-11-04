//! Return threading: a block that only returns a phi of an aggregate becomes,
//! in each predecessor that jumps to it, a `return` of that predecessor's input.
//!
//! An aggregate phi owns storage that its incoming edges copy into. A value that
//! a `return` names can live in the return buffer and needs no copy at all, and a
//! call in a `return` can pass the buffer straight through. Each `return` takes
//! an epilogue, which costs a few bytes natively, so this pass belongs in native
//! pipelines.

use smallvec::smallvec;
use sonatina_ir::{
    BlockId, Function, InstId, ValueId,
    inst::control_flow::{Jump, Return},
};

use crate::cfg_edit::{CfgEditor, CleanupMode};

#[derive(Default)]
pub struct ReturnThread;

impl ReturnThread {
    pub fn run(&mut self, func: &mut Function) -> bool {
        let is = func.inst_set();
        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        let mut changed = false;
        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            let Some(phi) = returned_phi(editor.func(), block) else {
                continue;
            };
            let preds: Vec<_> = editor.cfg().preds_of(block).copied().collect();
            let mut threaded = 0;
            for &pred in &preds {
                let func = editor.func_mut();
                let Some(jump) = func.layout.last_inst_of(pred) else {
                    continue;
                };
                if func.dfg.downcast::<&Jump>(jump).is_none() {
                    continue;
                }
                let input = phi_input(func, phi, pred);
                func.dfg.edit_phi(phi, |phi| phi.remove_phi_arg(pred));
                editor.truncate_block_from_inst(jump);
                editor.append_inst_with_result(
                    pred,
                    Box::new(Return::new_unchecked(is, smallvec![input].into())),
                    None,
                );
                threaded += 1;
            }
            if threaded > 0 {
                editor.recompute_cfg();
                changed = true;
            }
            if threaded == preds.len() {
                editor.delete_block_unreachable(block);
            }
        }
        changed
    }
}

/// The phi of `block`, if the block holds nothing but it and a `return` of its
/// aggregate result.
fn returned_phi(func: &Function, block: BlockId) -> Option<InstId> {
    let dfg = &func.dfg;
    let mut insts = func.layout.iter_inst(block);
    let (phi, ret) = (insts.next()?, insts.next()?);
    if insts.next().is_some() {
        return None;
    }
    if !dfg.is_phi(phi) {
        return None;
    }
    let result = dfg.inst_result(phi)?;
    let args = dfg.downcast::<&Return>(ret)?.args();
    (args.as_slice() == [result]
        && dfg.value_ty(result).is_compound()
        && dfg.users(result).count() == 1)
        .then_some(phi)
}

fn phi_input(func: &Function, phi: InstId, pred: BlockId) -> ValueId {
    let phi = func.dfg.cast_phi(phi).expect("returned_phi found a phi");
    let input = phi.args().iter().find(|&&(_, block)| block == pred);
    input.expect("a phi has an input for each predecessor").0
}
