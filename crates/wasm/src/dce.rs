//! Removal of operators whose values nothing uses. The translation computes
//! every limb of a wide operation and every value a lowering may need, though
//! a use often reads only some of them, and WAFFLE's backend writes every
//! value it cannot place under its one use to a local, used or not.

use rustc_hash::FxHashMap;
use waffle::{FuncDecl, FunctionBody, Module, Value, ValueDef};

pub(super) fn run(module: &mut Module<'_>) {
    for func in module.funcs.values_mut() {
        if let FuncDecl::Body(_, _, body) = func {
            remove_unused(body);
        }
    }
}

/// Removes the pure single-result operators that nothing uses, and then those
/// that only they used. A call, a memory access and an operator that may trap
/// have effects, so they stay.
fn remove_unused(body: &mut FunctionBody) {
    let mut uses = FxHashMap::<Value, u32>::default();
    for block in body.blocks.values() {
        for &inst in &block.insts {
            body.values[inst].visit_uses(&body.arg_pool, |used| {
                *uses.entry(body.resolve_alias(used)).or_default() += 1;
            });
        }
        block.terminator.visit_uses(|used| {
            *uses.entry(body.resolve_alias(used)).or_default() += 1;
        });
    }
    // A value is defined before its uses in its block, so a pass over the
    // block in reverse sees a value's operands after the value. An operand in
    // a dominating block is seen on the next pass.
    let mut removed = true;
    while removed {
        removed = false;
        for block in body.blocks.iter() {
            let insts = std::mem::take(&mut body.blocks[block].insts);
            let mut kept = Vec::with_capacity(insts.len());
            for &inst in insts.iter().rev() {
                let unused = uses.get(&inst).is_none_or(|&count| count == 0);
                let pure = matches!(
                    &body.values[inst],
                    ValueDef::Operator(op, _, types) if op.is_pure() && types.len() == 1
                );
                if unused && pure {
                    body.values[inst].visit_uses(&body.arg_pool, |used| {
                        if let Some(count) = uses.get_mut(&body.resolve_alias(used)) {
                            *count -= 1;
                        }
                    });
                    removed = true;
                } else {
                    kept.push(inst);
                }
            }
            kept.reverse();
            body.blocks[block].insts = kept;
        }
    }
}
