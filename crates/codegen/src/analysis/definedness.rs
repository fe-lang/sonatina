//! Conservative SSA definedness, with optional point-specific memory evidence.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Immediate, InstId, Value, ValueId,
    inst::{BinaryInstKind, InstClassKind},
};

pub(crate) fn value_may_be_undef(
    func: &Function,
    value: ValueId,
    cache: &mut FxHashMap<ValueId, bool>,
    mut override_value: impl FnMut(ValueId) -> Option<bool>,
) -> bool {
    let mut visiting = FxHashSet::default();
    let mut stack = vec![(value, false)];
    while let Some((value, post_order)) = stack.pop() {
        if cache.contains_key(&value) {
            continue;
        }
        if let Some(may_be_undef) = override_value(value) {
            cache.insert(value, may_be_undef);
            continue;
        }
        if post_order {
            visiting.remove(&value);
            let may_be_undef = match func.dfg.value(value) {
                Value::Undef { .. } => true,
                Value::Immediate { .. } | Value::Arg { .. } | Value::Global { .. } => false,
                Value::Inst { inst, .. } => inst_result_may_be_undef(func, *inst, cache),
            };
            cache.insert(value, may_be_undef);
            continue;
        }
        if !visiting.insert(value) {
            cache.insert(value, true);
            continue;
        }
        stack.push((value, true));
        if let Value::Inst { inst, .. } = func.dfg.value(value) {
            for used in func.dfg.inst(*inst).collect_values().into_iter().rev() {
                if cache.contains_key(&used) {
                    continue;
                }
                if visiting.contains(&used) {
                    cache.insert(used, true);
                } else {
                    stack.push((used, false));
                }
            }
        }
    }
    cache.get(&value).copied().unwrap_or(true)
}

fn inst_result_may_be_undef(
    func: &Function,
    inst: InstId,
    cache: &FxHashMap<ValueId, bool>,
) -> bool {
    let inst_data = func.dfg.inst(inst);
    let values = inst_data.collect_values();
    if values
        .iter()
        .copied()
        .any(|value| cache.get(&value).copied().unwrap_or(true))
    {
        return true;
    }

    if let InstClassKind::Binary(kind) = inst_data.kind()
        && matches!(
            kind,
            BinaryInstKind::Udiv
                | BinaryInstKind::Sdiv
                | BinaryInstKind::Umod
                | BinaryInstKind::Smod
        )
    {
        let [_, rhs] = values.as_slice() else {
            return true;
        };
        return func.dfg.value_imm(*rhs).is_none_or(Immediate::is_zero);
    }

    false
}
