//! Conservative SSA definedness, with optional point-specific memory evidence.
//!
//! Memory reads, call results and parameters are never undef: uninitialized
//! memory holds arbitrary fixed bits, and an undef argument or return value
//! reaches the other side as one arbitrary value. Undef arises only from
//! `undef` itself and from operations with undefined results, and spreads
//! through the instructions that use it. A division by a divisor that may be
//! zero has an undefined result, unless every path to it passes a branch that
//! found the divisor nonzero, as a checked division's does.

use std::cell::OnceCell;

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    ControlFlowGraph, Function, I256, Immediate, InstId, Value, ValueId,
    effects::AccessKind,
    inst::{BinaryInstKind, InstClassKind, UnaryInstKind, control_flow::Br, data},
    types::EnumVariantRef,
};

pub(crate) fn value_may_be_undef(
    func: &Function,
    value: ValueId,
    cache: &mut FxHashMap<ValueId, bool>,
    mut override_value: impl FnMut(ValueId) -> Option<bool>,
) -> bool {
    let guards = Guards::default();
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
                Value::Inst { inst, .. } => {
                    inst_result_may_be_undef(func, *inst, &guards, |used| {
                        cache.get(&used).copied().unwrap_or(true)
                    })
                }
            };
            cache.insert(value, may_be_undef);
            continue;
        }
        if !visiting.insert(value) {
            cache.insert(value, true);
            continue;
        }
        stack.push((value, true));
        if let Value::Inst { inst, .. } = func.dfg.value(value)
            && !is_freeze(func, *inst)
        {
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

fn is_freeze(func: &Function, inst: InstId) -> bool {
    func.dfg.downcast::<&data::Freeze>(inst).is_some()
}

/// Reads and calls, whose results are never undef.
pub(crate) fn is_read_or_call(func: &Function, inst: InstId) -> bool {
    func.dfg.is_call(inst)
        || func.dfg.downcast::<&data::ObjLoad>(inst).is_some()
        || func.dfg.downcast::<&data::EnumGetTag>(inst).is_some()
        || func
            .dfg
            .effects(inst)
            .accesses
            .iter()
            .any(|access| access.kind == AccessKind::Read)
}

/// Whether field `idx` of `aggregate` may be undef, following `insert_value`
/// and phis to the values that set it. A cycle of phis adds no undef.
fn field_may_be_undef(
    func: &Function,
    aggregate: ValueId,
    idx: I256,
    operand_may_be_undef: &impl Fn(ValueId) -> bool,
    visiting: &mut FxHashSet<ValueId>,
) -> bool {
    if !visiting.insert(aggregate) {
        return false;
    }
    let Some(inst) = func.dfg.value_inst(aggregate) else {
        return operand_may_be_undef(aggregate);
    };
    if let Some(insert) = func.dfg.downcast::<&data::InsertValue>(inst) {
        return match func.dfg.value_imm(*insert.idx()) {
            Some(field) if field.as_i256() == idx => operand_may_be_undef(*insert.value()),
            Some(_) => {
                field_may_be_undef(func, *insert.dest(), idx, operand_may_be_undef, visiting)
            }
            None => operand_may_be_undef(aggregate),
        };
    }
    if let Some(phi) = func.dfg.cast_phi(inst) {
        return phi
            .args()
            .iter()
            .any(|&(arg, _)| field_may_be_undef(func, arg, idx, operand_may_be_undef, visiting));
    }
    operand_may_be_undef(aggregate)
}

/// Whether `field` of `variant` in the enum `value` may be undef, following
/// phis to the `enum.make`s that built it.
fn variant_field_may_be_undef(
    func: &Function,
    value: ValueId,
    variant: EnumVariantRef,
    field: I256,
    operand_may_be_undef: &impl Fn(ValueId) -> bool,
    visiting: &mut FxHashSet<ValueId>,
) -> bool {
    if !visiting.insert(value) {
        return false;
    }
    let Some(inst) = func.dfg.value_inst(value) else {
        return operand_may_be_undef(value);
    };
    if let Some(make) = func.dfg.downcast::<&data::EnumMake>(inst) {
        // An extract runs only on its own variant, which a variant check
        // ensures; another variant's `enum.make` never reaches it.
        return *make.variant() == variant
            && usize::try_from(field.to_u256().low_u64())
                .ok()
                .and_then(|field| make.values().get(field))
                .is_none_or(|&field| operand_may_be_undef(field));
    }
    if let Some(phi) = func.dfg.cast_phi(inst) {
        return phi.args().iter().any(|&(arg, _)| {
            variant_field_may_be_undef(func, arg, variant, field, operand_may_be_undef, visiting)
        });
    }
    operand_may_be_undef(value)
}

fn inst_result_may_be_undef(
    func: &Function,
    inst: InstId,
    guards: &Guards,
    operand_may_be_undef: impl Fn(ValueId) -> bool,
) -> bool {
    if is_freeze(func, inst) {
        return false;
    }
    // A field is as defined as the value last inserted there, even into an
    // aggregate that started as undef.
    if let Some(extract) = func.dfg.downcast::<&data::ExtractValue>(inst)
        && let Some(idx) = func.dfg.value_imm(*extract.idx())
    {
        return field_may_be_undef(
            func,
            *extract.dest(),
            idx.as_i256(),
            &operand_may_be_undef,
            &mut FxHashSet::default(),
        );
    }
    if let Some(extract) = func.dfg.downcast::<&data::EnumExtract>(inst)
        && let Some(field) = func.dfg.value_imm(*extract.field())
    {
        return variant_field_may_be_undef(
            func,
            *extract.value(),
            *extract.variant(),
            field.as_i256(),
            &operand_may_be_undef,
            &mut FxHashSet::default(),
        );
    }
    let inst_data = func.dfg.inst(inst);
    let values = inst_data.collect_values();
    if values.iter().copied().any(&operand_may_be_undef) {
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
        let [_, divisor] = values.as_slice() else {
            return true;
        };
        return match func.dfg.value_imm(*divisor) {
            Some(divisor) => divisor.is_zero(),
            None => !guards.rule_out_zero(func, inst, *divisor),
        };
    }

    false
}

/// The control flow that division guards are found in, built on first use.
#[derive(Default)]
struct Guards(OnceCell<ControlFlowGraph>);

impl Guards {
    /// Whether every path to the division `inst` leaves a branch that tests
    /// `divisor` against zero along the edge where it is nonzero: the
    /// division's block, or one in the chain of single predecessors above
    /// it, is entered only by that edge, and the chain stops at the entry
    /// block.
    fn rule_out_zero(&self, func: &Function, inst: InstId, divisor: ValueId) -> bool {
        let cfg = self.0.get_or_init(|| {
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            cfg
        });
        let Some(mut block) = func.layout.try_inst_block(inst) else {
            return false;
        };
        let entry = func.layout.entry_block();
        let mut visited = FxHashSet::default();
        // The call enters the entry block with any divisor, whatever its
        // predecessors in the CFG.
        while Some(block) != entry && visited.insert(block) {
            let mut preds = cfg.preds_of(block);
            let (Some(&pred), None) = (preds.next(), preds.next()) else {
                return false;
            };
            if let Some(term) = func.layout.last_inst_of(pred)
                && let Some(br) = func.dfg.downcast::<&Br>(term)
                && br.nz_dest() != br.z_dest()
                && let Some(holds_if_nonzero) = zero_test(func, *br.cond(), divisor)
                && block
                    == if holds_if_nonzero {
                        *br.nz_dest()
                    } else {
                        *br.z_dest()
                    }
            {
                return true;
            }
            block = pred;
        }
        false
    }
}

/// For a branch condition comparing `value` with zero, whether the
/// condition holds when `value` is nonzero.
fn zero_test(func: &Function, cond: ValueId, value: ValueId) -> Option<bool> {
    let inst = func.dfg.value_inst(cond)?;
    let zero = |operand: ValueId| func.dfg.value_imm(operand).is_some_and(Immediate::is_zero);
    match (
        func.dfg.inst(inst).kind(),
        func.dfg.inst(inst).collect_values().as_slice(),
    ) {
        (InstClassKind::Unary(UnaryInstKind::IsZero), &[operand]) if operand == value => {
            Some(false)
        }
        (InstClassKind::Binary(kind), &[lhs, rhs]) => {
            let compared = (lhs == value && zero(rhs)) || (rhs == value && zero(lhs));
            match kind {
                BinaryInstKind::Eq if compared => Some(false),
                BinaryInstKind::Ne if compared => Some(true),
                // Unsigned: above zero is nonzero.
                BinaryInstKind::Gt if lhs == value && zero(rhs) => Some(true),
                BinaryInstKind::Lt if zero(lhs) && rhs == value => Some(true),
                _ => None,
            }
        }
        _ => None,
    }
}
