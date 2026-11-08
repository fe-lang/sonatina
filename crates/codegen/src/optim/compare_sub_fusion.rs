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
//! The x64 backend branches on the borrow in the flags, so the `usubo` costs
//! what the comparison did and each subtraction is saved. A minuend used
//! after the comparison too, such as a stack depth a fault path reports,
//! stays live past the `usubo`, which then subtracts from a copy of it; its
//! difference is fused only when used in many blocks. The destinations of a
//! tail switch count as the switch's block: the backend makes their calls
//! one indirect tail call there.
//!
//! An overflow test `b > MAX - a` (or `MAX - a < b`, or with `not a`) is the
//! carry of `a + b`: it becomes `uaddo a b`, whose sum replaces the
//! additions of `a` and `b` it dominates. For wide integers the test
//! otherwise subtracts from a constant and compares limb by limb before the
//! addition it guards.

use std::iter;

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    inst::{
        BinaryInstKind, InstClassKind, UnaryInstKind,
        arith::{Uaddo, Usubo},
    },
};

use crate::domtree::DomTree;

/// The fewest blocks using a difference for which one `usubo` on a copy of a
/// live minuend is cheaper than a subtraction in each.
const MIN_USE_BLOCKS: usize = 4;

#[derive(Default)]
pub struct CompareSubFusion;

impl CompareSubFusion {
    pub fn new() -> Self {
        Self
    }

    /// `tail_switches` are the function's tail switches, the `br_table`s
    /// whose destinations each tail-call with the same arguments.
    pub fn run(&mut self, func: &mut Function, dom: &DomTree, tail_switches: &[InstId]) -> bool {
        let switch_blocks: FxHashMap<_, _> = tail_switches
            .iter()
            .flat_map(|&br_table| {
                let block = func.layout.inst_block(br_table);
                let dests = func
                    .dfg
                    .branch_info(br_table)
                    .expect("a tail switch is a branch")
                    .dests();
                dests.into_iter().map(move |dest| (dest, block))
            })
            .collect();
        let mut subs = FxHashMap::<(ValueId, ValueId), Vec<InstId>>::default();
        let mut adds = FxHashMap::<(ValueId, ValueId), Vec<InstId>>::default();
        let mut compares = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                match binary_operands(func, inst) {
                    Some((BinaryInstKind::Sub, lhs, rhs)) => {
                        subs.entry((lhs, rhs)).or_default().push(inst)
                    }
                    Some((BinaryInstKind::Add | BinaryInstKind::Uaddo, lhs, rhs)) => {
                        adds.entry(unordered(lhs, rhs)).or_default().push(inst)
                    }
                    Some((BinaryInstKind::Lt | BinaryInstKind::Gt, ..)) => compares.push(inst),
                    _ => {}
                }
            }
        }

        let mut changed = false;
        for compare in compares {
            // An earlier fusion renames a difference this comparison reads.
            let (lhs, rhs) = match binary_operands(func, compare) {
                Some((BinaryInstKind::Lt, lhs, rhs)) => (lhs, rhs),
                Some((BinaryInstKind::Gt, lhs, rhs)) => (rhs, lhs),
                _ => unreachable!("a collected comparison is never rewritten into another kind"),
            };
            if let Some(addend) = complement_of(func, lhs) {
                let additions = adds.remove(&unordered(addend, rhs)).unwrap_or_default();
                fuse_add_overflow(func, dom, compare, addend, rhs, additions);
                changed = true;
                continue;
            }
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
                .map(|block| switch_blocks.get(&block).copied().unwrap_or(block))
                .collect();
            // A minuend used after the comparison stays live past the
            // `usubo`, which then subtracts from a copy of it.
            let minuend_live = func.dfg.users(lhs).any(|&user| {
                user != compare && !fused.contains(&user) && dominates(func, dom, compare, user)
            });
            if fused.is_empty() || (minuend_live && use_blocks.len() < MIN_USE_BLOCKS) {
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
                // Subtractions of the difference now subtract the `usubo`'s.
                for user in func.dfg.change_to_alias(result, difference) {
                    if let Some((BinaryInstKind::Sub, lhs, rhs)) = binary_operands(func, user) {
                        subs.entry((lhs, rhs)).or_default().push(user);
                    }
                }
                func.layout.remove_inst(sub);
                func.erase_inst(sub);
            }
            changed = true;
        }
        changed
    }
}

/// Replaces `compare`, the test `MAX - a < b`, with `uaddo a b`, whose sum
/// and carry replace the `additions` of `a` and `b` that it dominates.
fn fuse_add_overflow(
    func: &mut Function,
    dom: &DomTree,
    compare: InstId,
    a: ValueId,
    b: ValueId,
    additions: Vec<InstId>,
) {
    let uaddo = func
        .dfg
        .make_inst(Uaddo::new_unchecked(func.inst_set(), a, b));
    let sum = func.dfg.make_value(Value::Inst {
        inst: uaddo,
        result_idx: 0,
        ty: func.dfg.value_ty(a),
    });
    let carry = func.dfg.make_value(Value::Inst {
        inst: uaddo,
        result_idx: 1,
        ty: Type::I1,
    });
    func.dfg.attach_results(uaddo, &[sum, carry]);
    func.layout.insert_inst_before(uaddo, compare);
    func.propagate_inst_attribution(uaddo, compare);

    let condition = func
        .dfg
        .inst_result(compare)
        .expect("a comparison has a result");
    func.dfg.change_to_alias(condition, carry);
    func.layout.remove_inst(compare);
    func.erase_inst(compare);

    for addition in additions {
        if !func.layout.is_inst_inserted(addition) || !dominates(func, dom, uaddo, addition) {
            continue;
        }
        let results = func.dfg.inst_results(addition).to_vec();
        for (result, replacement) in results.into_iter().zip([sum, carry]) {
            func.dfg.change_to_alias(result, replacement);
        }
        func.layout.remove_inst(addition);
        func.erase_inst(addition);
    }
}

/// `a` where `value` is `MAX - a` or `not a` of an integer type.
fn complement_of(func: &Function, value: ValueId) -> Option<ValueId> {
    let inst = func.dfg.value_inst(value)?;
    let data = func.dfg.inst(inst);
    let complemented = match (data.kind(), &data.collect_values()[..]) {
        (InstClassKind::Binary(BinaryInstKind::Sub), &[max, a])
            if func.dfg.value_imm(max).is_some_and(|max| max.is_all_one()) =>
        {
            a
        }
        (InstClassKind::Unary(UnaryInstKind::Not), &[a]) => a,
        _ => return None,
    };
    func.dfg
        .value_ty(complemented)
        .is_integral()
        .then_some(complemented)
}

/// `(lhs, rhs)` in a fixed order, for commutative operations.
fn unordered(lhs: ValueId, rhs: ValueId) -> (ValueId, ValueId) {
    (lhs.min(rhs), lhs.max(rhs))
}

/// The kind and operands of a binary instruction.
fn binary_operands(func: &Function, inst: InstId) -> Option<(BinaryInstKind, ValueId, ValueId)> {
    let InstClassKind::Binary(kind) = func.dfg.inst(inst).kind() else {
        return None;
    };
    let [lhs, rhs] = func.dfg.inst(inst).collect_values()[..] else {
        return None;
    };
    Some((kind, lhs, rhs))
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
pub(crate) fn dominates(func: &Function, dom: &DomTree, inst: InstId, user: InstId) -> bool {
    let block = func.layout.inst_block(inst);
    if func.layout.inst_block(user) != block {
        return dom.dominates(block, func.layout.inst_block(user));
    }
    iter::successors(func.layout.next_inst_of(inst), |&next| {
        func.layout.next_inst_of(next)
    })
    .any(|next| next == user)
}

#[cfg(test)]
mod tests {
    use crate::{
        optim::pipeline::{Pass, run_function_pass_round},
        test_support::{dump_func_by_name, parse_test_module},
    };

    #[test]
    fn tail_switch_destinations_count_as_one_block() {
        // The guarded difference is an argument of each of the switch's
        // four tail calls.
        let fuses = |linkage: &str| {
            let module = parse_test_module(&format!(
                r#"
target = "x86_64-unknown-native"

func {linkage} %dispatch(v0.i64, v1.i64, v2.i64) -> i64 {{
    block0:
        v3.i1 = lt v1 v2;
        br v3 block1 block2;
    block1:
        return v1;
    block2:
        v4.i64 = sub v1 v2;
        v5.i64 = and v0 3.i64;
        br_table v5 block6 (0.i64 block3) (1.i64 block4) (2.i64 block5);
    block3:
        v6.i64 = call %op v0 v4 v2;
        return v6;
    block4:
        v7.i64 = call %op v0 v4 v2;
        return v7;
    block5:
        v8.i64 = call %op v0 v4 v2;
        return v8;
    block6:
        v9.i64 = call %op v0 v4 v2;
        return v9;
}}

func private %op(v0.i64, v1.i64, v2.i64) -> i64 {{
    block0:
        v3.i64 = add v0 1.i64;
        v4.i64 = call %dispatch v3 v1 v2;
        return v4;
}}
"#
            ));
            run_function_pass_round(&module, &[Pass::CompareSubFusion], &mut true, None);
            dump_func_by_name(&module, "dispatch").contains("usubo")
        };
        // A private dispatch tail-calls through one table, where the
        // difference is used once.
        assert!(!fuses("private"));
        // A public one makes four calls.
        assert!(fuses("public"));
    }

    #[test]
    fn overflow_tests_become_the_carry_of_their_addition() {
        // `checked_add`: `b > MAX - a` guards `a + b`, which a `uaddo` checks
        // again; `not a < b` is the same test.
        let module = parse_test_module(
            r#"
target = "x86_64-unknown-native"

func public %checked_add(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = sub -1.i256 v0;
        v3.i1 = gt v1 v2;
        br v3 block1 block2;
    block1:
        return 0.i256;
    block2:
        (v4.i256, v5.i1) = uaddo v1 v0;
        br v5 block1 block3;
    block3:
        v6.i256 = add v0 v1;
        v7.i256 = mul v4 v6;
        return v7;
}

func public %not_less(v0.i64, v1.i64) -> i1 {
    block0:
        v2.i64 = not v0;
        v3.i1 = lt v2 v1;
        return v3;
}

func public %no_overflow(v0.i64, v1.i64) -> i1 {
    block0:
        v2.i64 = sub -1.i64 v0;
        v3.i1 = lt v1 v2;
        return v3;
}
"#,
        );
        run_function_pass_round(&module, &[Pass::CompareSubFusion], &mut true, None);
        let checked_add = dump_func_by_name(&module, "checked_add");
        assert_eq!(checked_add.matches("uaddo").count(), 1, "{checked_add}");
        let (sum, carry) = checked_add
            .lines()
            .find_map(|line| {
                let results = line.trim().strip_suffix(" = uaddo v0 v1;")?;
                let (sum, carry) = results
                    .strip_prefix('(')?
                    .strip_suffix(".i1)")?
                    .split_once(", ")?;
                Some((sum.strip_suffix(".i256")?.to_string(), carry.to_string()))
            })
            .unwrap_or_else(|| panic!("{checked_add}"));
        assert!(
            checked_add.contains(&format!("br {carry} block1 block2;"))
                && checked_add.contains(&format!("br {carry} block1 block3;"))
                && checked_add.contains(&format!("mul {sum} {sum};"))
                && !checked_add.contains(" gt ")
                && !checked_add.contains(" add "),
            "{checked_add}"
        );
        let not_less = dump_func_by_name(&module, "not_less");
        assert!(
            not_less.contains("uaddo v0 v1") && !not_less.contains(" lt "),
            "{not_less}"
        );
        // `a < MAX - b` is no carry test.
        let no_overflow = dump_func_by_name(&module, "no_overflow");
        assert!(!no_overflow.contains("uaddo"), "{no_overflow}");
    }
}
