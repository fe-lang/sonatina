//! Switch formation: a tree of branches that each compare one integer with a
//! constant becomes one `br_table` on that integer.
//!
//! The region starts at a block that branches on a comparison of `v` with a
//! constant and grows through successors that do nothing but branch on
//! another such comparison of `v`, as long as they are entered only from the
//! region. Each value of `v` takes exactly one path through the region, so
//! every edge out of the region carries a set of values. Edges into a block
//! that bring its phis the same inputs make one target; the target reached
//! by the most values becomes the table's default, and every value of the
//! others becomes a key. A block with several targets is entered from the
//! table directly by one and through a jump block by each other.
//!
//! A range test expands into a key per value, so a region whose keys
//! outnumber its comparisons by more than [`MAX_KEYS_PER_TEST`] stays as it
//! is. Native backends lower a `br_table` to jump tables and a search over
//! them; the EVM backend has its own switch lowering, so this pass belongs in
//! native pipelines.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, I256, Immediate, InstId, Type, U256, ValueId,
    inst::{
        BinaryInstKind, InstClassKind, UnaryInstKind,
        control_flow::{Br, BrTable},
    },
};

use super::branch_canonicalize::{compare_value, remove_dead_single_result_inst};
use crate::cfg_edit::{CfgEditor, CleanupMode, iter_phis_in_block};

/// The fewest comparisons worth a table.
const MIN_TESTS: usize = 3;
/// The most keys per replaced comparison.
const MAX_KEYS_PER_TEST: u128 = 8;
/// The most keys in one table.
const MAX_KEYS: u128 = 1024;

#[derive(Default)]
pub struct SwitchFormation;

impl SwitchFormation {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        let mut blocks: Vec<_> = editor.cfg().post_order().collect();
        blocks.reverse();
        let mut changed = false;
        for block in blocks {
            changed |=
                editor.func().layout.is_block_inserted(block) && form_switch(&mut editor, block);
        }
        changed
    }
}

/// A branch on a comparison of an integer `value` of `bits` bits with a
/// constant.
struct Test {
    value: ValueId,
    bits: u32,
    /// The values for which the branch goes to `nz`.
    taken: Values,
    nz: BlockId,
    z: BlockId,
    cond_inst: InstId,
}

fn test_of(func: &Function, block: BlockId) -> Option<Test> {
    let term = func.layout.last_inst_of(block)?;
    let br = func.dfg.downcast::<&Br>(term)?;
    let (nz, z) = (*br.nz_dest(), *br.z_dest());
    let cond_inst = func.dfg.value_inst(*br.cond())?;
    let (kind, value, constant) = match func.dfg.inst(cond_inst).kind() {
        InstClassKind::Unary(UnaryInstKind::IsZero) => (
            BinaryInstKind::Eq,
            func.dfg.inst(cond_inst).collect_values()[0],
            0,
        ),
        _ => {
            let (_, kind, lhs, rhs) = compare_value(func, *br.cond())?;
            // `k < v` is `v > k`.
            match (func.dfg.value_imm(lhs), func.dfg.value_imm(rhs)) {
                (None, Some(k)) => (kind, lhs, k.as_i256().to_u256().low_u64()),
                (Some(k), None) => (mirror(kind), rhs, k.as_i256().to_u256().low_u64()),
                _ => return None,
            }
        }
    };
    let bits = match func.dfg.value_ty(value) {
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        _ => return None,
    };
    Some(Test {
        value,
        bits,
        taken: compare_set(kind, constant, bits),
        nz,
        z,
        cond_inst,
    })
}

/// Whether `block` does nothing but `test`: no phis, and no instruction but
/// its condition, which only the branch uses.
fn is_bare(func: &Function, block: BlockId, test: &Test) -> bool {
    let term = func.layout.last_inst_of(block).expect("terminated block");
    let cond_in_block = func.layout.inst_block(test.cond_inst) == block;
    func.layout
        .iter_inst(block)
        .all(|inst| inst == term || (cond_in_block && inst == test.cond_inst))
        && (!cond_in_block
            || func
                .dfg
                .inst_result(test.cond_inst)
                .is_some_and(|cond| func.dfg.users_num(cond) == 1))
}

fn form_switch(editor: &mut CfgEditor<'_>, root: BlockId) -> bool {
    let func = editor.func();
    let Some(root_test) = test_of(func, root) else {
        return false;
    };
    let (value, bits) = (root_test.value, root_test.bits);

    // Grow through bare tests of `value`, then keep those entered only from
    // the region.
    let mut region: FxHashMap<BlockId, Test> = FxHashMap::default();
    let mut pending = vec![root_test.nz, root_test.z];
    while let Some(block) = pending.pop() {
        if block == root || region.contains_key(&block) {
            continue;
        }
        if let Some(test) = test_of(func, block)
            && test.value == value
            && is_bare(func, block, &test)
        {
            pending.extend([test.nz, test.z]);
            region.insert(block, test);
        }
    }
    loop {
        let entered_outside: Vec<_> = region
            .keys()
            .filter(|&&block| {
                editor
                    .cfg()
                    .preds_of(block)
                    .any(|pred| *pred != root && !region.contains_key(pred))
            })
            .copied()
            .collect();
        if entered_outside.is_empty() {
            break;
        }
        for block in entered_outside {
            region.remove(&block);
        }
    }
    let tests = region.len() + 1;
    if tests < MIN_TESTS {
        return false;
    }

    // Order the region so each block follows all of its predecessors.
    let succs = |block: BlockId| {
        let test = region.get(&block).unwrap_or(&root_test);
        [test.nz, test.z]
    };
    let mut post_order = Vec::with_capacity(tests);
    let mut visiting = FxHashSet::default();
    let mut done = FxHashSet::default();
    let mut stack = vec![(root, false)];
    while let Some((block, finished)) = stack.pop() {
        if finished {
            done.insert(block);
            post_order.push(block);
            continue;
        }
        if done.contains(&block) {
            continue;
        }
        if !visiting.insert(block) {
            return false;
        }
        stack.push((block, true));
        for succ in succs(block) {
            if succ == root {
                return false;
            }
            if region.contains_key(&succ) {
                stack.push((succ, false));
            }
        }
    }

    // The values that reach each region block, and those each edge out of
    // the region carries.
    let max = u64::MAX >> (64 - bits);
    let mut reach = FxHashMap::default();
    reach.insert(root, Values::range(0, max));
    let mut exits: Vec<(BlockId, BlockId, Values)> = Vec::new();
    for &block in post_order.iter().rev() {
        let test = region.get(&block).unwrap_or(&root_test);
        let values = reach.remove(&block).expect("region block is reached");
        let taken = values.intersect(&test.taken);
        let not_taken = values.intersect(&test.taken.complement(max));
        for (dest, values) in [(test.nz, taken), (test.z, not_taken)] {
            if region.contains_key(&dest) {
                let entry = reach.entry(dest).or_default();
                *entry = entry.union(&values);
            } else if let Some((_, _, exit)) = exits
                .iter_mut()
                .find(|(from, to, _)| *from == block && *to == dest)
            {
                *exit = exit.union(&values);
            } else {
                exits.push((block, dest, values));
            }
        }
    }

    // A target is a destination with the phi inputs an exit brings it;
    // exits that bring the same inputs share one.
    let mut targets: Vec<(BlockId, Vec<ValueId>, Values)> = Vec::new();
    for (from, dest, values) in exits {
        let inputs: Vec<_> = iter_phis_in_block(func, dest)
            .map(|phi_inst| {
                let phi = func.dfg.cast_phi(phi_inst).expect("phi");
                phi.args()
                    .iter()
                    .find(|(_, pred)| *pred == from)
                    .expect("a phi has an input from each predecessor")
                    .0
            })
            .collect();
        if let Some((_, _, target)) = targets
            .iter_mut()
            .find(|(to, target_inputs, _)| *to == dest && *target_inputs == inputs)
        {
            *target = target.union(&values);
        } else {
            targets.push((dest, inputs, values));
        }
    }
    let default = targets
        .iter()
        .enumerate()
        .max_by_key(|(idx, (_, _, values))| (values.len(), std::cmp::Reverse(*idx)))
        .map(|(idx, _)| idx)
        .expect("a region leaves to some block");
    let keys: u128 = targets
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != default)
        .map(|(_, (_, _, values))| values.len())
        .sum();
    if keys > MAX_KEYS || keys > MAX_KEYS_PER_TEST * tests as u128 {
        return false;
    }

    let ty = func.dfg.value_ty(value);
    let conds: Vec<_> = region
        .values()
        .chain([&root_test])
        .map(|test| test.cond_inst)
        .collect();
    let in_region = |block: BlockId| block == root || region.contains_key(&block);
    let dests: FxHashSet<_> = targets.iter().map(|(dest, _, _)| *dest).collect();
    for dest in dests {
        let phis: Vec<_> = iter_phis_in_block(editor.func(), dest).collect();
        for phi_inst in phis {
            editor
                .func_mut()
                .dfg
                .edit_phi(phi_inst, |phi| phi.retain(|pred| !in_region(pred)));
        }
    }

    // The first target of a destination is entered from the root, and each
    // other one through a jump block of its own.
    let mut entered = FxHashSet::default();
    let mut blocks = Vec::with_capacity(targets.len());
    for (idx, (dest, inputs, values)) in targets.iter().enumerate() {
        if idx != default && values.is_empty() {
            blocks.push(None);
            continue;
        }
        let pred = if entered.insert(*dest) {
            root
        } else {
            editor.insert_edge_block(*dest)
        };
        let phis: Vec<_> = iter_phis_in_block(editor.func(), *dest).collect();
        for (phi_inst, &input) in phis.into_iter().zip(inputs) {
            editor
                .func_mut()
                .dfg
                .edit_phi(phi_inst, |phi| phi.append_phi_arg(input, pred));
        }
        blocks.push(Some(if pred == root { *dest } else { pred }));
    }

    let mut cases: Vec<_> = targets
        .iter()
        .zip(&blocks)
        .enumerate()
        .filter(|(idx, _)| *idx != default)
        .flat_map(|(_, ((_, _, values), block))| {
            block
                .map(|block| values.iter().map(move |key| (key, block)))
                .into_iter()
                .flatten()
        })
        .collect();
    cases.sort_unstable_by_key(|(key, _)| *key);
    let func = editor.func_mut();
    let table = cases
        .into_iter()
        .map(|(key, block)| {
            let key = Immediate::from_i256(I256::from_u256(U256::from(key)), ty);
            (func.dfg.make_imm_value(key), block)
        })
        .collect();
    let term = func.layout.last_inst_of(root).expect("terminated block");
    let br_table = BrTable::new_unchecked(func.inst_set(), value, blocks[default], table);
    func.dfg.replace_inst(term, Box::new(br_table));

    // The region's other blocks are now unreachable, and so may be a leaf
    // whose values the region never sends it.
    editor.recompute_cfg();
    let reachable = editor.cfg().reachable_blocks();
    let unreachable: Vec<_> = editor
        .func()
        .layout
        .iter_block()
        .filter(|block| !reachable[*block])
        .collect();
    editor.delete_blocks_unreachable(&unreachable);
    let func = editor.func_mut();
    for cond in conds {
        remove_dead_single_result_inst(func, cond);
    }
    editor.recompute_cfg();
    true
}

/// `k kind v` as `v kind' k`.
fn mirror(kind: BinaryInstKind) -> BinaryInstKind {
    match kind {
        BinaryInstKind::Lt => BinaryInstKind::Gt,
        BinaryInstKind::Gt => BinaryInstKind::Lt,
        BinaryInstKind::Le => BinaryInstKind::Ge,
        BinaryInstKind::Ge => BinaryInstKind::Le,
        BinaryInstKind::Slt => BinaryInstKind::Sgt,
        BinaryInstKind::Sgt => BinaryInstKind::Slt,
        BinaryInstKind::Sle => BinaryInstKind::Sge,
        BinaryInstKind::Sge => BinaryInstKind::Sle,
        kind => kind,
    }
}

/// The bit patterns `v` of `bits` bits for which `v kind k` holds.
fn compare_set(kind: BinaryInstKind, k: u64, bits: u32) -> Values {
    let max = u64::MAX >> (64 - bits);
    let k = k & max;
    let unsigned = |kind, k: u64| match kind {
        BinaryInstKind::Lt => k
            .checked_sub(1)
            .map_or_else(Values::default, |hi| Values::range(0, hi)),
        BinaryInstKind::Le => Values::range(0, k),
        BinaryInstKind::Gt if k == max => Values::default(),
        BinaryInstKind::Gt => Values::range(k + 1, max),
        BinaryInstKind::Ge => Values::range(k, max),
        _ => unreachable!("not an ordering"),
    };
    // A signed order is the unsigned order of patterns with the sign bit
    // flipped.
    let sign = 1u64 << (bits - 1);
    let signed = |kind| {
        let flipped = unsigned(kind, k ^ sign);
        Values::from_ranges(
            flipped
                .0
                .into_iter()
                .flat_map(|(lo, hi)| {
                    if hi < sign {
                        vec![(lo + sign, hi + sign)]
                    } else if lo >= sign {
                        vec![(lo - sign, hi - sign)]
                    } else {
                        vec![(lo + sign, max), (0, hi - sign)]
                    }
                })
                .collect(),
        )
    };
    match kind {
        BinaryInstKind::Eq => Values::range(k, k),
        BinaryInstKind::Ne => Values::range(k, k).complement(max),
        BinaryInstKind::Lt | BinaryInstKind::Le | BinaryInstKind::Gt | BinaryInstKind::Ge => {
            unsigned(kind, k)
        }
        BinaryInstKind::Slt => signed(BinaryInstKind::Lt),
        BinaryInstKind::Sle => signed(BinaryInstKind::Le),
        BinaryInstKind::Sgt => signed(BinaryInstKind::Gt),
        BinaryInstKind::Sge => signed(BinaryInstKind::Ge),
        _ => unreachable!("not a comparison"),
    }
}

/// A set of bit patterns as sorted, disjoint, non-adjacent inclusive ranges.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Values(Vec<(u64, u64)>);

impl Values {
    fn range(lo: u64, hi: u64) -> Self {
        Self::from_ranges(vec![(lo, hi)])
    }

    fn from_ranges(mut ranges: Vec<(u64, u64)>) -> Self {
        ranges.retain(|(lo, hi)| lo <= hi);
        ranges.sort_unstable();
        let mut merged: Vec<(u64, u64)> = Vec::with_capacity(ranges.len());
        for (lo, hi) in ranges {
            match merged.last_mut() {
                Some(last) if lo <= last.1.saturating_add(1) => last.1 = last.1.max(hi),
                _ => merged.push((lo, hi)),
            }
        }
        Self(merged)
    }

    fn union(&self, other: &Self) -> Self {
        Self::from_ranges(self.0.iter().chain(&other.0).copied().collect())
    }

    fn intersect(&self, other: &Self) -> Self {
        Self::from_ranges(
            self.0
                .iter()
                .flat_map(|&(a_lo, a_hi)| {
                    other
                        .0
                        .iter()
                        .map(move |&(b_lo, b_hi)| (a_lo.max(b_lo), a_hi.min(b_hi)))
                })
                .collect(),
        )
    }

    fn complement(&self, max: u64) -> Self {
        let mut ranges = Vec::new();
        let mut next = Some(0);
        for &(lo, hi) in &self.0 {
            if let Some(start) = next
                && lo > start
            {
                ranges.push((start, lo - 1));
            }
            next = (hi < max).then(|| hi + 1);
        }
        if let Some(start) = next {
            ranges.push((start, max));
        }
        Self(ranges)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> u128 {
        self.0.iter().map(|&(lo, hi)| u128::from(hi - lo) + 1).sum()
    }

    fn iter(&self) -> impl Iterator<Item = u64> + '_ {
        self.0.iter().flat_map(|&(lo, hi)| lo..=hi)
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::inst::BinaryInstKind;

    use super::{Values, compare_set};

    #[test]
    fn compare_sets_cover_unsigned_and_signed_orders() {
        for bits in [8, 16] {
            let max = u64::MAX >> (64 - bits);
            let sign = 1u64 << (bits - 1);
            let signed = |pattern: u64| {
                if pattern & sign == 0 {
                    pattern as i64
                } else {
                    pattern as i64 - (max as i64 + 1)
                }
            };
            let holds = |kind, v: u64, k: u64| match kind {
                BinaryInstKind::Eq => v == k,
                BinaryInstKind::Ne => v != k,
                BinaryInstKind::Lt => v < k,
                BinaryInstKind::Le => v <= k,
                BinaryInstKind::Gt => v > k,
                BinaryInstKind::Ge => v >= k,
                BinaryInstKind::Slt => signed(v) < signed(k),
                BinaryInstKind::Sle => signed(v) <= signed(k),
                BinaryInstKind::Sgt => signed(v) > signed(k),
                BinaryInstKind::Sge => signed(v) >= signed(k),
                _ => unreachable!(),
            };
            for k in [0, 1, 7, sign - 1, sign, sign + 1, max - 1, max] {
                for kind in [
                    BinaryInstKind::Eq,
                    BinaryInstKind::Ne,
                    BinaryInstKind::Lt,
                    BinaryInstKind::Le,
                    BinaryInstKind::Gt,
                    BinaryInstKind::Ge,
                    BinaryInstKind::Slt,
                    BinaryInstKind::Sle,
                    BinaryInstKind::Sgt,
                    BinaryInstKind::Sge,
                ] {
                    let set = compare_set(kind, k, bits);
                    let expected = Values::from_ranges(
                        (0..=max)
                            .filter(|&v| holds(kind, v, k))
                            .map(|v| (v, v))
                            .collect(),
                    );
                    assert_eq!(set, expected, "{kind:?} {k} at {bits} bits");
                    assert_eq!(
                        set.union(&set.complement(max)),
                        Values::range(0, max),
                        "{kind:?} {k}"
                    );
                    assert!(set.intersect(&set.complement(max)).is_empty());
                }
            }
        }
    }
}
