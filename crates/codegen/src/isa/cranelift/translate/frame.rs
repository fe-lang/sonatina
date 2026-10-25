use std::{
    cmp::Reverse,
    collections::{BTreeSet, BinaryHeap},
};

use cranelift_codegen::ir::{self as clif, InstBuilder, StackSlotData, StackSlotKind};
use cranelift_entity::SecondaryMap;
use cranelift_frontend::FunctionBuilder;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, ValueId,
    inst::{InstId, inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
};

use super::{
    INLINE_MEMORY_BYTES, uses_indirect_value_representation, value_storage_alignment,
    value_storage_size,
};

/// Stack slots for indirectly represented SSA values.
///
/// A value-producing instruction with an aggregate or `i256` result writes
/// a snapshot that nothing mutates afterwards. Phis, loads, call results
/// and the heads of `insert_value` chains own storage. An `insert_value`
/// that is the sole consumer of an earlier insert in its block continues
/// that storage, and an extracted aggregate is a view into its base's. A
/// storage class is these values together, and it is live wherever one of
/// them is.
///
/// Classes share a slot when their live ranges are disjoint. A class's
/// range covers its definition, every use, and every block on a path from
/// the definition to a use; a phi is defined by the copies at the end of
/// each predecessor. An instruction reads its operands while it writes its
/// result, so the two always overlap. Ranges are intervals over the
/// translation's block order, so two classes live at a common point never
/// share a slot.
///
/// A load whose only use copies it, later in its block with no state
/// change in between, owns no storage: the consumer copies straight from
/// the load's source. A store may overlap that source, so it consumes only
/// a load small enough to copy inline, reading every word before writing.
///
/// A returned class can live in the function's return buffer instead, so
/// that its `return` copies nothing. The buffer is caller storage distinct
/// from every argument, and holds classes with disjoint ranges. A `return`
/// of another value still copies into it, which is safe because no value is
/// live after a `return`.
pub(super) struct FrameSlots {
    slot_of: FxHashMap<ValueId, clif::StackSlot>,
    return_buffer: Option<clif::Value>,
    /// Values stored in the return buffer: returned classes' roots and their
    /// `insert_value` continuations.
    in_return_buffer: FxHashSet<ValueId>,
    /// The `insert_value` continuing each continued source's storage.
    continuation: FxHashMap<ValueId, InstId>,
    forwarded: FxHashSet<ValueId>,
}

impl FrameSlots {
    pub fn new(
        function: &Function,
        cfg: &ControlFlowGraph,
        block_order: &[BlockId],
        return_buffer: Option<clif::Value>,
        builder: &mut FunctionBuilder,
    ) -> Result<Self, String> {
        let plan = Plan::new(function, cfg, block_order)?;
        let mut in_buffer = vec![false; plan.classes.len()];
        if return_buffer.is_some() {
            // Keep the most returned classes that are never live together.
            let mut returned: Vec<_> = (0..plan.classes.len())
                .filter(|&class| plan.classes[class].returned)
                .collect();
            returned.sort_by_key(|&class| plan.classes[class].end);
            let mut last_end = None;
            for class in returned {
                if last_end.is_none_or(|end| plan.classes[class].start > end) {
                    in_buffer[class] = true;
                    last_end = Some(plan.classes[class].end);
                }
            }
        }

        let mut slots: Vec<(u32, u64)> = Vec::new();
        let mut slot_of_class = vec![None; plan.classes.len()];
        let mut free: BTreeSet<(u32, usize)> = BTreeSet::new();
        let mut active: BinaryHeap<Reverse<(u32, usize)>> = BinaryHeap::new();
        let mut order: Vec<_> = (0..plan.classes.len())
            .filter(|&class| !in_buffer[class])
            .collect();
        order.sort_by_key(|&class| plan.classes[class].start);
        for class in order {
            let Class {
                start,
                end,
                size,
                align,
                ..
            } = plan.classes[class];
            while let Some(&Reverse((last, slot))) = active.peek()
                && last < start
            {
                active.pop();
                free.insert((slots[slot].0, slot));
            }
            // Take the smallest free slot that fits, else grow the largest.
            let fit = free
                .range((size, 0)..)
                .next()
                .or_else(|| free.iter().next_back())
                .copied();
            let slot = match fit {
                Some(entry) => {
                    free.remove(&entry);
                    entry.1
                }
                None => {
                    slots.push((0, 1));
                    slots.len() - 1
                }
            };
            slots[slot] = (slots[slot].0.max(size), slots[slot].1.max(align));
            slot_of_class[class] = Some(slot);
            active.push(Reverse((end, slot)));
        }

        let slots: Vec<_> = slots
            .into_iter()
            .map(|(size, align)| {
                builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size.max(1),
                    align.trailing_zeros() as u8,
                ))
            })
            .collect();
        let dfg = &function.dfg;
        Ok(Self {
            slot_of: plan
                .roots
                .iter()
                .filter_map(|&(root, class)| Some((root, slots[slot_of_class[class]?])))
                .collect(),
            return_buffer,
            in_return_buffer: plan
                .members
                .iter()
                .zip(in_buffer)
                .filter(|&(_, in_buffer)| in_buffer)
                .flat_map(|(members, _)| {
                    let root_ty = dfg.value_ty(members[0]);
                    members
                        .iter()
                        .copied()
                        .filter(move |&member| dfg.value_ty(member) == root_ty)
                })
                .collect(),
            continuation: plan.continuation,
            forwarded: plan.forwarded,
        })
    }

    /// Whether a load leaves its result in memory for its consumer.
    pub fn forwards(&self, load: ValueId) -> bool {
        self.forwarded.contains(&load)
    }

    /// The address of the storage of a value that owns storage.
    pub fn address(
        &self,
        value: ValueId,
        builder: &mut FunctionBuilder,
    ) -> Result<clif::Value, String> {
        if self.in_return_buffer.contains(&value) {
            return self
                .return_buffer
                .ok_or_else(|| "return buffer without an indirect return".to_string());
        }
        let slot = self
            .slot_of
            .get(&value)
            .ok_or_else(|| format!("v{} has no frame slot", value.0))?;
        Ok(builder.ins().stack_addr(clif::types::I64, *slot, 0))
    }

    /// Whether `value` is already in the return buffer, so that returning
    /// it copies nothing.
    pub fn in_return_buffer(&self, value: ValueId) -> bool {
        self.in_return_buffer.contains(&value)
    }

    /// Whether the `insert_value` `inst` writes into the storage of its
    /// source `source`.
    pub fn continues_source(&self, inst: InstId, source: ValueId) -> bool {
        self.continuation.get(&source) == Some(&inst)
    }

    /// The `insert_value` chain head `head` and the inserts continuing its
    /// storage, in order.
    pub fn insert_chain<'a>(
        &'a self,
        function: &'a Function,
        head: InstId,
    ) -> impl Iterator<Item = InstId> + 'a {
        std::iter::successors(Some(head), move |&inst| {
            self.continuation
                .get(&function.dfg.inst_result(inst)?)
                .copied()
        })
    }
}

#[derive(Clone, Copy)]
struct Class {
    def_block: BlockId,
    /// The range starts at the defining instruction, or at the start of a
    /// phi's block, and grows to cover the class's live points.
    start: u32,
    end: u32,
    size: u32,
    align: u64,
    /// Whether a `return` returns the root or one of its continuations.
    returned: bool,
}

impl Class {
    fn cover(&mut self, position: u32) {
        self.start = self.start.min(position);
        self.end = self.end.max(position);
    }
}

struct Plan {
    classes: Vec<Class>,
    /// The values of each class, its root first.
    members: Vec<Vec<ValueId>>,
    /// Values that own storage, by class.
    roots: Vec<(ValueId, usize)>,
    continuation: FxHashMap<ValueId, InstId>,
    forwarded: FxHashSet<ValueId>,
}

impl Plan {
    fn new(
        function: &Function,
        cfg: &ControlFlowGraph,
        block_order: &[BlockId],
    ) -> Result<Self, String> {
        let dfg = &function.dfg;
        let ctx = function.ctx();
        let mut position = SecondaryMap::<InstId, u32>::new();
        let mut bounds = SecondaryMap::<BlockId, Option<(u32, u32)>>::new();
        let mut next = 0;
        for &block in block_order {
            let start = next;
            for inst in function.layout.iter_inst(block) {
                position[inst] = next;
                next += 1;
            }
            bounds[block] = Some((start, next.saturating_sub(1).max(start)));
        }

        let mut plan = Self {
            classes: Vec::new(),
            members: Vec::new(),
            roots: Vec::new(),
            continuation: FxHashMap::default(),
            forwarded: FxHashSet::default(),
        };
        let mut class_of = FxHashMap::<ValueId, usize>::default();
        for &block in block_order {
            let (block_start, _) = bounds[block].unwrap();
            for inst in function.layout.iter_inst(block) {
                let [result] = *dfg.inst_results(inst) else {
                    continue;
                };
                let ty = dfg.value_ty(result);
                if !uses_indirect_value_representation(ctx, ty) {
                    continue;
                }
                let class = match native_inst_set().resolve_inst(dfg.inst(inst)) {
                    NativeInstKind::Phi(_) => Some(block_start),
                    NativeInstKind::Mload(_) | NativeInstKind::ObjLoad(_)
                        if copied_once(function, inst, result)? =>
                    {
                        plan.forwarded.insert(result);
                        None
                    }
                    NativeInstKind::Mload(_)
                    | NativeInstKind::ObjLoad(_)
                    | NativeInstKind::Call(_) => Some(position[inst]),
                    NativeInstKind::InsertValue(insert) => {
                        let source = *insert.dest();
                        let continues = dfg.value_inst(source).is_some_and(|source_inst| {
                            function.layout.inst_block(source_inst) == block
                                && dfg.users(source).copied().eq([inst])
                                && matches!(
                                    native_inst_set().resolve_inst(dfg.inst(source_inst)),
                                    NativeInstKind::InsertValue(_)
                                )
                        });
                        if continues {
                            plan.continuation.insert(source, inst);
                            let class = class_of[&source];
                            class_of.insert(result, class);
                            plan.members[class].push(result);
                            None
                        } else {
                            Some(position[inst])
                        }
                    }
                    NativeInstKind::ExtractValue(extract) => {
                        if let Some(&class) = class_of.get(extract.dest()) {
                            class_of.insert(result, class);
                            plan.members[class].push(result);
                        }
                        None
                    }
                    _ => None,
                };
                if let Some(def) = class {
                    let index = plan.classes.len();
                    plan.classes.push(Class {
                        def_block: block,
                        start: def,
                        end: def,
                        size: value_storage_size(ty, ctx)?,
                        align: value_storage_alignment(ty, ctx)?,
                        returned: false,
                    });
                    plan.roots.push((result, index));
                    class_of.insert(result, index);
                    plan.members.push(vec![result]);
                }
            }
        }

        let mut ranges = Ranges {
            bounds,
            visited: SecondaryMap::new(),
            stamp: 0,
            pending: Vec::new(),
        };
        for (class, members) in plan.classes.iter_mut().zip(&plan.members) {
            let root_ty = dfg.value_ty(members[0]);
            ranges.stamp += 1;
            // A phi is written by the copies at the end of its predecessors.
            if let Some(phi) = dfg
                .value_inst(members[0])
                .and_then(|inst| dfg.cast_phi(inst))
            {
                for &(_, pred) in phi.args() {
                    if let Some((_, end)) = ranges.bounds[pred] {
                        class.cover(end);
                    }
                }
            }
            for &value in members {
                for &user in dfg.users(value) {
                    if let Some(phi) = dfg.cast_phi(user) {
                        for (_, pred) in phi.args().iter().filter(|(input, _)| *input == value) {
                            ranges.live_out(class, *pred);
                        }
                    } else {
                        class.returned |= dfg.value_ty(value) == root_ty
                            && matches!(
                                native_inst_set().resolve_inst(dfg.inst(user)),
                                NativeInstKind::Return(_)
                            );
                        let block = function.layout.inst_block(user);
                        if let Some((start, _)) = ranges.bounds[block] {
                            class.cover(position[user]);
                            if block != class.def_block {
                                class.cover(start);
                                for &pred in cfg.preds_of(block) {
                                    ranges.live_out(class, pred);
                                }
                            }
                        }
                    }
                    while let Some(block) = ranges.pending.pop() {
                        for &pred in cfg.preds_of(block) {
                            ranges.live_out(class, pred);
                        }
                    }
                }
            }
        }
        Ok(plan)
    }
}

/// Whether the only use of the load `inst` copies its result later in the
/// same block, with no instruction in between that may change state.
fn copied_once(function: &Function, inst: InstId, result: ValueId) -> Result<bool, String> {
    let dfg = &function.dfg;
    let mut users = dfg.users(result);
    let (Some(&user), None) = (users.next(), users.next()) else {
        return Ok(false);
    };
    let inline = value_storage_size(dfg.value_ty(result), function.ctx())? <= INLINE_MEMORY_BYTES;
    let copies = match native_inst_set().resolve_inst(dfg.inst(user)) {
        // A chain head copies its source, and every insert copies its field.
        NativeInstKind::InsertValue(_) => true,
        NativeInstKind::Mstore(store) => *store.addr() != result && inline,
        NativeInstKind::ObjStore(store) => *store.object() != result && inline,
        NativeInstKind::Return(_) => true,
        _ => false,
    };
    Ok(copies
        && function.layout.inst_block(user) == function.layout.inst_block(inst)
        && std::iter::successors(function.layout.next_inst_of(inst), |&next| {
            function.layout.next_inst_of(next)
        })
        .take_while(|&next| next != user)
        .all(|next| !dfg.may_mutate_state(next)))
}

/// Live range construction over the translation's block order.
struct Ranges {
    /// The first and last position of each translated block.
    bounds: SecondaryMap<BlockId, Option<(u32, u32)>>,
    visited: SecondaryMap<BlockId, u32>,
    /// Identifies the class whose range `visited` describes.
    stamp: u32,
    /// Blocks the class is live into, whose predecessors it is live out of.
    pending: Vec<BlockId>,
}

impl Ranges {
    /// Extends `class` to the end of `block`. Unless `block` defines the
    /// class, the class is live through it from its predecessors.
    fn live_out(&mut self, class: &mut Class, block: BlockId) {
        let Some((start, end)) = self.bounds[block] else {
            return;
        };
        class.cover(end);
        if block != class.def_block && self.visited[block] != self.stamp {
            self.visited[block] = self.stamp;
            class.cover(start);
            self.pending.push(block);
        }
    }
}

#[cfg(test)]
mod tests {
    use cranelift_codegen::ir as clif;
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
    use sonatina_ir::ControlFlowGraph;

    use super::FrameSlots;

    /// The sizes of the slots planned for function `%f`.
    fn slot_sizes(body: &str) -> Vec<u32> {
        let source = format!("target = \"x86_64-unknown-native\"\n{body}");
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let func = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .unwrap();
        module.func_store.view(func, |function| {
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(function);
            let mut block_order: Vec<_> = cfg.post_order().collect();
            block_order.reverse();
            let mut clif_function = clif::Function::new();
            let mut context = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut clif_function, &mut context);
            FrameSlots::new(function, &cfg, &block_order, None, &mut builder).unwrap();
            clif_function
                .sized_stack_slots
                .values()
                .map(|slot| slot.size)
                .collect()
        })
    }

    #[test]
    fn sequential_temporaries_share_a_slot() {
        let sizes = slot_sizes(
            r#"
func public %f(v0.*[i64; 64], v1.*[i64; 64]) {
block0:
    v2.[i64; 64] = mload v0 [i64; 64];
    mstore v1 v2 [i64; 64];
    v3.[i64; 64] = mload v1 [i64; 64];
    mstore v0 v3 [i64; 64];
    v4.[i64; 32] = mload v0 [i64; 32];
    mstore v1 v4 [i64; 32];
    return;
}
"#,
        );
        assert_eq!(sizes, [512]);
    }

    #[test]
    fn overlapping_values_and_views_keep_separate_slots() {
        // `v3` is a view into `v2`, so `v2` stays live until `v3`'s store.
        let sizes = slot_sizes(
            r#"
func public %f(v0.*[[i64; 32]; 2], v1.*[i64; 32]) {
block0:
    v2.[[i64; 32]; 2] = mload v0 [[i64; 32]; 2];
    v3.[i64; 32] = extract_value v2 1.i64;
    v4.[i64; 32] = mload v1 [i64; 32];
    mstore v0 v4 [i64; 32];
    mstore v1 v3 [i64; 32];
    return;
}
"#,
        );
        assert_eq!(sizes, [512, 256]);
    }

    #[test]
    fn instructions_read_operands_while_writing_results() {
        // An insert chain head copies its source, and a call result is
        // written while the callee reads its argument.
        let sizes = slot_sizes(
            r#"
declare external %g([i64; 32]) -> [i64; 32];
func public %f(v0.*[i64; 32]) {
block0:
    v1.[i64; 32] = mload v0 [i64; 32];
    v2.[i64; 32] = insert_value v1 0.i64 7.i64;
    v3.[i64; 32] = insert_value v2 1.i64 8.i64;
    v4.[i64; 32] = call %g v3;
    mstore v0 v4 [i64; 32];
    return;
}
"#,
        );
        assert_eq!(sizes, [256, 256]);
    }

    #[test]
    fn loop_ranges_cover_the_whole_loop() {
        // `v2` lives across the loop and the phi `v5` across its backedge
        // copy from `v6`, so neither shares a slot with the loop's values.
        // The phi's inputs `v3` and `v6` are dead after their edges' copies.
        let sizes = slot_sizes(
            r#"
func public %f(v0.*[i64; 32], v1.i1) {
block0:
    v2.[i64; 32] = mload v0 [i64; 32];
    v3.[i64; 16] = mload v0 [i64; 16];
    jump block1;
block1:
    v5.[i64; 16] = phi (v3 block0) (v6 block1);
    v6.[i64; 16] = mload v0 [i64; 16];
    mstore v0 v5 [i64; 16];
    br v1 block1 block2;
block2:
    mstore v0 v2 [i64; 32];
    return;
}
"#,
        );
        assert_eq!(sizes, [256, 128, 128]);
    }
}
