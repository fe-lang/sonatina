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
    inst::{InstId, control_flow::Call, inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
    module::FuncRef,
    types::CompoundType,
};

use super::{
    INLINE_MEMORY_BYTES, aggregate_elem_offset, constant_value_index, is_undef,
    uses_indirect_value_representation, value_storage_alignment, value_storage_size,
};

/// Stack slots for indirectly represented SSA values: aggregates. (i256
/// values are four limbs in Cranelift values, and small aggregates their
/// parts: see `register_parts`.)
///
/// A value-producing instruction with an aggregate result writes a
/// snapshot that nothing mutates afterwards. Phis, loads, call results,
/// `enum.make` and the heads of `insert_value` chains own storage. An
/// `insert_value` that is the sole consumer of an earlier insert in its
/// block continues that storage, and an aggregate extracted with
/// `extract_value` or `enum.extract` is a view into its base's. A
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
/// A class whose last value only fills a field of an `insert_value` chain
/// with an undef source lives in that chain's storage, at the field: the
/// insert copies nothing. Nothing reads the field before the insert, and the
/// chain's storage stays live while the class is. A phi does so only when it
/// is its block's one aggregate phi, so its edge copies need no ordering.
///
/// An `insert_value` chain with an undef source whose last value is only
/// stored into an object is built at the store's destination instead, when
/// nothing between the chain's start and the store touches memory and the
/// destination's address is defined before the chain starts.
///
/// A returned class can live in the function's return buffer instead, so
/// that its `return` copies nothing. The buffer is caller storage distinct
/// from every argument, and holds classes with disjoint ranges. A `return`
/// of another value still copies into it, which is safe because no value is
/// live after a `return`.
///
/// Objects (`obj.alloc`) have slots of their own. A local object whose
/// address does not escape is reached by a callee only through the call's
/// arguments, which lets values move between it and calls without copies;
/// so is a `noalias` object argument whose address does not escape, though
/// its storage stays the caller's. A local object initialized from a
/// by-reference argument in the entry block, before any other use, and not
/// written afterwards, lives in the argument's storage; so does one
/// initialized from a constant projection of such an argument, at the
/// field, unless the function owns the argument and may write its storage.
/// A load of a whole such object whose only use passes it to a call later
/// in its block, with no state change in between, owns no storage: the
/// call reads the object, which nothing else can change while it runs. A
/// call's indirect result whose only use stores it into such an object
/// later in its block, with no state change in between, is written there
/// by the callee, unless an argument reaches the object or an instruction in
/// between reads it. Any other load of such an object reads it in place
/// when no write of it can come between the load and a read of the loaded
/// value or of a view of it: no store into it, no call that may write
/// through one of its addresses (`ArgWrites`), and no call that may be given
/// its storage, as below, runs after the load and before or at such a read.
///
/// A callee may own a by-reference argument (`Ownership`), building an
/// object in its storage. The caller then passes storage it does not use
/// after the call and no other argument shares: a forwarded load of a local
/// object in its own slot that it no longer uses, or a value whose range
/// ends at the call. The call writes an object it is given, so a load of
/// the object read after the call does not read it in place.
/// Otherwise it copies the argument into a temporary, a class live only at
/// the call.
pub(super) struct FrameSlots {
    slot_of: FxHashMap<ValueId, clif::StackSlot>,
    return_buffer: Option<clif::Value>,
    /// Values stored in the return buffer: returned classes' roots and their
    /// `insert_value` continuations.
    in_return_buffer: FxHashSet<ValueId>,
    /// The `insert_value` continuing each continued source's storage.
    continuation: FxHashMap<ValueId, InstId>,
    forwarded: FxHashSet<ValueId>,
    /// The object each call writes its result into, and the stores that
    /// therefore copy nothing.
    destination: FxHashMap<InstId, ValueId>,
    stored_in_place: FxHashSet<InstId>,
    /// The temporary each owned argument a call cannot give away is copied
    /// into.
    temporary: FxHashMap<(InstId, usize), clif::StackSlot>,
    /// Objects living in the storage of the argument they are initialized
    /// from, with their offset there.
    aliased: FxHashMap<ValueId, (ValueId, u32)>,
    /// Roots of classes living in a field of another class's storage, with
    /// that class's root and the field's offset.
    embedded: FxHashMap<ValueId, (ValueId, u32)>,
    /// Inserts whose aggregate value is already in their field.
    in_place: FxHashSet<InstId>,
    /// Roots of classes built at the destination of the store of their last
    /// value, with that destination.
    stored_at: FxHashMap<ValueId, ValueId>,
}

impl FrameSlots {
    pub fn new(
        function: &Function,
        cfg: &ControlFlowGraph,
        block_order: &[BlockId],
        return_buffer: Option<clif::Value>,
        calls: &impl CallFacts,
        builder: &mut FunctionBuilder,
    ) -> Result<Self, String> {
        let plan = Plan::new(function, cfg, block_order, calls)?;
        let mut in_buffer = vec![false; plan.classes.len()];
        if return_buffer.is_some() {
            // Keep the most returned classes that are never live together.
            let mut returned: Vec<_> = (0..plan.classes.len())
                .filter(|&class| {
                    plan.classes[class].returned && !plan.embedded.contains_key(&class)
                })
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
            .filter(|&class| {
                !in_buffer[class]
                    && !plan.embedded.contains_key(&class)
                    && !plan.stored.contains_key(&class)
            })
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
            temporary: plan
                .temporaries
                .iter()
                .filter_map(|&(site, class)| Some((site, slots[slot_of_class[class]?])))
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
            stored_in_place: plan
                .destination
                .values()
                .map(|&(_, store)| store)
                .chain(plan.aliased.values().map(|&(_, _, store)| store))
                .chain(plan.stored.values().map(|&(_, store)| store))
                .collect(),
            aliased: plan
                .aliased
                .iter()
                .map(|(&object, &(arg, offset, _))| (object, (arg, offset)))
                .collect(),
            destination: plan
                .destination
                .into_iter()
                .map(|(call, (object, _))| (call, object))
                .collect(),
            embedded: plan
                .embedded
                .iter()
                .map(|(&child, &(parent, offset))| {
                    (plan.members[child][0], (plan.members[parent][0], offset))
                })
                .collect(),
            in_place: plan.in_place,
            stored_at: plan
                .stored
                .iter()
                .map(|(&class, &(object, _))| (plan.members[class][0], object))
                .collect(),
        })
    }

    /// The class root `value`'s storage lies in, with its offset there, if
    /// its class is embedded in another.
    pub fn embedded_in(&self, value: ValueId) -> Option<(ValueId, u32)> {
        self.embedded.get(&value).copied()
    }

    /// The object whose storage the class of root `value` is built in, if
    /// it is built at its store's destination.
    pub fn stored_at(&self, value: ValueId) -> Option<ValueId> {
        self.stored_at.get(&value).copied()
    }

    /// The object the call `inst` writes its indirect result into, if not
    /// the result's own storage.
    pub fn destination(&self, inst: InstId) -> Option<ValueId> {
        self.destination.get(&inst).copied()
    }

    /// The argument whose storage the object `object` lives in, if any,
    /// with the object's offset there.
    pub fn aliased(&self, object: ValueId) -> Option<(ValueId, u32)> {
        self.aliased.get(&object).copied()
    }

    /// The temporary the call `inst` copies its argument `index` into, which
    /// the callee owns, if it cannot pass the argument's own storage.
    pub fn temporary(
        &self,
        inst: InstId,
        index: usize,
        builder: &mut FunctionBuilder,
    ) -> Option<clif::Value> {
        let slot = self.temporary.get(&(inst, index))?;
        Some(builder.ins().stack_addr(clif::types::I64, *slot, 0))
    }

    /// Whether the store `inst` stores a value its call already wrote in
    /// place.
    pub fn stored_in_place(&self, inst: InstId) -> bool {
        self.stored_in_place.contains(&inst)
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
        if let Some(&(parent, offset)) = self.embedded.get(&value) {
            let parent = self.address(parent, builder)?;
            return Ok(builder.ins().iadd_imm_s(parent, i64::from(offset)));
        }
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

    /// Whether the `insert_value` `inst` finds its aggregate value already in
    /// its field.
    pub fn inserts_in_place(&self, inst: InstId) -> bool {
        self.in_place.contains(&inst)
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

/// What the frame plan needs to know of the function's calls.
pub(super) trait CallFacts {
    /// Whether the call `call` is a tail call.
    fn is_tail_call(&self, call: InstId) -> bool;
    /// Whether `callee` owns its argument `index` (`Ownership`).
    fn owns(&self, callee: FuncRef, index: usize) -> bool;
    /// Whether the function being translated owns its argument `index`.
    fn owns_arg(&self, index: usize) -> bool;
    /// Whether `callee` may write through its argument `index`.
    fn may_write(&self, callee: FuncRef, index: usize) -> bool;
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
    /// Calls writing their result into an object, with the object and the
    /// store.
    destination: FxHashMap<InstId, (ValueId, InstId)>,
    /// The class of each owned argument copied into a temporary.
    temporaries: Vec<((InstId, usize), usize)>,
    /// Objects living in an argument's storage, with the argument, the
    /// object's offset there and the store that would have copied it.
    aliased: FxHashMap<ValueId, (ValueId, u32, InstId)>,
    /// Classes living in a field of another class's storage, with that
    /// class and the field's offset.
    embedded: FxHashMap<usize, (usize, u32)>,
    /// Inserts whose aggregate value is already in their field.
    in_place: FxHashSet<InstId>,
    /// Classes built at the destination of the store of their last value,
    /// with the destination and the store.
    stored: FxHashMap<usize, (ValueId, InstId)>,
}

impl Plan {
    fn new(
        function: &Function,
        cfg: &ControlFlowGraph,
        block_order: &[BlockId],
        calls: &impl CallFacts,
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
            destination: FxHashMap::default(),
            temporaries: Vec::new(),
            aliased: FxHashMap::default(),
            embedded: FxHashMap::default(),
            in_place: FxHashSet::default(),
            stored: FxHashMap::default(),
        };
        let local = local_objects(function);
        // Objects initialized from a by-reference argument, or a constant
        // projection of one, in the entry block before any other use, and
        // not written afterwards.
        if let Some(entry) = function.layout.entry_block() {
            for inst in function.layout.iter_inst(entry) {
                let NativeInstKind::ObjStore(store) =
                    native_inst_set().resolve_inst(dfg.inst(inst))
                else {
                    continue;
                };
                let (object, value) = (*store.object(), *store.value());
                let is_object = dfg.value_inst(object).is_some_and(|alloc| {
                    matches!(
                        native_inst_set().resolve_inst(dfg.inst(alloc)),
                        NativeInstKind::ObjAlloc(alloc) if *alloc.ty() == dfg.value_ty(value)
                    )
                });
                let first_use = function
                    .layout
                    .iter_inst(entry)
                    .find(|&other| dfg.users(object).any(|&user| user == other));
                if is_object
                    && local.get(&object) == Some(&object)
                    && let Some((arg, offset)) = argument_storage(function, value, calls)?
                    && uses_indirect_value_representation(ctx, dfg.value_ty(value))
                    && first_use == Some(inst)
                    && !object_written_after(function, cfg, &position, &local, object, inst, calls)
                {
                    plan.aliased.insert(object, (arg, offset, inst));
                }
            }
        }
        // The local object each call argument passed in place reads.
        let mut passed_from = FxHashMap::<ValueId, ValueId>::default();
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
                    NativeInstKind::ObjLoad(load)
                        if let Some(&object) = local.get(load.object())
                            && passed_once(function, inst, result, object, &local, calls)
                                .is_some() =>
                    {
                        plan.forwarded.insert(result);
                        passed_from.insert(result, object);
                        None
                    }
                    NativeInstKind::ObjLoad(load)
                        if let Some(&object) = local.get(load.object())
                            && !object_written_while_read(
                                function, cfg, &position, &local, object, inst, result, calls,
                            ) =>
                    {
                        plan.forwarded.insert(result);
                        None
                    }
                    NativeInstKind::Call(_)
                        if !calls.is_tail_call(inst)
                            && let Some(target) = result_destination(
                                function,
                                &position,
                                inst,
                                result,
                                &local,
                                &passed_from,
                            ) =>
                    {
                        plan.destination.insert(inst, target);
                        None
                    }
                    NativeInstKind::Mload(_)
                    | NativeInstKind::ObjLoad(_)
                    | NativeInstKind::Call(_)
                    | NativeInstKind::EnumMake(_)
                    | NativeInstKind::Sha256Compress(_) => Some(position[inst]),
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
                    NativeInstKind::EnumExtract(extract) => {
                        if let Some(&class) = class_of.get(extract.value()) {
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

        plan.embed(function, &class_of)?;
        plan.store_in_place(function, &position, &local, calls);

        // Owned arguments the caller cannot give away go through temporaries.
        for &block in block_order {
            for inst in function.layout.iter_inst(block) {
                let NativeInstKind::Call(call) = native_inst_set().resolve_inst(dfg.inst(inst))
                else {
                    continue;
                };
                if calls.is_tail_call(inst) {
                    continue;
                }
                let args = call.args();
                for (index, &arg) in args.iter().enumerate() {
                    let ty = dfg.value_ty(arg);
                    if !calls.owns(*call.callee(), index)
                        || !uses_indirect_value_representation(ctx, ty)
                    {
                        continue;
                    }
                    let shared = |same: &dyn Fn(ValueId) -> bool| {
                        args.iter()
                            .enumerate()
                            .any(|(other, &value)| other != index && same(value))
                    };
                    let given = if let Some(&object) = passed_from.get(&arg) {
                        // Only an object in its own slot is this function's to give.
                        // `object_written_after` counts the call as a write of it.
                        dfg.value_inst(object).is_some()
                            && !plan.aliased.contains_key(&object)
                            && !shared(&|value| passed_from.get(&value) == Some(&object))
                            && !object_used_after(function, cfg, &position, &local, object, inst)
                    } else {
                        class_of.get(&arg).is_some_and(|&class| {
                            plan.members[class][0] == arg
                                && plan.classes[class].end == position[inst]
                                && !shared(&|value| class_of.get(&value) == Some(&class))
                        })
                    };
                    if !given {
                        let class = plan.classes.len();
                        plan.classes.push(Class {
                            def_block: block,
                            start: position[inst],
                            end: position[inst],
                            size: value_storage_size(ty, ctx)?,
                            align: value_storage_alignment(ty, ctx)?,
                            returned: false,
                        });
                        plan.members.push(Vec::new());
                        plan.temporaries.push(((inst, index), class));
                    }
                }
            }
        }
        Ok(plan)
    }

    /// Builds each `insert_value` chain on undef whose last value is only
    /// stored into an object at that object, with the classes embedded in
    /// it, when the object's address is defined before the first of them
    /// starts and nothing from there to the store may read or write the
    /// object, which would see it written early. Every class embedded in it
    /// must be such a chain or an `enum.make` in its block too, so that all
    /// of them write the object only there.
    ///
    /// Only the function's own uses of its addresses reach a local object,
    /// so the instructions in between may be anything else, and a forwarded
    /// load, which reads its source where it is used, reaches the object
    /// only if that source is one of its addresses. Any other object may be
    /// reached through memory, so everything in between must be free of
    /// effects, and no forwarded load may be used there or inserted. An
    /// object built in the storage of an argument the function owns is read
    /// by the argument's reads too.
    fn store_in_place(
        &mut self,
        function: &Function,
        position: &SecondaryMap<InstId, u32>,
        local: &FxHashMap<ValueId, ValueId>,
        calls: &impl CallFacts,
    ) {
        let dfg = &function.dfg;
        // The reads of each argument the function owns whose storage holds
        // a local object (`Ownership`), by that object: they read the
        // object, and may follow its initializing store.
        let owned_reads: FxHashMap<ValueId, Vec<InstId>> = function
            .arg_values
            .iter()
            .enumerate()
            .filter(|&(index, _)| calls.owns_arg(index))
            .flat_map(|(_, &arg)| {
                dfg.users(arg).filter_map(move |&user| {
                    match native_inst_set().resolve_inst(dfg.inst(user)) {
                        NativeInstKind::ObjStore(store) if *store.value() == arg => {
                            Some((*store.object(), value_reads(function, arg)))
                        }
                        _ => None,
                    }
                })
            })
            .collect();
        // The classes embedded in each class, directly or not.
        let mut descendants = FxHashMap::<usize, Vec<usize>>::default();
        for &child in self.embedded.keys() {
            let mut outer = child;
            while let Some(&(parent, _)) = self.embedded.get(&outer) {
                descendants.entry(parent).or_default().push(child);
                outer = parent;
            }
        }
        // The `insert_value` chain of a class on undef, if it is one: each
        // insert with the value it inserts.
        let chain_of = |class: usize| -> Option<Vec<(InstId, ValueId)>> {
            let head = dfg.value_inst(*self.members[class].first()?)?;
            let chain: Option<Vec<_>> = std::iter::successors(Some(head), |&inst| {
                self.continuation.get(&dfg.inst_result(inst)?).copied()
            })
            .map(
                |inst| match native_inst_set().resolve_inst(dfg.inst(inst)) {
                    NativeInstKind::InsertValue(insert) => {
                        Some((inst, *insert.dest(), *insert.value()))
                    }
                    _ => None,
                },
            )
            .collect();
            let chain = chain?;
            is_undef(function, chain[0].1).then(|| {
                chain
                    .into_iter()
                    .map(|(inst, _, value)| (inst, value))
                    .collect()
            })
        };
        // The instructions that write a class embedded in such a chain, with
        // the values they read: its own chain, or an `enum.make`, which
        // writes the tag and the variant's fields.
        let writes_of = |class: usize| -> Option<Vec<(InstId, ValueId)>> {
            if let Some(chain) = chain_of(class) {
                return Some(chain);
            }
            let [root] = self.members[class][..] else {
                return None;
            };
            let inst = dfg.value_inst(root)?;
            let NativeInstKind::EnumMake(make) = native_inst_set().resolve_inst(dfg.inst(inst))
            else {
                return None;
            };
            Some(make.values().iter().map(|&value| (inst, value)).collect())
        };
        'classes: for class in 0..self.classes.len() {
            if self.embedded.contains_key(&class) {
                continue;
            }
            let Some(chain) = chain_of(class) else {
                continue;
            };
            let (head, _) = chain[0];
            let Some(tail) = chain.last().and_then(|&(inst, _)| dfg.inst_result(inst)) else {
                continue;
            };
            let mut users = dfg.users(tail).copied();
            let (Some(store), None) = (users.next(), users.next()) else {
                continue;
            };
            let NativeInstKind::ObjStore(info) = native_inst_set().resolve_inst(dfg.inst(store))
            else {
                continue;
            };
            let block = function.layout.inst_block(head);
            if *info.value() != tail || function.layout.inst_block(store) != block {
                continue;
            }
            let object = *info.object();
            let root = local.get(&object).copied();
            // Whether the forwarded load `value` may read the object.
            let reads_object = |value: ValueId| {
                let source = dfg.value_inst(value).and_then(|load| {
                    match native_inst_set().resolve_inst(dfg.inst(load)) {
                        NativeInstKind::ObjLoad(load) => local.get(load.object()),
                        _ => None,
                    }
                });
                self.forwarded.contains(&value) && root.is_none_or(|root| source == Some(&root))
            };
            let mut writes = chain.clone();
            for &child in descendants.get(&class).into_iter().flatten() {
                let Some(child_writes) = writes_of(child) else {
                    continue 'classes;
                };
                if child_writes
                    .iter()
                    .any(|&(inst, _)| function.layout.inst_block(inst) != block)
                {
                    continue 'classes;
                }
                writes.extend(child_writes);
            }
            if writes.iter().any(|&(_, value)| reads_object(value)) {
                continue;
            }
            let builders: FxHashSet<InstId> = writes.iter().map(|&(inst, _)| inst).collect();
            let Some(&first) = builders.iter().min_by_key(|&&inst| position[inst]) else {
                continue;
            };
            let defined_before = dfg.value_inst(object).is_none_or(|def| {
                function.layout.inst_block(def) != block || position[def] < position[first]
            });
            let reads_owner = owned_reads.get(&root.unwrap_or(object));
            let touches_object = |inst: InstId| {
                if reads_owner.is_some_and(|reads| reads.contains(&inst)) {
                    return true;
                }
                let operands = dfg.inst(inst).collect_values();
                match root {
                    Some(root) => operands
                        .iter()
                        .any(|&value| local.get(&value) == Some(&root) || reads_object(value)),
                    None => {
                        !dfg.has_value_semantics(inst)
                            || operands.iter().any(|value| self.forwarded.contains(value))
                    }
                }
            };
            let untouched = std::iter::successors(function.layout.next_inst_of(first), |&next| {
                function.layout.next_inst_of(next)
            })
            .take_while(|&next| next != store)
            .all(|next| builders.contains(&next) || !touches_object(next));
            if defined_before && untouched {
                self.stored.insert(class, (object, store));
            }
        }
    }

    /// Places each class whose last value only fills a field of an
    /// `insert_value` chain with an undef source in that chain's storage.
    /// The chain zeroes only fields no insert of it writes, so building the
    /// class there before the chain starts loses nothing.
    fn embed(
        &mut self,
        function: &Function,
        class_of: &FxHashMap<ValueId, usize>,
    ) -> Result<(), String> {
        let dfg = &function.dfg;
        let insert_of = |inst: InstId| match native_inst_set().resolve_inst(dfg.inst(inst)) {
            NativeInstKind::InsertValue(insert) => Some(insert),
            _ => None,
        };
        for child in 0..self.classes.len() {
            let Some(&root) = self.members[child].first() else {
                continue;
            };
            let Some(root_inst) = dfg.value_inst(root) else {
                continue;
            };
            // An edge copies a block's aggregate phis in parallel, ordered by
            // the phis' own storage, so only a lone one may live in a field.
            if dfg.cast_phi(root_inst).is_some() {
                let block = function.layout.inst_block(root_inst);
                let aggregate_phis = function
                    .layout
                    .iter_inst(block)
                    .take_while(|&inst| dfg.is_phi(inst))
                    .filter(|&inst| {
                        dfg.inst_result(inst)
                            .is_some_and(|result| class_of.contains_key(&result))
                    })
                    .count();
                if aggregate_phis != 1 {
                    continue;
                }
            }
            let tail = std::iter::successors(Some(root), |value| {
                dfg.inst_result(*self.continuation.get(value)?)
            })
            .last()
            .unwrap_or(root);
            let mut users = dfg.users(tail).copied();
            let (Some(insert_inst), None) = (users.next(), users.next()) else {
                continue;
            };
            let Some(insert) = insert_of(insert_inst) else {
                continue;
            };
            let Some(parent) = dfg
                .inst_result(insert_inst)
                .and_then(|result| class_of.get(&result).copied())
            else {
                continue;
            };
            if *insert.value() != tail || *insert.dest() == tail || parent == child {
                continue;
            }
            let Some(head) = dfg.value_inst(self.members[parent][0]) else {
                continue;
            };
            if !insert_of(head).is_some_and(|head| is_undef(function, *head.dest())) {
                continue;
            }
            let index = constant_value_index(function, *insert.idx(), "insert_value")?;
            let chain = std::iter::successors(Some(head), |&inst| {
                self.continuation.get(&dfg.inst_result(inst)?).copied()
            });
            let mut writes = 0;
            for inst in chain {
                let insert = insert_of(inst).ok_or("insert chain continues past insert_value")?;
                if constant_value_index(function, *insert.idx(), "insert_value")? == index {
                    writes += 1;
                }
            }
            if writes != 1 {
                continue;
            }
            let ty = dfg.value_ty(self.members[parent][0]);
            let (offset, _) = aggregate_elem_offset(function.ctx(), ty, index)?;
            self.embedded.insert(child, (parent, offset as u32));
            self.in_place.insert(insert_inst);
        }
        // Each outermost class's storage holds the classes inside it while
        // they live.
        let embedded: Vec<_> = self.embedded.keys().copied().collect();
        for child in embedded {
            let Class { start, end, .. } = self.classes[child];
            let mut outer = child;
            while let Some(&(parent, _)) = self.embedded.get(&outer) {
                outer = parent;
            }
            self.classes[outer].cover(start);
            self.classes[outer].cover(end);
        }
        Ok(())
    }
}

/// Whether the local object `object` may be used after the call `call`: an
/// address of it is used later in the call's block, or in a block the call
/// reaches, which includes the call's own block when it is in a loop.
fn object_used_after(
    function: &Function,
    cfg: &ControlFlowGraph,
    position: &SecondaryMap<InstId, u32>,
    local: &FxHashMap<ValueId, ValueId>,
    object: ValueId,
    call: InstId,
) -> bool {
    object_uses(function, local, object).any(runs_after(function, cfg, position, call))
}

/// The by-reference argument whose storage holds `value`, with `value`'s
/// offset there: the argument itself, or a projection of it by constant
/// indices that the function cannot write, as it neither owns the argument
/// nor passes it on to a callee that does.
fn argument_storage(
    function: &Function,
    mut value: ValueId,
    calls: &impl CallFacts,
) -> Result<Option<(ValueId, u32)>, String> {
    let dfg = &function.dfg;
    let mut offset = 0;
    loop {
        if let Some(index) = function.arg_values.iter().position(|&arg| arg == value) {
            return Ok((offset == 0 || !calls.owns_arg(index)).then_some((value, offset)));
        }
        let Some(inst) = dfg.value_inst(value) else {
            return Ok(None);
        };
        let NativeInstKind::ExtractValue(extract) = native_inst_set().resolve_inst(dfg.inst(inst))
        else {
            return Ok(None);
        };
        let index = constant_value_index(function, *extract.idx(), "extract_value")?;
        value = *extract.dest();
        let (field, _) = aggregate_elem_offset(function.ctx(), dfg.value_ty(value), index)?;
        offset += field as u32;
    }
}

/// Whether anything after `inst` may write the local object `object`.
fn object_written_after(
    function: &Function,
    cfg: &ControlFlowGraph,
    position: &SecondaryMap<InstId, u32>,
    local: &FxHashMap<ValueId, ValueId>,
    object: ValueId,
    inst: InstId,
    calls: &impl CallFacts,
) -> bool {
    object_writes(function, cfg, position, local, object, calls)
        .any(runs_after(function, cfg, position, inst))
}

/// Whether something may write the local object `object` after the load
/// `inst` of it and before, or at, a read of its result `result` or of a
/// view of that result, which reads the object in place.
#[allow(clippy::too_many_arguments)]
fn object_written_while_read(
    function: &Function,
    cfg: &ControlFlowGraph,
    position: &SecondaryMap<InstId, u32>,
    local: &FxHashMap<ValueId, ValueId>,
    object: ValueId,
    inst: InstId,
    result: ValueId,
    calls: &impl CallFacts,
) -> bool {
    let reads = value_reads(function, result);
    let after_load = runs_after(function, cfg, position, inst);
    object_writes(function, cfg, position, local, object, calls).any(|write| {
        after_load(write) && {
            let after_write = runs_after(function, cfg, position, write);
            reads.iter().any(|&read| read == write || after_write(read))
        }
    })
}

/// The instructions that may write the local object `object`, each where
/// the write happens: a store into it, a call that may write through one of
/// its addresses, or a call its storage may be given to. That is a call
/// passed a load of the object in place (`passed_once`) for an argument its
/// callee owns, when the object is an `obj.alloc` not used after the call.
fn object_writes<'a>(
    function: &'a Function,
    cfg: &'a ControlFlowGraph,
    position: &'a SecondaryMap<InstId, u32>,
    local: &'a FxHashMap<ValueId, ValueId>,
    object: ValueId,
    calls: &'a impl CallFacts,
) -> impl Iterator<Item = InstId> + 'a {
    let dfg = &function.dfg;
    object_uses(function, local, object).filter_map(move |user| {
        match native_inst_set().resolve_inst(dfg.inst(user)) {
            NativeInstKind::ObjStore(_) => Some(user),
            NativeInstKind::Call(call) => call
                .args()
                .iter()
                .enumerate()
                .any(|(index, arg)| {
                    local.get(arg) == Some(&object) && calls.may_write(*call.callee(), index)
                })
                .then_some(user),
            NativeInstKind::ObjLoad(_) => {
                let loaded = dfg.inst_result(user)?;
                let (call, info) = passed_once(function, user, loaded, object, local, calls)?;
                (dfg.value_inst(object).is_some()
                    && info
                        .args()
                        .iter()
                        .enumerate()
                        .any(|(index, &arg)| arg == loaded && calls.owns(*info.callee(), index))
                    && !object_used_after(function, cfg, position, local, object, call))
                .then_some(call)
            }
            _ => None,
        }
    })
}

/// The instructions reading the aggregate `value` where they run, when it
/// is left in its source's storage: its users, and those of the views
/// `extract_value` and `enum.extract` take of it.
fn value_reads(function: &Function, value: ValueId) -> Vec<InstId> {
    let dfg = &function.dfg;
    let mut reads = Vec::new();
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        for &user in dfg.users(value) {
            reads.push(user);
            let view = match native_inst_set().resolve_inst(dfg.inst(user)) {
                NativeInstKind::ExtractValue(extract) if *extract.dest() == value => {
                    dfg.inst_result(user)
                }
                NativeInstKind::EnumExtract(extract) if *extract.value() == value => {
                    dfg.inst_result(user)
                }
                _ => None,
            };
            if let Some(view) = view
                && uses_indirect_value_representation(function.ctx(), dfg.value_ty(view))
            {
                pending.push(view);
            }
        }
    }
    reads
}

/// The uses of addresses of the local object `object`.
fn object_uses<'a>(
    function: &'a Function,
    local: &'a FxHashMap<ValueId, ValueId>,
    object: ValueId,
) -> impl Iterator<Item = InstId> + 'a {
    local
        .iter()
        .filter(move |&(_, &of)| of == object)
        .flat_map(move |(&address, _)| function.dfg.users(address).copied())
}

/// Whether an instruction may run after `inst`: later in its block, or in a
/// block it reaches, which includes its own block when that is in a loop.
fn runs_after<'a>(
    function: &'a Function,
    cfg: &ControlFlowGraph,
    position: &'a SecondaryMap<InstId, u32>,
    inst: InstId,
) -> impl Fn(InstId) -> bool + 'a {
    let block = function.layout.inst_block(inst);
    let mut reached = FxHashSet::default();
    let mut pending: Vec<_> = cfg.succs_of(block).copied().collect();
    while let Some(next) = pending.pop() {
        if reached.insert(next) {
            pending.extend(cfg.succs_of(next).copied());
        }
    }
    move |other| {
        let other_block = function.layout.inst_block(other);
        reached.contains(&other_block) || other_block == block && position[other] > position[inst]
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

/// Each address of a local object whose address does not escape, with the
/// object (its `obj.alloc`, or a `noalias` object argument): one only
/// projected, indexed, loaded, stored into, and passed to `nocapture`
/// parameters, so that a callee reaches it only through its call's
/// arguments.
fn local_objects(function: &Function) -> FxHashMap<ValueId, ValueId> {
    let dfg = &function.dfg;
    let ctx = function.ctx();
    let mut object_of = FxHashMap::default();
    let mut escaped = FxHashSet::default();
    let mut pending: Vec<_> = function
        .layout
        .iter_block()
        .flat_map(|block| function.layout.iter_inst(block))
        .filter(|&inst| {
            matches!(
                native_inst_set().resolve_inst(dfg.inst(inst)),
                NativeInstKind::ObjAlloc(_)
            )
        })
        .filter_map(|inst| dfg.inst_result(inst))
        .chain(function.arg_values.iter().copied().filter(|&arg| {
            function.is_noalias_arg(arg)
                && matches!(
                    dfg.value_ty(arg).resolve_compound(ctx),
                    Some(CompoundType::ObjRef(_))
                )
        }))
        .map(|object| (object, object))
        .collect();
    while let Some((address, object)) = pending.pop() {
        object_of.insert(address, object);
        for &user in dfg.users(address) {
            let derived = match native_inst_set().resolve_inst(dfg.inst(user)) {
                NativeInstKind::ObjProj(proj)
                    if proj.values()[1..].iter().all(|&v| v != address) =>
                {
                    dfg.inst_result(user)
                }
                NativeInstKind::ObjIndex(index) if *index.index() != address => {
                    dfg.inst_result(user)
                }
                NativeInstKind::ObjLoad(_) => None,
                NativeInstKind::ObjStore(store) if *store.value() != address => None,
                NativeInstKind::Call(call)
                    if call.args().iter().enumerate().all(|(index, &arg)| {
                        arg != address
                            || ctx.func_sig(*call.callee(), |sig| sig.is_nocapture_arg(index))
                    }) =>
                {
                    None
                }
                _ => {
                    escaped.insert(object);
                    None
                }
            };
            if let Some(derived) = derived {
                pending.push((derived, object));
            }
        }
    }
    object_of.retain(|_, object| !escaped.contains(object));
    object_of
}

/// The call the only use of the load `inst` of the local object `object`
/// passes it to, if that is later in its block, not a tail call, with no
/// state change in between, and no other argument reaching the object.
fn passed_once<'a>(
    function: &'a Function,
    inst: InstId,
    result: ValueId,
    object: ValueId,
    local: &FxHashMap<ValueId, ValueId>,
    calls: &impl CallFacts,
) -> Option<(InstId, &'a Call)> {
    let dfg = &function.dfg;
    let mut users = dfg.users(result);
    let (Some(&call), None) = (users.next(), users.next()) else {
        return None;
    };
    let NativeInstKind::Call(info) = native_inst_set().resolve_inst(dfg.inst(call)) else {
        return None;
    };
    (!calls.is_tail_call(call)
        && info
            .args()
            .iter()
            .all(|arg| *arg == result || local.get(arg) != Some(&object))
        && unchanged_between(function, inst, call))
    .then_some((call, info))
}

/// For the call `inst`, whose result `result` its only use stores into a
/// local object later in its block with no state change in between: that
/// object's address, defined before the call, and the store, unless an
/// argument reaches the object or an instruction in between reads it, which
/// would see the result early.
fn result_destination(
    function: &Function,
    position: &SecondaryMap<InstId, u32>,
    inst: InstId,
    result: ValueId,
    local: &FxHashMap<ValueId, ValueId>,
    passed_from: &FxHashMap<ValueId, ValueId>,
) -> Option<(ValueId, InstId)> {
    let dfg = &function.dfg;
    let mut users = dfg.users(result);
    let (Some(&store), None) = (users.next(), users.next()) else {
        return None;
    };
    let NativeInstKind::ObjStore(info) = native_inst_set().resolve_inst(dfg.inst(store)) else {
        return None;
    };
    let address = *info.object();
    let object = *local.get(&address)?;
    let NativeInstKind::Call(call) = native_inst_set().resolve_inst(dfg.inst(inst)) else {
        return None;
    };
    let defined_before = dfg.value_inst(address).is_none_or(|def| {
        function.layout.inst_block(def) != function.layout.inst_block(inst)
            || position[def] < position[inst]
    });
    (*info.value() == result
        && defined_before
        && call
            .args()
            .iter()
            .all(|arg| local.get(arg) != Some(&object) && passed_from.get(arg) != Some(&object))
        && unchanged_between(function, inst, store)
        && std::iter::successors(function.layout.next_inst_of(inst), |&next| {
            function.layout.next_inst_of(next)
        })
        .take_while(|&next| next != store)
        .all(|next| {
            !dfg.inst(next)
                .collect_values()
                .iter()
                .any(|value| local.get(value) == Some(&object))
        }))
    .then_some((address, store))
}

/// Whether `last` follows `first` in its block with no instruction in
/// between that may change state.
fn unchanged_between(function: &Function, first: InstId, last: InstId) -> bool {
    function.layout.inst_block(first) == function.layout.inst_block(last)
        && std::iter::successors(function.layout.next_inst_of(first), |&next| {
            function.layout.next_inst_of(next)
        })
        .take_while(|&next| next != last)
        .all(|next| !function.dfg.may_mutate_state(next))
        && std::iter::successors(function.layout.next_inst_of(first), |&next| {
            function.layout.next_inst_of(next)
        })
        .any(|next| next == last)
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

    use sonatina_ir::{inst::InstId, module::FuncRef};

    use super::{CallFacts, FrameSlots};

    /// Calls nothing is known of: no tail calls or owned arguments, and
    /// every call may write through every argument.
    struct NoCalls;

    impl CallFacts for NoCalls {
        fn is_tail_call(&self, _: InstId) -> bool {
            false
        }
        fn owns(&self, _: FuncRef, _: usize) -> bool {
            false
        }
        fn owns_arg(&self, _: usize) -> bool {
            false
        }
        fn may_write(&self, _: FuncRef, _: usize) -> bool {
            true
        }
    }

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
            FrameSlots::new(function, &cfg, &block_order, None, &NoCalls, &mut builder).unwrap();
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
    fn inserted_values_live_in_their_fields() {
        // The call result and the inner chain only fill fields of the outer
        // chain, so they are built in its storage.
        let sizes = slot_sizes(
            r#"
declare external %g() -> [i64; 32];
func public %f(v0.*[[i64; 32]; 2]) {
block0:
    v1.[i64; 32] = call %g;
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 5.i64;
    v3.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 0.i64 v1;
    v4.[[i64; 32]; 2] = insert_value v3 1.i64 v2;
    mstore v0 v4 [[i64; 32]; 2];
    return;
}
"#,
        );
        assert_eq!(sizes, [512]);
    }

    #[test]
    fn values_inserted_over_defined_sources_keep_their_storage() {
        // The chain copies the loaded `v2` over all its storage first.
        let sizes = slot_sizes(
            r#"
declare external %g() -> [i64; 32];
func public %f(v0.*[[i64; 32]; 2]) {
block0:
    v1.[i64; 32] = call %g;
    v2.[[i64; 32]; 2] = mload v0 [[i64; 32]; 2];
    v3.[[i64; 32]; 2] = insert_value v2 0.i64 v1;
    mstore v0 v3 [[i64; 32]; 2];
    return;
}
"#,
        );
        assert_eq!(sizes, [256, 512]);
    }

    #[test]
    fn values_for_rewritten_fields_keep_their_storage() {
        // Field 0 is written twice, so `v1` and `v2` cannot both live there.
        let sizes = slot_sizes(
            r#"
declare external %g() -> [i64; 32];
func public %f(v0.*[[i64; 32]; 2]) {
block0:
    v1.[i64; 32] = call %g;
    v2.[i64; 32] = call %g;
    v3.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 0.i64 v1;
    v4.[[i64; 32]; 2] = insert_value v3 0.i64 v2;
    mstore v0 v4 [[i64; 32]; 2];
    return;
}
"#,
        );
        assert_eq!(sizes, [256, 256, 512]);
    }

    #[test]
    fn stored_chains_are_built_at_their_destination() {
        // `v2`'s chain is only stored into `v1`; `v5`'s store into memory
        // follows a load of memory, which may read it, so it is built in a
        // slot and copied.
        let sizes = slot_sizes(
            r#"
func public %f(v0.i64, v4.*i64, v7.*[i64; 32]) {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v3.[i64; 32] = insert_value v2 1.i64 v0;
    obj.store v1 v3;
    v8.objref<[i64; 32]> = obj.from_ptr v7;
    v5.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v6.i64 = mload v4 i64;
    obj.store v8 v5;
    mstore v4 v6 i64;
    return;
}
"#,
        );
        assert_eq!(sizes, [256]);
    }

    #[test]
    fn chains_stored_into_local_objects_are_built_there_across_other_effects() {
        // Nothing but its own uses reaches `v1`, so neither the store to
        // memory nor the call between `v2`'s chain and `v1`'s store sees `v1`
        // written early.
        let sizes = slot_sizes(
            r#"
declare external %g(i64) -> i64;
func public %f(v0.i64, v7.*i64) {
block0:
    v1.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    mstore v7 v0 i64;
    v3.i64 = call %g v0;
    v4.[i64; 32] = insert_value undef.[i64; 32] 5.i64 v3;
    v5.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 1.i64 v2;
    v6.[[i64; 32]; 2] = insert_value v5 0.i64 v4;
    obj.store v1 v6;
    return;
}
"#,
        );
        assert_eq!(sizes, [0u32; 0]);
    }

    #[test]
    fn chains_stored_into_local_objects_keep_storage_when_the_object_is_read_between() {
        // `v4` reads `v1`'s second field after `v2` would have written it.
        // (Built there, the chains would need no slot.)
        let sizes = slot_sizes(
            r#"
func public %f(v0.i64, v10.*i64) {
block0:
    v1.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    v14.objref<[i64; 32]> = obj.index v1 1.i64;
    v3.objref<i64> = obj.index v14 2.i64;
    obj.store v3 v0;
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v4.i64 = obj.load v3;
    mstore v10 v4 i64;
    v5.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 1.i64 v2;
    obj.store v1 v5;
    return;
}
"#,
        );
        assert_eq!(sizes, [512]);
    }

    #[test]
    fn chains_stored_into_local_objects_keep_storage_when_they_insert_its_loads() {
        // `v4` reads `v1`'s first field in place where `v6` inserts it,
        // after `v5` would have written the second.
        let sizes = slot_sizes(
            r#"
func public %f(v0.i64) {
block0:
    v1.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    v2.objref<[i64; 32]> = obj.index v1 0.i64;
    v7.objref<i64> = obj.index v2 3.i64;
    obj.store v7 v0;
    v4.[i64; 32] = obj.load v2;
    v3.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v5.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 1.i64 v3;
    v6.[[i64; 32]; 2] = insert_value v5 0.i64 v4;
    obj.store v1 v6;
    return;
}
"#,
        );
        assert_eq!(sizes, [512]);
    }

    #[test]
    fn stored_chains_build_their_embedded_chains_at_the_destination() {
        // `v4`'s chain, built before its parent's starts, fills a field of
        // the chain stored into `v1`, so both are built in `v1`.
        let sizes = slot_sizes(
            r#"
func public %f(v0.i64) {
block0:
    v1.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v3.[i64; 32] = insert_value v2 1.i64 v0;
    v4.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 1.i64 v3;
    v5.[i64; 32] = insert_value undef.[i64; 32] 2.i64 v0;
    v6.[[i64; 32]; 2] = insert_value v4 0.i64 v5;
    obj.store v1 v6;
    return;
}
"#,
        );
        assert_eq!(sizes, [0u32; 0]);
    }

    #[test]
    fn stored_chains_build_their_embedded_enums_at_the_destination() {
        // `v3`, an enum too wide for registers, fills a field of the chain
        // stored into `v2`, so both are built in `v2`.
        let sizes = slot_sizes(
            r#"
type @kind = enum {
    #Storage(i64, i64, i64, i1),
    #Mark(i8),
};
type @change = {i64, @kind};

func public %f(v0.i64, v1.*@change) {
block0:
    v2.objref<@change> = obj.from_ptr v1;
    v3.@kind = enum.make @kind #Storage (v0, v0, v0, 1.i1);
    v4.@change = insert_value undef.@change 0.i64 v0;
    v5.@change = insert_value v4 1.i64 v3;
    obj.store v2 v5;
    return;
}
"#,
        );
        assert_eq!(sizes, [0u32; 0]);
    }

    #[test]
    fn stored_chains_keep_storage_when_a_store_comes_between_their_parts() {
        // `v2`'s chain is embedded but a store comes between it and the store
        // of its parent into memory, which may be what the chain would
        // overwrite.
        let sizes = slot_sizes(
            r#"
func public %f(v0.i64, v7.*i64, v8.*[[i64; 32]; 2]) {
block0:
    v1.objref<[[i64; 32]; 2]> = obj.from_ptr v8;
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    mstore v7 v0 i64;
    v4.[[i64; 32]; 2] = insert_value undef.[[i64; 32]; 2] 1.i64 v2;
    obj.store v1 v4;
    return;
}
"#,
        );
        assert_eq!(sizes, [512]);
    }

    #[test]
    fn chains_stored_after_object_reads_keep_their_storage() {
        // `v4` reads `v0`'s first field after `v2` would have written it.
        let sizes = slot_sizes(
            r#"
func private %f(v0.objref<[i64; 32]>, v1.i64) {
block0:
    v2.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v1;
    v3.objref<i64> = obj.index v0 0.i64;
    v4.i64 = obj.load v3;
    v5.[i64; 32] = insert_value v2 1.i64 v4;
    obj.store v0 v5;
    return;
}
"#,
        );
        assert_eq!(sizes, [256]);
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
