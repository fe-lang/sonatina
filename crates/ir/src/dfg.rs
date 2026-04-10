//! This module contains Sonatine IR data flow graph.
use std::io;

use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use dyn_clone::clone_box;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use vec_collections::VecSet;

use super::{Immediate, Type, Value, ValueId};
use crate::{
    EffectCostClass, GlobalVariableRef, Inst, InstDowncast, InstDowncastMut, InstEffectSummary,
    InstEffects, InstSetBase,
    effects::{classify_inst_effects, summarize_inst_effects},
    inst::{
        InstId,
        control_flow::{self, BranchInfo, CallInfo, Jump, Phi},
    },
    ir_writer::{FuncWriteCtx, IrWrite},
    module::ModuleCtx,
};

type UserSet = VecSet<[InstId; 2]>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ValueUsers(UserSet);

impl Default for ValueUsers {
    fn default() -> Self {
        Self(VecSet::empty())
    }
}

impl ValueUsers {
    fn as_slice(&self) -> &[InstId] {
        self.0.as_ref()
    }

    fn insert(&mut self, inst: InstId) {
        self.0.insert(inst);
    }

    fn iter(&self) -> impl Iterator<Item = &InstId> {
        self.0.iter()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn remove(&mut self, inst: &InstId) {
        self.0.remove(inst);
    }

    fn union_with(&mut self, other: &Self) {
        self.0 |= &other.0;
    }
}

pub struct DataFlowGraph {
    pub ctx: ModuleCtx,
    #[doc(hidden)]
    pub blocks: PrimaryMap<BlockId, Block>,
    live_blocks: SecondaryMap<BlockId, bool>,
    #[doc(hidden)]
    pub values: PrimaryMap<ValueId, Value>,
    live_values: SecondaryMap<ValueId, bool>,
    #[doc(hidden)]
    pub insts: PrimaryMap<InstId, Box<dyn Inst>>,
    live_insts: SecondaryMap<InstId, bool>,
    inst_results: SecondaryMap<InstId, SmallVec<[ValueId; 1]>>,
    #[doc(hidden)]
    pub immediates: FxHashMap<Immediate, ValueId>,
    #[doc(hidden)]
    pub globals: FxHashMap<GlobalVariableRef, ValueId>,
    users: SecondaryMap<ValueId, ValueUsers>,
}

impl Clone for DataFlowGraph {
    fn clone(&self) -> Self {
        let mut insts = PrimaryMap::with_capacity(self.insts.len());
        for inst in self.insts.values() {
            insts.push(clone_box(inst.as_ref()));
        }

        Self {
            ctx: self.ctx.clone(),
            blocks: self.blocks.clone(),
            live_blocks: self.live_blocks.clone(),
            values: self.values.clone(),
            live_values: self.live_values.clone(),
            insts,
            live_insts: self.live_insts.clone(),
            inst_results: self.inst_results.clone(),
            immediates: self.immediates.clone(),
            globals: self.globals.clone(),
            users: self.users.clone(),
        }
    }
}

impl DataFlowGraph {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
            ctx,
            blocks: PrimaryMap::default(),
            live_blocks: SecondaryMap::default(),
            values: PrimaryMap::default(),
            live_values: SecondaryMap::default(),
            insts: PrimaryMap::default(),
            live_insts: SecondaryMap::default(),
            inst_results: SecondaryMap::default(),
            immediates: FxHashMap::default(),
            globals: FxHashMap::default(),
            users: SecondaryMap::default(),
        }
    }

    pub fn make_block(&mut self) -> BlockId {
        let block = self.blocks.push(Block::new());
        self.live_blocks[block] = true;
        block
    }

    pub fn make_value(&mut self, value: Value) -> ValueId {
        let value_id = self.values.push(value);
        self.live_values[value_id] = true;
        value_id
    }

    pub fn make_inst<I: Inst>(&mut self, inst: I) -> InstId {
        self.make_inst_dyn(Box::new(inst))
    }

    pub fn make_inst_dyn(&mut self, inst: Box<dyn Inst>) -> InstId {
        let inst_id = self.insts.push(inst);
        self.live_insts[inst_id] = true;
        self.attach_user(inst_id);
        inst_id
    }

    pub fn clone_inst(&self, inst_id: InstId) -> Box<dyn Inst> {
        clone_box(self.inst(inst_id))
    }

    pub fn make_imm_value<Imm>(&mut self, imm: Imm) -> ValueId
    where
        Imm: Into<Immediate>,
    {
        let imm: Immediate = imm.into();
        if let Some(&value) = self.immediates.get(&imm) {
            return value;
        }

        let ty = imm.ty();
        let value_data = Value::Immediate { imm, ty };
        let value = self.make_value(value_data);
        self.immediates.insert(imm, value);
        value
    }

    pub fn make_undef_value(&mut self, ty: Type) -> ValueId {
        let value_data = Value::Undef { ty };
        self.make_value(value_data)
    }

    /// Returns inst if the value is originated from inst.
    pub fn value_inst(&self, value: ValueId) -> Option<InstId> {
        match self.value(value) {
            Value::Inst { inst, .. } => Some(*inst),
            _ => None,
        }
    }

    /// Returns `(inst, result_idx)` if the value is defined by an instruction result.
    pub fn value_inst_result(&self, value: ValueId) -> Option<(InstId, usize)> {
        match self.value(value) {
            Value::Inst {
                inst, result_idx, ..
            } => Some((*inst, usize::from(*result_idx))),
            _ => None,
        }
    }

    pub fn value_result_idx(&self, value: ValueId) -> Option<usize> {
        self.value_inst_result(value)
            .map(|(_, result_idx)| result_idx)
    }

    /// Returns immediate if the value is immediate value.
    pub fn value_imm(&self, value: ValueId) -> Option<Immediate> {
        match self.value(value) {
            Value::Immediate { imm, .. } => Some(*imm),
            _ => None,
        }
    }

    pub fn make_global_value(&mut self, gv: GlobalVariableRef) -> ValueId {
        if let Some(&value) = self.globals.get(&gv) {
            return value;
        }

        let gv_ty = self.ctx.with_gv_store(|s| s.ty(gv));
        let ty = self.ctx.with_ty_store_mut(|s| s.make_ptr(gv_ty));
        let value_data = Value::Global { gv, ty };
        let value = self.make_value(value_data);
        self.globals.insert(gv, value);
        value
    }

    pub fn replace_inst(&mut self, inst_id: InstId, new: Box<dyn Inst>) {
        self.replace_inst_preserving_results(inst_id, new);
    }

    /// Replaces an instruction in place while preserving the existing result mapping.
    ///
    /// Callers must ensure the replacement preserves result count, ordering, and types.
    pub fn replace_inst_preserving_results(&mut self, inst_id: InstId, new: Box<dyn Inst>) {
        let slot = &mut self.insts[inst_id];
        let old = &mut std::mem::replace(slot, new);

        // Remove the arguments of the old inst from the user set.
        old.for_each_value(&mut |value| {
            self.remove_user(value, inst_id);
        });

        // Attach new inst.
        self.attach_user(inst_id);
    }

    pub fn attach_results(&mut self, inst_id: InstId, values: &[ValueId]) {
        assert!(
            self.inst_results[inst_id].is_empty(),
            "results for {inst_id:?} are already attached"
        );
        for (result_idx, value_id) in values.iter().copied().enumerate() {
            assert!(
                matches!(
                    self.value(value_id),
                    Value::Inst {
                        inst,
                        result_idx: value_result_idx,
                        ..
                    } if *inst == inst_id && usize::from(*value_result_idx) == result_idx
                ),
                "attached result value {value_id:?} does not match {inst_id:?}[{result_idx}]"
            );
        }
        self.inst_results[inst_id] = SmallVec::from_slice(values);
    }

    pub fn append_result(&mut self, inst_id: InstId, value_id: ValueId) {
        let result_idx = self.inst_results[inst_id].len();
        assert!(
            matches!(
                self.value(value_id),
                Value::Inst {
                    inst,
                    result_idx: value_result_idx,
                    ..
                } if *inst == inst_id && usize::from(*value_result_idx) == result_idx
            ),
            "appended result value {value_id:?} does not match {inst_id:?}[{result_idx}]"
        );
        self.inst_results[inst_id].push(value_id);
    }

    pub fn attach_result(&mut self, inst_id: InstId, value_id: ValueId) {
        self.attach_results(inst_id, &[value_id]);
    }

    pub fn make_arg_value(&mut self, ty: Type, idx: usize) -> Value {
        Value::Arg { ty, idx }
    }

    pub fn has_block(&self, block: BlockId) -> bool {
        self.has_block_slot(block) && self.live_blocks[block]
    }

    pub fn has_block_slot(&self, block: BlockId) -> bool {
        (block.as_u32() as usize) < self.blocks.len()
    }

    pub fn has_value(&self, value: ValueId) -> bool {
        self.has_value_slot(value) && self.live_values[value]
    }

    pub fn has_value_slot(&self, value: ValueId) -> bool {
        (value.as_u32() as usize) < self.values.len()
    }

    pub fn has_inst(&self, inst: InstId) -> bool {
        self.has_inst_slot(inst) && self.live_insts[inst]
    }

    pub fn has_inst_slot(&self, inst: InstId) -> bool {
        (inst.as_u32() as usize) < self.insts.len()
    }

    pub fn block_ids(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks.keys().filter(|block| self.live_blocks[*block])
    }

    pub fn value_ids(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.values.keys().filter(|value| self.live_values[*value])
    }

    pub fn inst_ids(&self) -> impl Iterator<Item = InstId> + '_ {
        self.insts.keys().filter(|inst| self.live_insts[*inst])
    }

    pub fn values_iter(&self) -> impl Iterator<Item = (ValueId, &Value)> + '_ {
        self.values
            .iter()
            .filter(|(value, _)| self.live_values[*value])
    }

    pub fn get_inst(&self, inst_id: InstId) -> Option<&dyn Inst> {
        if !self.has_inst(inst_id) {
            return None;
        }
        Some(self.insts[inst_id].as_ref())
    }

    pub fn inst(&self, inst_id: InstId) -> &dyn Inst {
        debug_assert!(self.has_inst(inst_id));
        self.insts[inst_id].as_ref()
    }

    pub fn inst_mut(&mut self, inst_id: InstId) -> &mut dyn Inst {
        debug_assert!(self.has_inst(inst_id));
        self.insts[inst_id].as_mut()
    }

    pub fn get_inst_mut(&mut self, inst_id: InstId) -> Option<&mut dyn Inst> {
        if !self.has_inst(inst_id) {
            return None;
        }
        Some(self.insts[inst_id].as_mut())
    }

    pub fn get_value(&self, value_id: ValueId) -> Option<&Value> {
        if !self.has_value(value_id) {
            return None;
        }
        Some(&self.values[value_id])
    }

    pub fn value(&self, value_id: ValueId) -> &Value {
        debug_assert!(self.has_value(value_id));
        &self.values[value_id]
    }

    pub fn value_ty(&self, value_id: ValueId) -> Type {
        match self.value(value_id) {
            Value::Inst { ty, .. }
            | Value::Arg { ty, .. }
            | Value::Immediate { ty, .. }
            | Value::Global { ty, .. }
            | Value::Undef { ty } => *ty,
        }
    }

    pub fn value_is_imm(&self, value_id: ValueId) -> bool {
        matches!(self.value(value_id), Value::Immediate { .. })
    }

    pub fn attach_user(&mut self, inst_id: InstId) {
        let inst = &self.insts[inst_id];
        inst.for_each_value(&mut |value| {
            self.users[value].insert(inst_id);
        })
    }

    pub fn untrack_inst(&mut self, inst_id: InstId) {
        let inst = &self.insts[inst_id];
        inst.for_each_value(&mut |value| {
            self.users[value].remove(&inst_id);
        })
    }

    pub fn remove_user(&mut self, value: ValueId, user: InstId) {
        self.users[value].remove(&user);
    }

    /// Returns the all instructions that use the `value_id`.
    pub fn users(&self, value_id: ValueId) -> impl Iterator<Item = &InstId> {
        self.users[value_id].iter()
    }

    /// Returns the number of instructions that use the `value_id`.
    pub fn users_num(&self, value_id: ValueId) -> usize {
        self.users[value_id].len()
    }

    /// Clear all user sets. Used before `rebuild_users` on `Function`.
    pub fn clear_users(&mut self) {
        self.users.clear();
    }

    pub fn users_set(&self, value_id: ValueId) -> Option<&[InstId]> {
        self.users.get(value_id).map(ValueUsers::as_slice)
    }

    pub fn inst_results(&self, inst_id: InstId) -> &[ValueId] {
        debug_assert!(self.has_inst(inst_id));
        self.inst_results[inst_id].as_slice()
    }

    pub fn try_inst_results(&self, inst_id: InstId) -> Option<&[ValueId]> {
        if !self.has_inst(inst_id) {
            return None;
        }
        Some(self.inst_results[inst_id].as_slice())
    }

    pub fn inst_result_at(&self, inst_id: InstId, idx: usize) -> Option<ValueId> {
        self.inst_results(inst_id).get(idx).copied()
    }

    pub fn single_inst_result(&self, inst_id: InstId) -> Option<ValueId> {
        let results = self.inst_results(inst_id);
        assert!(
            results.len() <= 1,
            "single_inst_result called on multi-result instruction {inst_id:?}"
        );
        results.first().copied()
    }

    pub fn try_single_inst_result(&self, inst_id: InstId) -> Option<Option<ValueId>> {
        self.try_inst_results(inst_id).map(|results| {
            assert!(
                results.len() <= 1,
                "try_single_inst_result called on multi-result instruction {inst_id:?}"
            );
            results.first().copied()
        })
    }

    pub fn inst_result(&self, inst_id: InstId) -> Option<ValueId> {
        self.single_inst_result(inst_id)
    }

    pub fn try_inst_result(&self, inst_id: InstId) -> Option<Option<ValueId>> {
        self.try_single_inst_result(inst_id)
    }

    pub fn branch_info(&self, inst_id: InstId) -> Option<&dyn BranchInfo> {
        let inst = self.inst(inst_id);
        InstDowncast::downcast(self.ctx.inst_set, inst)
    }

    pub fn is_terminator(&self, inst_id: InstId) -> bool {
        self.inst(inst_id).is_terminator()
    }

    pub fn is_exit(&self, inst_id: InstId) -> bool {
        self.is_terminator(inst_id) && self.branch_info(inst_id).is_none()
    }

    pub fn append_phi_arg(&mut self, inst_id: InstId, value: ValueId, block: BlockId) {
        let Some(phi) = self.cast_phi_mut(inst_id) else {
            return;
        };
        phi.append_phi_arg(value, block);
        self.attach_user(inst_id);
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.ctx.inst_set
    }

    pub fn cast_phi(&self, inst_id: InstId) -> Option<&control_flow::Phi> {
        let inst = self.inst(inst_id);
        let is = self.inst_set();
        InstDowncast::downcast(is, inst)
    }

    pub fn cast_phi_mut(&mut self, inst_id: InstId) -> Option<&mut control_flow::Phi> {
        let is = self.inst_set();
        let inst = self.inst_mut(inst_id);
        InstDowncastMut::downcast_mut(is, inst)
    }

    pub fn call_info(&self, inst_id: InstId) -> Option<&dyn CallInfo> {
        let inst = self.inst(inst_id);
        InstDowncast::downcast(self.ctx.inst_set, inst)
    }

    pub fn cast_jump(&self, inst_id: InstId) -> Option<&control_flow::Jump> {
        let inst = self.inst(inst_id);
        let is = self.inst_set();
        InstDowncast::downcast(is, inst)
    }

    pub fn cast_jump_mut(&mut self, inst_id: InstId) -> Option<&mut control_flow::Jump> {
        let is = self.inst_set();
        let inst = self.inst_mut(inst_id);
        InstDowncastMut::downcast_mut(is, inst)
    }

    pub fn cast_call(&self, inst_id: InstId) -> Option<&control_flow::Call> {
        let inst = self.inst(inst_id);
        let is = self.inst_set();
        InstDowncast::downcast(is, inst)
    }

    pub fn cast_br_table(&self, inst_id: InstId) -> Option<&control_flow::BrTable> {
        let inst = self.inst(inst_id);
        let is = self.inst_set();
        InstDowncast::downcast(is, inst)
    }

    pub fn make_phi(&self, args: Vec<(ValueId, BlockId)>) -> Phi {
        Phi::new(self.inst_set().phi(), args)
    }

    pub fn make_jump(&self, to: BlockId) -> Jump {
        Jump::new(self.inst_set().jump(), to)
    }

    pub fn change_to_alias(&mut self, value: ValueId, alias: ValueId) {
        let users = std::mem::take(&mut self.users[value]);
        for inst in users.iter() {
            self.insts[*inst].for_each_value_mut(&mut |user_value| {
                if *user_value == value {
                    *user_value = alias;
                }
            });
        }
        self.users[alias].union_with(&users);
    }

    pub fn delete_inst(&mut self, inst_id: InstId) {
        assert!(
            self.has_inst(inst_id),
            "cannot delete missing inst {inst_id:?}"
        );

        self.untrack_inst(inst_id);

        let results = std::mem::take(&mut self.inst_results[inst_id]);
        for value_id in results {
            assert!(
                self.users_num(value_id) == 0,
                "cannot delete inst {inst_id:?} with live result users"
            );
            self.delete_value(value_id);
        }

        self.live_insts[inst_id] = false;
    }

    pub fn delete_block(&mut self, block: BlockId) {
        assert!(
            self.has_block(block),
            "cannot delete missing block {block:?}"
        );
        self.live_blocks[block] = false;
    }

    fn delete_value(&mut self, value_id: ValueId) {
        assert!(
            self.has_value(value_id),
            "cannot delete missing value {value_id:?}"
        );
        assert!(
            self.users_num(value_id) == 0,
            "cannot delete value {value_id:?} with live users"
        );

        match self.values[value_id] {
            Value::Immediate { imm, .. } => {
                self.immediates.remove(&imm);
            }
            Value::Global { gv, .. } => {
                self.globals.remove(&gv);
            }
            _ => {}
        }

        self.live_values[value_id] = false;
    }

    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    pub fn num_values(&self) -> usize {
        self.values.len()
    }

    pub fn num_insts(&self) -> usize {
        self.insts.len()
    }

    pub fn rebuild_value_caches(&mut self) {
        self.immediates.clear();
        self.globals.clear();
        let value_ids: Vec<_> = self.value_ids().collect();
        for value_id in value_ids {
            match &self.values[value_id] {
                Value::Immediate { imm, .. } => {
                    self.immediates.insert(*imm, value_id);
                }
                Value::Global { gv, .. } => {
                    self.globals.insert(*gv, value_id);
                }
                _ => {}
            }
        }
    }

    pub fn effect_summary(&self, inst_id: InstId) -> InstEffectSummary {
        summarize_inst_effects(self, inst_id)
    }

    pub fn effects(&self, inst_id: InstId) -> InstEffects {
        classify_inst_effects(self, inst_id)
    }

    pub fn may_read_memory(&self, inst_id: InstId) -> bool {
        self.effect_summary(inst_id).may_read_memory()
    }

    pub fn may_write_memory(&self, inst_id: InstId) -> bool {
        self.effect_summary(inst_id).may_write_memory()
    }

    pub fn may_observe_state(&self, inst_id: InstId) -> bool {
        self.effect_summary(inst_id).may_observe_state()
    }

    pub fn may_mutate_state(&self, inst_id: InstId) -> bool {
        self.effect_summary(inst_id).may_mutate_state()
    }

    pub fn may_transfer_control(&self, inst_id: InstId) -> bool {
        self.effect_summary(inst_id).may_transfer_control()
    }

    pub fn has_value_semantics(&self, inst_id: InstId) -> bool {
        !self.effect_summary(inst_id).has_effect()
            && !self.is_branch(inst_id)
            && !self.is_phi(inst_id)
            && !self.is_terminator(inst_id)
    }

    pub fn can_drop_if_unused(&self, inst_id: InstId) -> bool {
        !self.inst_results(inst_id).is_empty()
            && !self.is_terminator(inst_id)
            && !self.effect_summary(inst_id).has_effect()
    }

    pub fn can_speculate(&self, inst_id: InstId) -> bool {
        self.has_value_semantics(inst_id)
    }

    pub fn effect_cost_class(&self, inst_id: InstId) -> EffectCostClass {
        let summary = self.effect_summary(inst_id);
        if self.is_return(inst_id) {
            EffectCostClass::Return
        } else if summary.may_transfer_control() {
            EffectCostClass::Control
        } else if summary.may_mutate_state() {
            EffectCostClass::Mutate
        } else if summary.may_observe_state() {
            EffectCostClass::Observe
        } else {
            EffectCostClass::Pure
        }
    }

    pub fn is_branch(&self, inst_id: InstId) -> bool {
        self.branch_info(inst_id).is_some()
    }

    pub fn is_phi(&self, inst_id: InstId) -> bool {
        self.cast_phi(inst_id).is_some()
    }

    pub fn is_call(&self, inst_id: InstId) -> bool {
        self.cast_call(inst_id).is_some()
    }

    pub fn is_return(&self, inst_id: InstId) -> bool {
        <&control_flow::Return as InstDowncast>::downcast(self.inst_set(), self.inst(inst_id))
            .is_some()
    }

    pub fn return_args(&self, inst: InstId) -> Option<&[ValueId]> {
        let r: &control_flow::Return = InstDowncast::downcast(self.inst_set(), self.inst(inst))?;
        Some(r.args().as_slice())
    }

    pub fn rewrite_branch_dest(&mut self, inst_id: InstId, from: BlockId, to: BlockId) {
        let inst_set = self.ctx.inst_set;
        let Some(branch) = self.branch_info(inst_id) else {
            return;
        };

        let new_inst = branch.rewrite_dest(inst_set, from, to);
        self.remove_old_users(inst_id, new_inst.as_ref());

        self.insts[inst_id] = new_inst;
    }

    pub fn remove_branch_dest(&mut self, inst_id: InstId, dest: BlockId) {
        let inst_set = self.ctx.inst_set;
        let Some(branch) = self.branch_info(inst_id) else {
            return;
        };

        let new_inst = branch.remove_dest(inst_set, dest);
        self.remove_old_users(inst_id, new_inst.as_ref());

        self.insts[inst_id] = new_inst;
    }

    fn remove_old_users(&mut self, inst_id: InstId, new: &dyn Inst) {
        let mut old_values = FxHashSet::default();
        let mut new_values = FxHashSet::default();

        self.inst(inst_id).for_each_value(&mut |value| {
            old_values.insert(value);
        });
        new.for_each_value(&mut |value| {
            new_values.insert(value);
        });

        assert!(old_values.is_superset(&new_values));

        let removed_values = old_values.difference(&new_values);
        for &removed in removed_values {
            self.users[removed].remove(&inst_id);
        }
    }
}

/// An opaque reference to [`Block`]
#[derive(Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);
entity_impl!(BlockId, "block");

impl<'a> IrWrite<FuncWriteCtx<'a>> for BlockId {
    fn write<W>(&self, w: &mut W, _ctx: &FuncWriteCtx<'a>) -> io::Result<()>
    where
        W: io::Write + ?Sized,
    {
        write!(w, "block{}", self.0)
    }
}

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is
/// managed by [`super::layout::Layout`].
#[derive(Debug, Clone, Default)]
pub struct Block {}

impl Block {
    pub fn new() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Type,
        builder::test_util::test_isa,
        inst::arith::{Add, Uaddo},
        module::ModuleCtx,
    };

    #[test]
    fn inst_results_track_order_and_result_slots() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let lhs = dfg.make_imm_value(Immediate::I32(1));
        let rhs = dfg.make_imm_value(Immediate::I32(2));
        let inst = dfg.make_inst(Uaddo::new(dfg.inst_set().has_uaddo().unwrap(), lhs, rhs));

        assert!(dfg.inst_results(inst).is_empty());

        let sum = dfg.make_value(Value::Inst {
            inst,
            result_idx: 0,
            ty: Type::I32,
        });
        let overflow = dfg.make_value(Value::Inst {
            inst,
            result_idx: 1,
            ty: Type::I1,
        });
        dfg.attach_results(inst, &[sum, overflow]);

        assert_eq!(dfg.inst_results(inst), &[sum, overflow]);
        assert_eq!(dfg.inst_result_at(inst, 0), Some(sum));
        assert_eq!(dfg.inst_result_at(inst, 1), Some(overflow));
        assert_eq!(dfg.value_inst_result(sum), Some((inst, 0)));
        assert_eq!(dfg.value_inst_result(overflow), Some((inst, 1)));
        assert_eq!(dfg.value_result_idx(sum), Some(0));
        assert_eq!(dfg.value_result_idx(overflow), Some(1));
    }

    #[test]
    #[should_panic(expected = "single_inst_result called on multi-result instruction")]
    fn single_inst_result_panics_on_multi_result() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let lhs = dfg.make_imm_value(Immediate::I32(1));
        let rhs = dfg.make_imm_value(Immediate::I32(2));
        let inst = dfg.make_inst(Uaddo::new(dfg.inst_set().has_uaddo().unwrap(), lhs, rhs));
        let sum = dfg.make_value(Value::Inst {
            inst,
            result_idx: 0,
            ty: Type::I32,
        });
        let overflow = dfg.make_value(Value::Inst {
            inst,
            result_idx: 1,
            ty: Type::I1,
        });
        dfg.attach_results(inst, &[sum, overflow]);

        let _ = dfg.single_inst_result(inst);
    }

    #[test]
    fn delete_inst_tombstones_results_and_live_iterators_skip_deleted_entities() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let live_block = dfg.make_block();
        let dead_block = dfg.make_block();
        let lhs = dfg.make_imm_value(Immediate::I32(1));
        let rhs = dfg.make_imm_value(Immediate::I32(2));
        let inst = dfg.make_inst(Uaddo::new(dfg.inst_set().has_uaddo().unwrap(), lhs, rhs));
        let sum = dfg.make_value(Value::Inst {
            inst,
            result_idx: 0,
            ty: Type::I32,
        });
        let overflow = dfg.make_value(Value::Inst {
            inst,
            result_idx: 1,
            ty: Type::I1,
        });
        dfg.attach_results(inst, &[sum, overflow]);

        dfg.delete_block(dead_block);
        dfg.delete_inst(inst);

        assert!(dfg.has_block(live_block));
        assert!(!dfg.has_block(dead_block));
        assert!(dfg.has_block_slot(dead_block));
        assert_eq!(dfg.block_ids().collect::<Vec<_>>(), vec![live_block]);

        assert!(!dfg.has_inst(inst));
        assert!(dfg.has_inst_slot(inst));
        assert!(dfg.get_inst(inst).is_none());
        assert!(dfg.try_inst_results(inst).is_none());
        assert!(dfg.inst_ids().next().is_none());

        assert!(dfg.has_value(lhs));
        assert!(dfg.has_value(rhs));
        assert!(!dfg.has_value(sum));
        assert!(!dfg.has_value(overflow));
        assert!(dfg.has_value_slot(sum));
        assert!(dfg.has_value_slot(overflow));
        assert!(dfg.get_value(sum).is_none());

        let live_values: Vec<_> = dfg.value_ids().collect();
        assert_eq!(live_values, vec![lhs, rhs]);
        let iterated_values: Vec<_> = dfg.values_iter().map(|(value, _)| value).collect();
        assert_eq!(iterated_values, live_values);
    }

    #[test]
    #[should_panic(expected = "cannot delete inst")]
    fn delete_inst_rejects_live_result_users() {
        let isa = test_isa();
        let mut dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
        let lhs = dfg.make_imm_value(Immediate::I32(1));
        let rhs = dfg.make_imm_value(Immediate::I32(2));

        let producer = dfg.make_inst(Add::new(dfg.inst_set().has_add().unwrap(), lhs, rhs));
        let produced = dfg.make_value(Value::Inst {
            inst: producer,
            result_idx: 0,
            ty: Type::I32,
        });
        dfg.attach_result(producer, produced);

        let consumer = dfg.make_inst(Add::new(dfg.inst_set().has_add().unwrap(), produced, lhs));
        let consumer_result = dfg.make_value(Value::Inst {
            inst: consumer,
            result_idx: 0,
            ty: Type::I32,
        });
        dfg.attach_result(consumer, consumer_result);

        dfg.delete_inst(producer);
    }
}
