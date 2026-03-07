//! This module contains Sonatine IR data flow graph.
use std::{collections::BTreeSet, io};

use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use dyn_clone::clone_box;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use super::{Immediate, Type, Value, ValueId};
use crate::{
    GlobalVariableRef, Inst, InstDowncast, InstDowncastMut, InstSetBase,
    inst::{
        InstId, SideEffect,
        control_flow::{self, BranchInfo, CallInfo, Jump, Phi},
    },
    ir_writer::{FuncWriteCtx, IrWrite},
    module::{FuncAttrs, ModuleCtx},
};

pub struct DataFlowGraph {
    pub ctx: ModuleCtx,
    #[doc(hidden)]
    pub blocks: PrimaryMap<BlockId, Block>,
    #[doc(hidden)]
    pub values: PrimaryMap<ValueId, Value>,
    #[doc(hidden)]
    pub insts: PrimaryMap<InstId, Box<dyn Inst>>,
    inst_results: SecondaryMap<InstId, SmallVec<[ValueId; 1]>>,
    #[doc(hidden)]
    pub immediates: FxHashMap<Immediate, ValueId>,
    #[doc(hidden)]
    pub globals: FxHashMap<GlobalVariableRef, ValueId>,
    users: SecondaryMap<ValueId, BTreeSet<InstId>>,
}

impl DataFlowGraph {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
            ctx,
            blocks: PrimaryMap::default(),
            values: PrimaryMap::default(),
            insts: PrimaryMap::default(),
            inst_results: SecondaryMap::default(),
            immediates: FxHashMap::default(),
            globals: FxHashMap::default(),
            users: SecondaryMap::default(),
        }
    }

    pub fn make_block(&mut self) -> BlockId {
        self.blocks.push(Block::new())
    }

    pub fn make_value(&mut self, value: Value) -> ValueId {
        self.values.push(value)
    }

    pub fn make_inst<I: Inst>(&mut self, inst: I) -> InstId {
        self.make_inst_dyn(Box::new(inst))
    }

    pub fn make_inst_dyn(&mut self, inst: Box<dyn Inst>) -> InstId {
        let inst_id = self.insts.push(inst);
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
        debug_assert!(
            self.inst_results[inst_id].is_empty(),
            "results for {inst_id:?} are already attached"
        );
        for (result_idx, value_id) in values.iter().copied().enumerate() {
            debug_assert!(
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
        debug_assert!(
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
        (block.as_u32() as usize) < self.blocks.len()
    }

    pub fn has_value(&self, value: ValueId) -> bool {
        (value.as_u32() as usize) < self.values.len()
    }

    pub fn has_inst(&self, inst: InstId) -> bool {
        (inst.as_u32() as usize) < self.insts.len()
    }

    pub fn get_inst(&self, inst_id: InstId) -> Option<&dyn Inst> {
        self.insts.get(inst_id).map(|inst| inst.as_ref())
    }

    pub fn inst(&self, inst_id: InstId) -> &dyn Inst {
        self.insts[inst_id].as_ref()
    }

    pub fn inst_mut(&mut self, inst_id: InstId) -> &mut dyn Inst {
        self.insts[inst_id].as_mut()
    }

    pub fn get_inst_mut(&mut self, inst_id: InstId) -> Option<&mut dyn Inst> {
        self.insts.get_mut(inst_id).map(|inst| inst.as_mut())
    }

    pub fn get_value(&self, value_id: ValueId) -> Option<&Value> {
        self.values.get(value_id)
    }

    pub fn value(&self, value_id: ValueId) -> &Value {
        &self.values[value_id]
    }

    pub fn value_ty(&self, value_id: ValueId) -> Type {
        match &self.values[value_id] {
            Value::Inst { ty, .. }
            | Value::Arg { ty, .. }
            | Value::Immediate { ty, .. }
            | Value::Global { ty, .. }
            | Value::Undef { ty } => *ty,
        }
    }

    pub fn value_is_imm(&self, value_id: ValueId) -> bool {
        matches!(self.values[value_id], Value::Immediate { .. })
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

    pub fn users_set(&self, value_id: ValueId) -> Option<&BTreeSet<InstId>> {
        self.users.get(value_id)
    }

    pub fn inst_results(&self, inst_id: InstId) -> &[ValueId] {
        self.inst_results[inst_id].as_slice()
    }

    pub fn try_inst_results(&self, inst_id: InstId) -> Option<&[ValueId]> {
        self.inst_results.get(inst_id).map(SmallVec::as_slice)
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
        let mut users = std::mem::take(&mut self.users[value]);
        for inst in &users {
            self.insts[*inst].for_each_value_mut(&mut |user_value| {
                if *user_value == value {
                    *user_value = alias;
                }
            });
        }
        self.users[alias].append(&mut users);
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
        for (value_id, value) in self.values.iter() {
            match value {
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

    pub fn side_effect(&self, inst_id: InstId) -> SideEffect {
        if let Some(call_info) = self.call_info(inst_id) {
            let callee = call_info.callee();
            let attrs = self.ctx.func_attrs(callee);

            if attrs.contains(FuncAttrs::NORETURN) || !attrs.contains(FuncAttrs::WILLRETURN) {
                return SideEffect::Control;
            }

            if attrs.contains(FuncAttrs::MEM_WRITE) {
                SideEffect::Write
            } else if attrs.contains(FuncAttrs::MEM_READ) {
                SideEffect::Read
            } else {
                SideEffect::None
            }
        } else {
            self.inst(inst_id).side_effect()
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

    pub fn as_return(&self, inst: InstId) -> Option<ValueId> {
        let r: &control_flow::Return = InstDowncast::downcast(self.inst_set(), self.inst(inst))?;
        *r.arg()
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
    use crate::{Type, builder::test_util::test_isa, inst::arith::Uaddo, module::ModuleCtx};

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
}
