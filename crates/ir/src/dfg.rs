//! This module contains Sonatine IR data flow graph.
use std::{collections::BTreeSet, fmt};

use cranelift_entity::{entity_impl, packed_option::PackedOption, PrimaryMap, SecondaryMap};
use rustc_hash::FxHashMap;

use crate::{
    inst::{
        control_flow::{self, BranchInfo},
        InstId,
    },
    ir_writer::DisplayWithFunc,
    module::ModuleCtx,
    Function, GlobalVariable, Inst, InstDowncast, InstDowncastMut, InstSetBase,
};

use super::{Immediate, Type, Value, ValueId};

pub struct DataFlowGraph {
    pub ctx: ModuleCtx,
    #[doc(hidden)]
    pub blocks: PrimaryMap<BlockId, Block>,
    #[doc(hidden)]
    pub values: PrimaryMap<ValueId, Value>,
    insts: PrimaryMap<InstId, Box<dyn Inst>>,
    inst_results: SecondaryMap<InstId, PackedOption<ValueId>>,
    #[doc(hidden)]
    pub immediates: FxHashMap<Immediate, ValueId>,
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
        let inst_id = self.insts.push(Box::new(inst));
        self.attach_user(inst_id);
        inst_id
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

    pub fn make_global_value(&mut self, gv: GlobalVariable) -> ValueId {
        let gv_ty = self.ctx.with_gv_store(|s| s.ty(gv));
        let ty = self.ctx.with_ty_store_mut(|s| s.make_ptr(gv_ty));
        let value_data = Value::Global { gv, ty };
        self.make_value(value_data)
    }

    pub fn replace_inst(&mut self, inst_id: InstId, new: Box<dyn Inst>) {
        let slot = &mut self.insts[inst_id];
        let old = &mut std::mem::replace(slot, new);

        // Remove the arguments of the old inst from the user set.
        old.visit_values(&mut |value| {
            self.remove_user(value, inst_id);
        });

        // Attach new inst.
        self.attach_user(inst_id);
    }

    pub fn attach_result(&mut self, inst_id: InstId, value_id: ValueId) {
        debug_assert!(self.inst_results[inst_id].is_none());
        self.inst_results[inst_id] = value_id.into();
    }

    pub fn make_arg_value(&mut self, ty: Type, idx: usize) -> Value {
        Value::Arg { ty, idx }
    }

    pub fn inst(&self, inst_id: InstId) -> &dyn Inst {
        self.insts[inst_id].as_ref()
    }

    pub fn inst_mut(&mut self, inst_id: InstId) -> &mut dyn Inst {
        self.insts[inst_id].as_mut()
    }

    pub fn value(&self, value_id: ValueId) -> &Value {
        &self.values[value_id]
    }

    pub fn value_ty(&self, value_id: ValueId) -> Type {
        match &self.values[value_id] {
            Value::Inst { ty, .. }
            | Value::Arg { ty, .. }
            | Value::Immediate { ty, .. }
            | Value::Global { ty, .. } => *ty,
        }
    }

    pub fn attach_user(&mut self, inst_id: InstId) {
        let inst = &self.insts[inst_id];
        inst.visit_values(&mut |value| {
            self.users[value].insert(inst_id);
        })
    }

    pub fn untrack_inst(&mut self, inst_id: InstId) {
        let inst = &self.insts[inst_id];
        inst.visit_values(&mut |value| {
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

    pub fn inst_result(&self, inst_id: InstId) -> Option<ValueId> {
        self.inst_results[inst_id].expand()
    }

    pub fn branch_info(&self, inst: InstId) -> Option<BranchInfo> {
        let inst = self.inst(inst);
        BranchInfo::downcast(self.ctx.inst_set, inst)
    }

    pub fn is_terminator(&self, inst: InstId) -> bool {
        self.inst(inst).is_terminator()
    }

    pub fn is_exit(&self, inst: InstId) -> bool {
        self.is_terminator(inst) && self.branch_info(inst).is_none()
    }

    pub fn append_phi_arg(&mut self, inst_id: InstId, value: ValueId, block: BlockId) {
        let Some(phi) = self.phi_mut(inst_id) else {
            return;
        };
        phi.append_phi_arg(value, block);
        self.attach_user(inst_id);
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.ctx.inst_set
    }

    pub fn phi(&self, inst_id: InstId) -> Option<&control_flow::Phi> {
        let inst = self.inst(inst_id);
        let is = self.inst_set();
        InstDowncast::downcast(is, inst)
    }

    pub fn phi_mut(&mut self, inst_id: InstId) -> Option<&mut control_flow::Phi> {
        let is = self.inst_set();
        let inst = self.inst_mut(inst_id);
        InstDowncastMut::downcast_mut(is, inst)
    }

    pub fn change_to_alias(&mut self, value: ValueId, alias: ValueId) {
        let mut users = std::mem::take(&mut self.users[value]);
        for inst in &users {
            self.insts[*inst].visit_values_mut(&mut |user_value| {
                if *user_value == value {
                    *user_value = alias;
                }
            });
        }
        self.users[alias].append(&mut users);
    }
}

/// An opaque reference to [`Block`]
#[derive(Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);
entity_impl!(BlockId, "block");

impl DisplayWithFunc for BlockId {
    fn fmt(&self, _func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "block{}", self.0)
    }
}

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
#[derive(Debug, Clone, Default)]
pub struct Block {}

impl Block {
    pub fn new() -> Self {
        Self::default()
    }
}
