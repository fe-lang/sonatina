//! This module contains Sonatine IR data flow graph.
use std::collections::BTreeSet;

use cranelift_entity::{packed_option::PackedOption, PrimaryMap, SecondaryMap};
use rustc_hash::FxHashMap;

use crate::{inst::InstId, module::ModuleCtx, Block, BlockId, GlobalVariable, Inst};

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

    pub fn make_inst(&mut self, inst: Box<dyn Inst>) -> InstId {
        let inst_id = self.insts.push(inst);
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

    pub fn value(&self, value_id: ValueId) -> &Value {
        &self.values[value_id]
    }

    pub fn attach_user(&mut self, inst_id: InstId) {
        let inst = &self.insts[inst_id];
        inst.visit_values(&mut |value| {
            self.users[value].insert(inst_id);
        })
    }

    /// Returns the all instructions that use the `value_id`.
    pub fn users(&self, value_id: ValueId) -> impl Iterator<Item = &InstId> {
        self.users[value_id].iter()
    }

    /// Returns the number of instructions that use the `value_id`.
    pub fn users_num(&self, value: ValueId) -> usize {
        self.users[value].len()
    }

    pub fn remove_user(&mut self, value: ValueId, user: InstId) {
        self.users[value].remove(&user);
    }
}
