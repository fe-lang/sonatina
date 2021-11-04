//! This module contains Sonatine IR instructions definitions.

use std::collections::BTreeSet;

use cranelift_entity::{packed_option::PackedOption, PrimaryMap, SecondaryMap};

use super::{Insn, InsnData, Type, Value, ValueData};

#[derive(Default, Debug, Clone)]
pub struct DataFlowGraph {
    #[doc(hidden)]
    pub blocks: PrimaryMap<Block, BlockData>,
    #[doc(hidden)]
    pub values: PrimaryMap<Value, ValueData>,
    insns: PrimaryMap<Insn, InsnData>,
    insn_results: SecondaryMap<Insn, PackedOption<Value>>,
    users: SecondaryMap<Value, BTreeSet<Insn>>,
}

impl DataFlowGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn make_block(&mut self) -> Block {
        self.blocks.push(BlockData::new())
    }

    pub fn make_value(&mut self, value: ValueData) -> Value {
        self.values.push(value)
    }

    pub fn make_insn(&mut self, insn: InsnData) -> Insn {
        let insn = self.insns.push(insn);
        let data = &self.insns[insn];
        for arg in data.args() {
            self.users[*arg].insert(insn);
        }
        insn
    }

    pub fn replace_value(&mut self, old_value: Value, new_value: Value) {
        let old_value_users = std::mem::take(&mut self.users[old_value]);

        for insn in old_value_users.into_iter() {
            for idx in 0..self.insn_args_num(insn) {
                if self.insn_arg(insn, idx) == old_value {
                    self.replace_insn_arg(insn, new_value, idx);
                }
            }
            self.users[new_value].insert(insn);
        }
    }

    pub fn make_result(&mut self, insn: Insn) -> Option<ValueData> {
        let ty = self.insns[insn].result_type(self)?;
        Some(ValueData::Insn { insn, ty })
    }

    pub fn attach_result(&mut self, insn: Insn, value: Value) {
        debug_assert!(self.insn_results[insn].is_none());
        self.insn_results[insn] = value.into();
    }

    pub fn make_arg_value(&mut self, ty: &Type, idx: usize) -> Value {
        let value_data = ValueData::Arg {
            ty: ty.clone(),
            idx,
        };
        self.values.push(value_data)
    }

    pub fn insn_data(&self, insn: Insn) -> &InsnData {
        &self.insns[insn]
    }

    pub fn users(&self, value: Value) -> impl Iterator<Item = &Insn> {
        self.users[value].iter()
    }

    pub fn users_num(&self, value: Value) -> usize {
        self.users[value].len()
    }

    pub fn remove_user(&mut self, value: Value, user: Insn) {
        self.users[value].remove(&user);
    }

    pub fn user(&self, value: Value, idx: usize) -> Insn {
        *self.users(value).nth(idx).unwrap()
    }

    pub fn block_data(&self, block: Block) -> &BlockData {
        &self.blocks[block]
    }

    pub fn value_def(&self, value: Value) -> ValueDef {
        match self.values[value] {
            ValueData::Insn { insn, .. } => ValueDef::Insn(insn),
            ValueData::Arg { idx, .. } => ValueDef::Arg(idx),
        }
    }

    pub fn value_insn(&self, value: Value) -> Option<Insn> {
        match self.value_def(value) {
            ValueDef::Insn(insn) => Some(insn),
            _ => None,
        }
    }

    pub fn value_ty(&self, value: Value) -> &Type {
        match &self.values[value] {
            ValueData::Insn { ty, .. } | ValueData::Arg { ty, .. } => ty,
        }
    }

    pub fn append_phi_arg(&mut self, insn: Insn, value: Value, block: Block) {
        let data = &mut self.insns[insn];
        match data {
            InsnData::Phi { values, blocks, .. } => {
                values.push(value);
                blocks.push(block);
            }
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn phi_blocks(&self, insn: Insn) -> &[Block] {
        let data = &self.insns[insn];
        match data {
            InsnData::Phi { blocks, .. } => blocks,
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn phi_blocks_mut(&mut self, insn: Insn) -> &mut [Block] {
        let data = &mut self.insns[insn];
        match data {
            InsnData::Phi { blocks, .. } => blocks,
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn insn_args(&self, insn: Insn) -> &[Value] {
        self.insn_data(insn).args()
    }

    pub fn insn_args_num(&self, insn: Insn) -> usize {
        self.insn_args(insn).len()
    }

    pub fn insn_arg(&self, insn: Insn, idx: usize) -> Value {
        self.insn_args(insn)[idx]
    }

    pub fn replace_insn_arg(&mut self, insn: Insn, new_arg: Value, idx: usize) -> Value {
        let data = &mut self.insns[insn];
        let args = data.args_mut();
        self.users[new_arg].insert(insn);
        let old_arg = std::mem::replace(&mut args[idx], new_arg);
        if args.iter().all(|arg| *arg != old_arg) {
            self.remove_user(old_arg, insn);
        }

        old_arg
    }

    pub fn insn_result(&self, insn: Insn) -> Option<Value> {
        self.insn_results[insn].expand()
    }

    pub fn branch_dests(&self, insn: Insn) -> &[Block] {
        self.insns[insn].branch_dests()
    }

    pub fn branch_dests_mut(&mut self, insn: Insn) -> &mut [Block] {
        self.insns[insn].branch_dests_mut()
    }

    pub fn is_phi(&self, insn: Insn) -> bool {
        matches!(self.insn_data(insn), InsnData::Phi { .. })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ValueDef {
    Insn(Insn),
    Arg(usize),
}

/// An opaque reference to [`BlockData`]
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct Block(pub u32);
cranelift_entity::entity_impl!(Block);

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
#[derive(Debug, Clone, Default)]
pub struct BlockData {}

impl BlockData {
    pub fn new() -> Self {
        Self::default()
    }
}
