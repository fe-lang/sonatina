//! This module contains Sonatine IR data flow graph.

use cranelift_entity::{packed_option::PackedOption, PrimaryMap, SecondaryMap};
use fxhash::FxHashMap;
use std::collections::BTreeSet;

use crate::{global_variable::ConstantValue, module::ModuleCtx};

use super::{BranchInfo, Immediate, Insn, InsnData, Type, Value, ValueData};

#[derive(Debug, Clone)]
pub struct DataFlowGraph {
    pub ctx: ModuleCtx,
    #[doc(hidden)]
    pub blocks: PrimaryMap<Block, BlockData>,
    #[doc(hidden)]
    pub values: PrimaryMap<Value, ValueData>,
    insns: PrimaryMap<Insn, InsnData>,
    insn_results: SecondaryMap<Insn, PackedOption<Value>>,
    #[doc(hidden)]
    pub immediates: FxHashMap<Immediate, Value>,
    users: SecondaryMap<Value, BTreeSet<Insn>>,
}

impl DataFlowGraph {
    pub fn new(ctx: ModuleCtx) -> Self {
        Self {
            ctx,
            blocks: PrimaryMap::default(),
            values: PrimaryMap::default(),
            insns: PrimaryMap::default(),
            insn_results: SecondaryMap::default(),
            immediates: FxHashMap::default(),
            users: SecondaryMap::default(),
        }
    }

    pub fn make_block(&mut self) -> Block {
        self.blocks.push(BlockData::new())
    }

    pub fn make_value(&mut self, value: ValueData) -> Value {
        self.values.push(value)
    }

    pub fn make_insn(&mut self, insn: InsnData) -> Insn {
        let insn = self.insns.push(insn);
        self.attach_user(insn);
        insn
    }

    pub fn make_imm_value<Imm>(&mut self, imm: Imm) -> Value
    where
        Imm: Into<Immediate>,
    {
        let imm: Immediate = imm.into();
        if let Some(&value) = self.immediates.get(&imm) {
            return value;
        }

        let ty = imm.ty();
        let value_data = ValueData::Immediate { imm, ty };
        let value = self.make_value(value_data);
        self.immediates.insert(imm, value);
        value
    }

    pub fn replace_insn(&mut self, insn: Insn, insn_data: InsnData) {
        for i in 0..self.insn_args_num(insn) {
            let arg = self.insn_arg(insn, i);
            self.remove_user(arg, insn);
        }
        self.insns[insn] = insn_data;
        self.attach_user(insn);
    }

    pub fn change_to_alias(&mut self, value: Value, alias: Value) {
        self.values[value] = ValueData::Alias {
            alias: self.resolve_alias(alias),
        }
    }

    pub fn resolve_alias(&self, mut value: Value) -> Value {
        for _ in 0..self.values.len() {
            match self.values[value] {
                ValueData::Insn { .. }
                | ValueData::Arg { .. }
                | ValueData::Immediate { .. }
                | ValueData::Global { .. } => return value,
                ValueData::Alias { alias } => value = alias,
            }
        }

        panic!("alias loop detected");
    }

    pub fn make_result(&mut self, insn: Insn) -> Option<ValueData> {
        let ty = self.insns[insn].result_type(self)?;
        Some(ValueData::Insn { insn, ty })
    }

    pub fn attach_result(&mut self, insn: Insn, value: Value) {
        debug_assert!(self.insn_results[insn].is_none());
        self.insn_results[insn] = value.into();
    }

    pub fn make_arg_value(&mut self, ty: Type, idx: usize) -> ValueData {
        ValueData::Arg { ty, idx }
    }

    pub fn insn_data(&self, insn: Insn) -> &InsnData {
        &self.insns[insn]
    }

    pub fn value_data(&self, value: Value) -> &ValueData {
        &self.values[value]
    }

    pub fn has_side_effect(&self, insn: Insn) -> bool {
        self.insns[insn].has_side_effect()
    }

    pub fn may_trap(&self, insn: Insn) -> bool {
        self.insns[insn].may_trap()
    }

    pub fn attach_user(&mut self, insn: Insn) {
        let data = &self.insns[insn];
        for arg in data.args() {
            self.users[*arg].insert(insn);
        }
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

    pub fn value_insn(&self, value: Value) -> Option<Insn> {
        let value = self.resolve_alias(value);
        match self.value_data(value) {
            ValueData::Insn { insn, .. } => Some(*insn),
            _ => None,
        }
    }

    pub fn value_ty(&self, value: Value) -> Type {
        let value = self.resolve_alias(value);
        match &self.values[value] {
            ValueData::Insn { ty, .. }
            | ValueData::Arg { ty, .. }
            | ValueData::Immediate { ty, .. }
            | ValueData::Global { ty, .. } => *ty,
            ValueData::Alias { .. } => unreachable!(),
        }
    }

    pub fn insn_result_ty(&self, insn: Insn) -> Option<Type> {
        self.insn_result(insn).map(|value| self.value_ty(value))
    }

    pub fn value_imm(&self, value: Value) -> Option<Immediate> {
        let value = self.resolve_alias(value);
        match self.value_data(value) {
            ValueData::Immediate { imm, .. } => Some(*imm),
            ValueData::Global { gv, .. } => self.ctx.with_gv_store(|s| {
                if !s.is_const(*gv) {
                    return None;
                }
                match s.init_data(*gv)? {
                    ConstantValue::Immediate { data, .. } => Some(*data),
                    _ => None,
                }
            }),
            _ => None,
        }
    }

    pub fn phi_blocks(&self, insn: Insn) -> &[Block] {
        self.insns[insn].phi_blocks()
    }

    pub fn phi_blocks_mut(&mut self, insn: Insn) -> &mut [Block] {
        self.insns[insn].phi_blocks_mut()
    }

    pub fn append_phi_arg(&mut self, insn: Insn, value: Value, block: Block) {
        self.insns[insn].append_phi_arg(value, block);
        self.attach_user(insn);
    }

    /// Remove phi arg that flow through the `from`.
    ///
    /// # Panics
    /// If `insn` is not a phi insn or there is no phi argument from the block, then the function panics.
    pub fn remove_phi_arg(&mut self, insn: Insn, from: Block) -> Value {
        let removed = self.insns[insn].remove_phi_arg(from);
        self.remove_user(removed, insn);
        removed
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

    pub fn analyze_branch(&self, insn: Insn) -> BranchInfo {
        self.insns[insn].analyze_branch()
    }

    pub fn remove_branch_dest(&mut self, insn: Insn, dest: Block) {
        self.insns[insn].remove_branch_dest(dest)
    }

    pub fn rewrite_branch_dest(&mut self, insn: Insn, from: Block, to: Block) {
        self.insns[insn].rewrite_branch_dest(from, to)
    }

    pub fn is_phi(&self, insn: Insn) -> bool {
        self.insns[insn].is_phi()
    }

    pub fn is_return(&self, insn: Insn) -> bool {
        self.insns[insn].is_return()
    }

    pub fn is_branch(&self, insn: Insn) -> bool {
        self.insns[insn].is_branch()
    }

    pub fn is_same_value(&self, v0: Value, v1: Value) -> bool {
        self.resolve_alias(v0) == self.resolve_alias(v1)
    }

    /// Returns `true` if `value` is an immediate.
    pub fn is_imm(&self, value: Value) -> bool {
        self.value_imm(value).is_some()
    }

    /// Returns `true` if `value` is a function argument.
    pub fn is_arg(&self, value: Value) -> bool {
        let value = self.resolve_alias(value);
        matches!(self.value_data(value), ValueData::Arg { .. })
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
