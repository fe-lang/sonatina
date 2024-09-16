//! This module contains Sonatine IR data flow graph.
use std::collections::BTreeSet;

use cranelift_entity::{entity_impl, packed_option::PackedOption, PrimaryMap, SecondaryMap};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::{global_variable::ConstantValue, module::ModuleCtx, GlobalVariable};

use super::{BranchInfo, Immediate, Insn, InsnData, Type, Value, ValueId};

#[derive(Debug, Clone)]
pub struct DataFlowGraph {
    pub ctx: ModuleCtx,
    #[doc(hidden)]
    pub blocks: PrimaryMap<BlockId, Block>,
    #[doc(hidden)]
    pub values: PrimaryMap<ValueId, Value>,
    insns: PrimaryMap<Insn, InsnData>,
    insn_results: SecondaryMap<Insn, PackedOption<ValueId>>,
    #[doc(hidden)]
    pub immediates: FxHashMap<Immediate, ValueId>,
    users: SecondaryMap<ValueId, BTreeSet<Insn>>,
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

    pub fn make_block(&mut self) -> BlockId {
        self.blocks.push(Block::new())
    }

    pub fn make_value(&mut self, value: Value) -> ValueId {
        self.values.push(value)
    }

    pub fn make_insn(&mut self, insn: InsnData) -> Insn {
        let insn = self.insns.push(insn);
        self.attach_user(insn);
        insn
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

    pub fn replace_insn(&mut self, insn: Insn, insn_data: InsnData) {
        for i in 0..self.insn_args_num(insn) {
            let arg = self.insn_arg(insn, i);
            self.remove_user(arg, insn);
        }
        self.insns[insn] = insn_data;
        self.attach_user(insn);
    }

    pub fn change_to_alias(&mut self, value: ValueId, alias: ValueId) {
        let mut users = std::mem::take(&mut self.users[value]);
        for insn in &users {
            for arg in self.insns[*insn].args_mut() {
                if *arg == value {
                    *arg = alias;
                }
            }
        }
        self.users[alias].append(&mut users);
    }

    pub fn make_result(&mut self, insn: Insn) -> Option<Value> {
        let ty = self.insns[insn].result_type(self)?;
        Some(Value::Insn { insn, ty })
    }

    pub fn attach_result(&mut self, insn: Insn, value: ValueId) {
        debug_assert!(self.insn_results[insn].is_none());
        self.insn_results[insn] = value.into();
    }

    pub fn make_arg_value(&mut self, ty: Type, idx: usize) -> Value {
        Value::Arg { ty, idx }
    }

    pub fn insn_data(&self, insn: Insn) -> &InsnData {
        &self.insns[insn]
    }

    pub fn value_data(&self, value: ValueId) -> &Value {
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

    pub fn users(&self, value: ValueId) -> impl Iterator<Item = &Insn> {
        self.users[value].iter()
    }

    pub fn users_num(&self, value: ValueId) -> usize {
        self.users[value].len()
    }

    pub fn remove_user(&mut self, value: ValueId, user: Insn) {
        self.users[value].remove(&user);
    }

    pub fn user(&self, value: ValueId, idx: usize) -> Insn {
        *self.users(value).nth(idx).unwrap()
    }

    pub fn block_data(&self, block: BlockId) -> &Block {
        &self.blocks[block]
    }

    pub fn value_insn(&self, value: ValueId) -> Option<Insn> {
        match self.value_data(value) {
            Value::Insn { insn, .. } => Some(*insn),
            _ => None,
        }
    }

    pub fn value_ty(&self, value: ValueId) -> Type {
        match &self.values[value] {
            Value::Insn { ty, .. }
            | Value::Arg { ty, .. }
            | Value::Immediate { ty, .. }
            | Value::Global { ty, .. } => *ty,
        }
    }

    pub fn insn_result_ty(&self, insn: Insn) -> Option<Type> {
        self.insn_result(insn).map(|value| self.value_ty(value))
    }

    pub fn value_imm(&self, value: ValueId) -> Option<Immediate> {
        match self.value_data(value) {
            Value::Immediate { imm, .. } => Some(*imm),
            Value::Global { gv, .. } => self.ctx.with_gv_store(|s| {
                if !s.is_const(*gv) {
                    return None;
                }
                match s.init_data(*gv)? {
                    ConstantValue::Immediate(data) => Some(*data),
                    _ => None,
                }
            }),
            _ => None,
        }
    }

    pub fn value_gv(&self, value: ValueId) -> Option<GlobalVariable> {
        match self.value_data(value) {
            Value::Global { gv, .. } => Some(*gv),
            _ => None,
        }
    }

    pub fn phi_blocks(&self, insn: Insn) -> &[BlockId] {
        self.insns[insn].phi_blocks()
    }

    pub fn phi_blocks_mut(&mut self, insn: Insn) -> &mut [BlockId] {
        self.insns[insn].phi_blocks_mut()
    }

    pub fn append_phi_arg(&mut self, insn: Insn, value: ValueId, block: BlockId) {
        self.insns[insn].append_phi_arg(value, block);
        self.attach_user(insn);
    }

    /// Remove phi arg that flow through the `from`.
    ///
    /// # Panics
    /// If `insn` is not a phi insn or there is no phi argument from the block, then the function panics.
    pub fn remove_phi_arg(&mut self, insn: Insn, from: BlockId) -> ValueId {
        let removed = self.insns[insn].remove_phi_arg(from);
        self.remove_user(removed, insn);
        removed
    }

    pub fn insn_args(&self, insn: Insn) -> &[ValueId] {
        self.insn_data(insn).args()
    }

    pub fn insn_args_num(&self, insn: Insn) -> usize {
        self.insn_args(insn).len()
    }

    pub fn insn_arg(&self, insn: Insn, idx: usize) -> ValueId {
        self.insn_args(insn)[idx]
    }

    pub fn replace_insn_arg(&mut self, insn: Insn, new_arg: ValueId, idx: usize) -> ValueId {
        let data = &mut self.insns[insn];
        let args = data.args_mut();
        self.users[new_arg].insert(insn);
        let old_arg = std::mem::replace(&mut args[idx], new_arg);
        if args.iter().all(|arg| *arg != old_arg) {
            self.remove_user(old_arg, insn);
        }

        old_arg
    }

    pub fn insn_result(&self, insn: Insn) -> Option<ValueId> {
        self.insn_results[insn].expand()
    }

    pub fn analyze_branch(&self, insn: Insn) -> BranchInfo {
        self.insns[insn].analyze_branch()
    }

    pub fn remove_branch_dest(&mut self, insn: Insn, dest: BlockId) {
        let this = &mut self.insns[insn];
        match this {
            InsnData::Jump { .. } => panic!("can't remove destination from `Jump` insn"),

            InsnData::Branch { dests, args } => {
                let remain = if dests[0] == dest {
                    dests[1]
                } else if dests[1] == dest {
                    dests[0]
                } else {
                    panic!("no dests found in the branch destination")
                };
                self.users[args[0]].remove(&insn);
                *this = InsnData::jump(remain);
            }

            InsnData::BrTable {
                default,
                table,
                args,
            } => {
                if Some(dest) == *default {
                    *default = None;
                } else if let Some((lhs, rest)) = args.split_first() {
                    type V<T> = SmallVec<[T; 8]>;
                    let (keep, drop): (V<_>, V<_>) = table
                        .iter()
                        .copied()
                        .zip(rest.iter().copied())
                        .partition(|(b, _)| *b != dest);
                    let (b, mut a): (V<_>, V<_>) = keep.into_iter().unzip();
                    a.insert(0, *lhs);
                    *args = a;
                    *table = b;

                    for (_, val) in drop {
                        self.users[val].remove(&insn);
                    }
                }

                let branch_info = this.analyze_branch();
                if branch_info.dests_num() == 1 {
                    for val in this.args() {
                        self.users[*val].remove(&insn);
                    }
                    *this = InsnData::jump(branch_info.iter_dests().next().unwrap());
                }
            }

            _ => panic!("not a branch"),
        }
    }

    pub fn rewrite_branch_dest(&mut self, insn: Insn, from: BlockId, to: BlockId) {
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

    /// Returns `true` if `value` is an immediate.
    pub fn is_imm(&self, value: ValueId) -> bool {
        self.value_imm(value).is_some()
    }

    /// Returns `true` if `value` is a function argument.
    pub fn is_arg(&self, value: ValueId) -> bool {
        matches!(self.value_data(value), Value::Arg { .. })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ValueDef {
    Insn(Insn),
    Arg(usize),
}

/// An opaque reference to [`Block`]
#[derive(Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);
entity_impl!(BlockId, "block");

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
