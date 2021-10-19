//! This module contains Sonatine IR instructions definitions.

use std::collections::HashMap;

use id_arena::{Arena, Id};

use super::{Insn, InsnData, Type, Value, ValueData};

#[derive(Default, Debug, Clone)]
pub struct DataFlowGraph {
    blocks: Arena<BlockData>,
    insns: Arena<InsnData>,
    values: Arena<ValueData>,
    insn_results: HashMap<Insn, Value>,
    users: HashMap<Value, Vec<Insn>>,
}

impl DataFlowGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn make_block(&mut self, name: &str) -> Block {
        self.blocks.alloc(BlockData::new(name))
    }

    pub fn make_insn(&mut self, insn: InsnData) -> Insn {
        let insn = self.insns.alloc(insn);
        let data = &self.insns[insn];
        for arg in data.args() {
            self.users.entry(*arg).or_default().push(insn);
        }
        insn
    }

    pub fn make_result(&mut self, insn: Insn) -> Option<Value> {
        debug_assert!(!self.insn_results.contains_key(&insn));

        let ty = self.insns[insn].result_type(self)?;
        let result_data = ValueData::Insn { insn, ty };
        let result = self.values.alloc(result_data);
        self.insn_results.insert(insn, result);
        Some(result)
    }

    pub fn make_arg_value(&mut self, ty: &Type, idx: usize) -> Value {
        let value_data = ValueData::Arg {
            ty: ty.clone(),
            idx,
        };
        self.values.alloc(value_data)
    }

    pub fn insn_data(&self, insn: Insn) -> &InsnData {
        &self.insns[insn]
    }

    pub fn users(&self, value: Value) -> &[Insn] {
        self.users
            .get(&value)
            .map(|users| users.as_slice())
            .unwrap_or_default()
    }

    pub fn user_of(&self, value: Value, idx: usize) -> Insn {
        self.users(value)[idx]
    }

    pub fn block_data(&self, block: Block) -> &BlockData {
        &self.blocks[block]
    }

    pub fn block_name(&self, block: Block) -> &str {
        &self.block_data(block).name
    }

    pub fn value_def(&self, value: Value) -> ValueDef {
        match self.values[value] {
            ValueData::Insn { insn, .. } => ValueDef::Insn(insn),
            ValueData::Arg { idx, .. } => ValueDef::Arg(idx),
            ValueData::Alias { .. } => self.value_def(self.resolve_alias(value)),
        }
    }

    pub fn value_ty(&self, value: Value) -> &Type {
        match &self.values[value] {
            ValueData::Insn { ty, .. } | ValueData::Arg { ty, .. } => ty,
            ValueData::Alias { .. } => self.value_ty(self.resolve_alias(value)),
        }
    }

    pub fn append_phi_arg(&mut self, insn: Insn, arg: Value) {
        let data = &mut self.insns[insn];
        match data {
            InsnData::Phi { args } => args.push(arg),
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn remove_phi_arg(&mut self, insn: Insn, idx: usize) {
        let data = &mut self.insns[insn];
        match data {
            InsnData::Phi { args } => {
                args.remove(idx);
            }
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn insn_args(&self, insn: Insn) -> &[Value] {
        self.insn_data(insn).args()
    }

    pub fn insn_arg(&self, insn: Insn, idx: usize) -> Value {
        self.insn_args(insn)[idx]
    }

    pub fn replace_insn_arg(&mut self, insn: Insn, new_arg: Value, idx: usize) -> Value {
        let data = &mut self.insns[insn];
        let args = data.args_mut();
        std::mem::replace(&mut args[idx], new_arg)
    }

    pub fn insn_result(&self, insn: Insn) -> Option<Value> {
        self.insn_results.get(&insn).copied()
    }

    pub fn make_alias(&mut self, from: Value, to: Value) {
        self.values[from] = ValueData::Alias {
            value: self.resolve_alias(to),
        };
    }

    pub fn resolve_alias(&self, mut value: Value) -> Value {
        let value_len = self.values.len();
        let alias_depth = 0;

        while let ValueData::Alias { value: resolved } = self.values[value] {
            if alias_depth >= value_len {
                panic!("alias cycle detected");
            }
            value = resolved;
        }

        value
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
pub type Block = Id<BlockData>;

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
#[derive(Debug, Clone)]
pub struct BlockData {
    pub name: String,
}

impl BlockData {
    pub fn new(name: &str) -> Self {
        BlockData {
            name: name.to_string(),
        }
    }
}
