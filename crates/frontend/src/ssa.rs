//! SSA construction algorighm here is based on [`Simple and Efficient Construction of Static
//! Single Assignment Form`](https://link.springer.com/chapter/10.1007/978-3-642-37051-9_6).
use std::collections::{HashMap, HashSet};

use id_arena::{Arena, Id};

use sonatina_codegen::ir::{
    function::{CursorLocation, FunctionCursor},
    Function, Insn, InsnData,
};

use super::{Block, Type, Value};

pub type Variable = Id<VariableData>;

pub struct VariableData {
    ty: Type,
}

#[derive(Default)]
pub(super) struct SsaBuilder {
    /// Records all predecessors of a block.
    preds: HashMap<Block, Vec<Block>>,

    /// Records sealed blocks.
    sealed: HashSet<Block>,

    /// Records defined variables in an block.
    defs: HashMap<(Block, Variable), Value>,

    vars: Arena<VariableData>,

    /// Records phis in an unsealed block.
    incomplete_phis: HashMap<Block, Vec<(Variable, Insn)>>,

    /// Records trivial phis.
    trivial_phis: HashSet<Insn>,
}

impl SsaBuilder {
    pub(super) fn declare_var(&mut self, ty: Type) -> Variable {
        self.vars.alloc(VariableData { ty })
    }

    pub(super) fn def_var(&mut self, var: Variable, value: Value, block: Block) {
        self.defs.insert((block, var), value);
    }

    pub(super) fn use_var(&mut self, func: &mut Function, var: Variable, block: Block) -> Value {
        if let Some(value) = self.defs.get(&(block, var)) {
            *value
        } else {
            self.use_var_recursive(func, var, block)
        }
    }

    pub(super) fn var_ty(&mut self, var: Variable) -> &Type {
        &self.vars[var].ty
    }

    pub(super) fn append_pred(&mut self, block: Block, pred: Block) {
        self.preds.entry(block).or_default().push(pred);
    }

    pub(super) fn seal_block(&mut self, func: &mut Function, block: Block) {
        for (var, phi) in self.incomplete_phis.remove(&block).unwrap_or_default() {
            self.add_phi_args(func, var, phi);
        }

        self.sealed.insert(block);
    }

    pub(super) fn is_sealed(&mut self, block: Block) -> bool {
        self.sealed.contains(&block)
    }

    fn use_var_recursive(&mut self, func: &mut Function, var: Variable, block: Block) -> Value {
        if !self.is_sealed(block) {
            let (insn, value) = self.prepend_phi(func, block);
            self.incomplete_phis
                .entry(block)
                .or_default()
                .push((var, insn));
            self.def_var(var, value, block);
            return value;
        }

        match self.preds.get(&block).map(|preds| preds.as_slice()) {
            Some(&[pred]) => self.use_var(func, var, pred),
            _ => {
                let (phi_insn, phi_value) = self.prepend_phi(func, block);
                // Break potential cycles by defining operandless phi.
                self.def_var(var, phi_value, block);
                self.add_phi_args(func, var, phi_insn);
                phi_value
            }
        }
    }

    fn add_phi_args(&mut self, func: &mut Function, var: Variable, phi: Insn) {
        let block = func.layout.insn_block(phi);

        if let Some(preds) = self.preds.remove(&block) {
            for pred in &preds {
                let value = self.use_var(func, var, *pred);
                func.dfg.append_phi_arg(phi, value);
            }
            self.preds.insert(block, preds);
        }

        self.remove_trivial_phi(func, phi);
    }

    fn remove_trivial_phi(&mut self, func: &mut Function, phi: Insn) {
        let phi_value = func.dfg.insn_result(phi).unwrap();
        let phi_args = func.dfg.insn_args(phi);
        if phi_args.is_empty() {
            panic!("variable is undefined or used in unreachable block");
        }

        let first = func.dfg.resolve_alias(phi_args[0]);
        let mut resolved_args = Vec::with_capacity(phi_args.len());
        resolved_args.push(first);

        if phi_args
            .iter()
            .any(|arg| func.dfg.resolve_alias(*arg) != first)
        {
            return;
        }

        let arg_len = phi_args.len();
        for i in 0..arg_len {
            let arg = func.dfg.insn_arg(phi, i);
            func.dfg.make_alias(arg, first);
        }
        self.trivial_phis.insert(phi);
        FunctionCursor::new(func, CursorLocation::At(phi)).remove_insn();

        for i in 0..func.dfg.users(phi_value).len() {
            let user = func.dfg.user_of(phi_value, i);
            if func.dfg.is_phi(user) && !self.trivial_phis.contains(&phi) {
                self.remove_trivial_phi(func, phi);
            }
        }
    }

    fn prepend_phi(&mut self, func: &mut Function, block: Block) -> (Insn, Value) {
        let insn_data = InsnData::Phi { args: Vec::new() };
        let mut cursor = FunctionCursor::new(func, CursorLocation::BlockTop(block));
        let (insn, value) = cursor.prepend_insn(insn_data);
        (insn, value.unwrap())
    }
}
