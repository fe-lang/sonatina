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
        if self.is_sealed(block) {
            return;
        }

        for (var, phi) in self.incomplete_phis.remove(&block).unwrap_or_default() {
            self.add_phi_args(func, var, phi);
        }

        self.sealed.insert(block);
    }

    pub(super) fn seal_all(&mut self, func: &mut Function) {
        let mut next_block = func.layout.first_block();
        while let Some(block) = next_block {
            self.seal_block(func, block);
            next_block = func.layout.next_block_of(block);
        }
    }

    pub(super) fn is_sealed(&self, block: Block) -> bool {
        self.sealed.contains(&block)
    }

    fn use_var_recursive(&mut self, func: &mut Function, var: Variable, block: Block) -> Value {
        if !self.is_sealed(block) {
            let (insn, value) = self.prepend_phi(func, var, block);
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
                let (phi_insn, phi_value) = self.prepend_phi(func, var, block);
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

        if phi_args
            .iter()
            .any(|arg| func.dfg.resolve_alias(*arg) != first)
        {
            return;
        }

        func.dfg.make_alias(phi_value, first);
        self.trivial_phis.insert(phi);
        FunctionCursor::new(func, CursorLocation::At(phi)).remove_insn();

        for i in 0..func.dfg.users(phi_value).len() {
            let user = func.dfg.user_of(phi_value, i);
            if func.dfg.is_phi(user) && !self.trivial_phis.contains(&user) {
                self.remove_trivial_phi(func, user);
            }
        }
    }

    fn prepend_phi(&mut self, func: &mut Function, var: Variable, block: Block) -> (Insn, Value) {
        let ty = self.var_ty(var).clone();
        let insn_data = InsnData::Phi {
            args: Vec::new(),
            ty,
        };
        let mut cursor = FunctionCursor::new(func, CursorLocation::BlockTop(block));
        let (insn, value) = cursor.prepend_insn(insn_data);
        (insn, value.unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::*;

    #[test]
    fn use_var_local() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);

        let entry_block = builder.append_block("entry");
        builder.switch_to_block(entry_block);
        let v0 = builder.imm_i32(1);
        builder.def_var(var, v0);
        let v1 = builder.use_var(var);
        builder.add(v1, v0);
        builder.seal_block();

        assert_eq!(
            dump_func(builder),
            "func %test_func():
    entry:
        %v0.i32 = imm.i32 1
        %v1.i32 = add %v0.i32 %v0.i32

"
        );
    }

    #[test]
    fn use_var_global_if() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);

        let b1 = builder.append_block("b1");
        let b2 = builder.append_block("b2");
        let b3 = builder.append_block("b3");
        let b4 = builder.append_block("b4");

        builder.switch_to_block(b1);
        let imm = builder.imm_i32(1);
        builder.brz(b2, imm);
        builder.jump(b3);
        builder.seal_block();

        builder.switch_to_block(b2);
        let imm = builder.imm_i32(2);
        builder.def_var(var, imm);
        builder.jump(b4);
        builder.seal_block();

        builder.switch_to_block(b3);
        let imm = builder.imm_i32(3);
        builder.def_var(var, imm);
        builder.jump(b4);
        builder.seal_block();

        builder.switch_to_block(b4);
        builder.use_var(var);
        builder.seal_block();

        assert_eq!(
            dump_func(builder),
            "func %test_func():
    b1:
        %v0.i32 = imm.i32 1
        brz %v0.i32 b2
        jump b3

    b2:
        %v1.i32 = imm.i32 2
        jump b4

    b3:
        %v2.i32 = imm.i32 3
        jump b4

    b4:
        %v3.i32 = phi %v1.i32 %v2.i32

"
        );
    }

    #[test]
    fn use_var_global_loop() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);

        let b1 = builder.append_block("b1");
        let b2 = builder.append_block("b2");
        let b3 = builder.append_block("b3");
        let b4 = builder.append_block("b4");

        builder.switch_to_block(b1);
        let value = builder.imm_i32(1);
        builder.def_var(var, value);
        builder.jump(b2);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.brz(b4, value);
        builder.jump(b3);

        builder.switch_to_block(b3);
        let value = builder.imm_i32(10);
        builder.def_var(var, value);
        builder.jump(b2);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.seal_block();

        builder.switch_to_block(b4);
        let val = builder.use_var(var);
        builder.add(val, val);
        builder.seal_block();

        assert_eq!(
            dump_func(builder),
            "func %test_func():
    b1:
        %v0.i32 = imm.i32 1
        jump b2

    b2:
        %v4.i32 = phi %v0.i32 %v1.i32
        brz %v0.i32 b4
        jump b3

    b3:
        %v1.i32 = imm.i32 10
        jump b2

    b4:
        %v3.i32 = add %v4.i32 %v4.i32

"
        );
    }

    #[test]
    fn use_var_global_complex() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);

        let b1 = builder.append_block("b1");
        let b2 = builder.append_block("b2");
        let b3 = builder.append_block("b3");
        let b4 = builder.append_block("b4");
        let b5 = builder.append_block("b5");
        let b6 = builder.append_block("b6");
        let b7 = builder.append_block("b7");

        builder.switch_to_block(b1);
        let value1 = builder.imm_i32(1);
        builder.def_var(var, value1);
        builder.jump(b2);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.brz(b3, value1);
        builder.jump(b7);

        builder.switch_to_block(b3);
        builder.brz(b4, value1);
        builder.jump(b5);
        builder.seal_block();

        builder.switch_to_block(b4);
        let value2 = builder.imm_i32(2);
        builder.def_var(var, value2);
        builder.jump(b6);
        builder.seal_block();

        builder.switch_to_block(b5);
        builder.jump(b6);
        builder.seal_block();

        builder.switch_to_block(b6);
        builder.jump(b2);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.seal_block();

        builder.switch_to_block(b7);
        let val = builder.use_var(var);
        builder.add(val, val);
        builder.seal_block();

        assert_eq!(
            dump_func(builder),
            "func %test_func():
    b1:
        %v0.i32 = imm.i32 1
        jump b2

    b2:
        %v4.i32 = phi %v0.i32 %v5.i32
        brz %v0.i32 b3
        jump b7

    b3:
        brz %v0.i32 b4
        jump b5

    b4:
        %v1.i32 = imm.i32 2
        jump b6

    b5:
        jump b6

    b6:
        %v5.i32 = phi %v1.i32 %v4.i32
        jump b2

    b7:
        %v3.i32 = add %v4.i32 %v4.i32

"
        );
    }

    #[test]
    fn use_var_global_complex_seal_all() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);

        let b1 = builder.append_block("b1");
        let b2 = builder.append_block("b2");
        let b3 = builder.append_block("b3");
        let b4 = builder.append_block("b4");
        let b5 = builder.append_block("b5");
        let b6 = builder.append_block("b6");
        let b7 = builder.append_block("b7");

        builder.switch_to_block(b1);
        let value1 = builder.imm_i32(1);
        builder.def_var(var, value1);
        builder.jump(b2);

        builder.switch_to_block(b2);
        builder.brz(b3, value1);
        builder.jump(b7);

        builder.switch_to_block(b3);
        builder.brz(b4, value1);
        builder.jump(b5);

        builder.switch_to_block(b4);
        let value2 = builder.imm_i32(2);
        builder.def_var(var, value2);
        builder.jump(b6);

        builder.switch_to_block(b5);
        builder.jump(b6);

        builder.switch_to_block(b6);
        builder.jump(b2);

        builder.switch_to_block(b2);

        builder.switch_to_block(b7);
        let val = builder.use_var(var);
        builder.add(val, val);

        builder.seal_all();

        assert_eq!(
            dump_func(builder),
            "func %test_func():
    b1:
        %v0.i32 = imm.i32 1
        jump b2

    b2:
        %v4.i32 = phi %v0.i32 %v5.i32
        brz %v0.i32 b3
        jump b7

    b3:
        brz %v0.i32 b4
        jump b5

    b4:
        %v1.i32 = imm.i32 2
        jump b6

    b5:
        jump b6

    b6:
        %v5.i32 = phi %v1.i32 %v4.i32
        jump b2

    b7:
        %v3.i32 = add %v4.i32 %v4.i32

"
        );
    }

    #[test]
    #[should_panic]
    fn undef_use() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);
        let b1 = builder.append_block("b1");
        builder.switch_to_block(b1);
        builder.use_var(var);
        builder.seal_block();
    }

    #[test]
    #[should_panic]
    fn unreachable_use() {
        let mut builder = func_builder(vec![], vec![]);

        let var = builder.declare_var(Type::I32);
        let b1 = builder.append_block("b1");
        let b2 = builder.append_block("b2");

        builder.switch_to_block(b1);
        let imm = builder.imm_i32(1);
        builder.def_var(var, imm);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.use_var(var);
        builder.seal_block();
    }
}
