//! SSA construction algorighm here is based on [`Simple and Efficient Construction of Static
//! Single Assignment Form`](https://link.springer.com/chapter/10.1007/978-3-642-37051-9_6).

use cranelift_entity::{packed_option::PackedOption, PrimaryMap, SecondaryMap, SparseSet};
use smallvec::SmallVec;

use crate::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    InsnData,
};

use crate::{Block, Function, Insn, Type, Value};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Variable(u32);
cranelift_entity::entity_impl!(Variable);

pub struct VariableData {
    ty: Type,
}

pub(super) struct SsaBuilder {
    blocks: SecondaryMap<Block, SsaBlockData>,

    /// Records all declared variables.
    vars: PrimaryMap<Variable, VariableData>,

    /// Records trivial phis.
    trivial_phis: SparseSet<Insn>,
}

impl Default for SsaBuilder {
    fn default() -> Self {
        Self {
            blocks: SecondaryMap::default(),
            vars: PrimaryMap::new(),
            trivial_phis: SparseSet::new(),
        }
    }
}

#[derive(Default, Clone)]
struct SsaBlockData {
    /// Records all predecessors of a block.
    preds: Vec<Block>,

    /// Records sealed blocks.
    is_sealed: bool,

    /// Records defined variables in an block.
    defs: SecondaryMap<Variable, PackedOption<Value>>,

    /// Records phis in an unsealed block.
    incomplete_phis: Vec<(Variable, Insn)>,
}

impl SsaBlockData {
    fn def_var(&mut self, var: Variable, value: Value) {
        self.defs[var] = value.into();
    }

    fn use_var_local(&self, var: Variable) -> Option<Value> {
        self.defs[var].expand()
    }

    fn append_pred(&mut self, pred: Block) {
        self.preds.push(pred);
    }

    fn seal(&mut self) {
        self.is_sealed = true;
    }

    fn is_sealed(&self) -> bool {
        self.is_sealed
    }

    fn take_incomplete_phis(&mut self) -> Vec<(Variable, Insn)> {
        std::mem::take(&mut self.incomplete_phis)
    }

    fn push_incomplete_phi(&mut self, var: Variable, insn: Insn) {
        self.incomplete_phis.push((var, insn))
    }

    fn preds(&self) -> &[Block] {
        &self.preds
    }
}

impl SsaBuilder {
    pub(super) fn declare_var(&mut self, ty: Type) -> Variable {
        self.vars.push(VariableData { ty })
    }

    pub(super) fn def_var(&mut self, var: Variable, value: Value, block: Block) {
        self.blocks[block].def_var(var, value);
    }

    pub(super) fn use_var(&mut self, func: &mut Function, var: Variable, block: Block) -> Value {
        if let Some(value) = self.blocks[block].use_var_local(var) {
            value
        } else {
            self.use_var_recursive(func, var, block)
        }
    }

    pub(super) fn var_ty(&mut self, var: Variable) -> &Type {
        &self.vars[var].ty
    }

    pub(super) fn append_pred(&mut self, block: Block, pred: Block) {
        self.blocks[block].append_pred(pred);
    }

    pub(super) fn seal_block(&mut self, func: &mut Function, block: Block) {
        if self.is_sealed(block) {
            return;
        }

        for (var, phi) in self.blocks[block].take_incomplete_phis() {
            self.add_phi_args(func, var, phi);
        }

        self.blocks[block].seal();
    }

    pub(super) fn seal_all(&mut self, func: &mut Function) {
        let mut next_block = func.layout.first_block();
        while let Some(block) = next_block {
            self.seal_block(func, block);
            next_block = func.layout.next_block_of(block);
        }
    }

    pub(super) fn is_sealed(&self, block: Block) -> bool {
        self.blocks[block].is_sealed()
    }

    fn use_var_recursive(&mut self, func: &mut Function, var: Variable, block: Block) -> Value {
        if !self.is_sealed(block) {
            let (insn, value) = self.prepend_phi(func, var, block);
            self.blocks[block].push_incomplete_phi(var, insn);
            self.def_var(var, value, block);
            return value;
        }

        match *self.blocks[block].preds() {
            [pred] => self.use_var(func, var, pred),
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
        let preds = std::mem::take(&mut self.blocks[block].preds);

        for pred in &preds {
            let value = self.use_var(func, var, *pred);
            func.dfg.append_phi_arg(phi, value, *pred);
        }
        self.blocks[block].preds = preds;

        self.remove_trivial_phi(func, phi);
    }

    fn remove_trivial_phi(&mut self, func: &mut Function, phi: Insn) {
        let phi_value = func.dfg.insn_result(phi).unwrap();
        let phi_args = func.dfg.insn_args(phi);
        if phi_args.is_empty() {
            panic!("variable is undefined or used in unreachable block");
        }

        let first = phi_args[0];

        if phi_args.iter().any(|arg| *arg != first) {
            return;
        }

        func.dfg.replace_value(phi_value, first);
        self.trivial_phis.insert(phi);
        InsnInserter::new(func, CursorLocation::At(phi)).remove_insn();

        for i in 0..func.dfg.users_num(phi_value) {
            let user = func.dfg.user(phi_value, i);
            if func.dfg.is_phi(user) && !self.trivial_phis.contains_key(user) {
                self.remove_trivial_phi(func, user);
            }
        }
    }

    fn prepend_phi(&mut self, func: &mut Function, var: Variable, block: Block) -> (Insn, Value) {
        let ty = self.var_ty(var).clone();
        let insn_data = InsnData::Phi {
            values: SmallVec::new(),
            blocks: SmallVec::new(),
            ty,
        };
        let mut cursor = InsnInserter::new(func, CursorLocation::BlockTop(block));
        let insn = cursor.prepend_insn_data(insn_data);
        let value = cursor.make_result(insn);
        if let Some(value) = value {
            cursor.attach_result(insn, value);
        }
        (insn, value.unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_util::*;
    use super::*;

    #[test]
    fn use_var_local() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let v0 = builder.imm_i32(1);
        builder.def_var(var, v0);
        let v1 = builder.use_var(var);
        builder.add(v1, v0);
        builder.ret(&[]);
        builder.seal_block();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func():
    block0:
        v0.i32 = imm_i32 1;
        v1.i32 = add v0 v0;
        return;

"
        );
    }

    #[test]
    fn use_var_global_if() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let imm = builder.imm_i32(1);
        builder.br(imm, b2, b1);
        builder.seal_block();

        builder.switch_to_block(b1);
        let imm = builder.imm_i32(2);
        builder.def_var(var, imm);
        builder.jump(b3);
        builder.seal_block();

        builder.switch_to_block(b2);
        let imm = builder.imm_i32(3);
        builder.def_var(var, imm);
        builder.jump(b3);
        builder.seal_block();

        builder.switch_to_block(b3);
        builder.use_var(var);
        builder.ret(&[]);
        builder.seal_block();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func():
    block0:
        v0.i32 = imm_i32 1;
        br v0 block2 block1;

    block1:
        v1.i32 = imm_i32 2;
        jump block3;

    block2:
        v2.i32 = imm_i32 3;
        jump block3;

    block3:
        v3.i32 = phi (v1 block1) (v2 block2);
        return;

"
        );
    }

    #[test]
    fn use_var_global_loop() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let value = builder.imm_i32(1);
        builder.def_var(var, value);
        builder.jump(b1);
        builder.seal_block();

        builder.switch_to_block(b1);
        builder.br(value, b2, b3);

        builder.switch_to_block(b2);
        let value = builder.imm_i32(10);
        builder.def_var(var, value);
        builder.jump(b1);
        builder.seal_block();

        builder.switch_to_block(b1);
        builder.seal_block();

        builder.switch_to_block(b3);
        let val = builder.use_var(var);
        builder.add(val, val);
        builder.ret(&[]);
        builder.seal_block();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func():
    block0:
        v0.i32 = imm_i32 1;
        jump block1;

    block1:
        v4.i32 = phi (v0 block0) (v1 block2);
        br v0 block2 block3;

    block2:
        v1.i32 = imm_i32 10;
        jump block1;

    block3:
        v3.i32 = add v4 v4;
        return;

"
        );
    }

    #[test]
    fn use_var_global_complex() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();

        builder.switch_to_block(b0);
        let value1 = builder.imm_i32(1);
        builder.def_var(var, value1);
        builder.jump(b1);
        builder.seal_block();

        builder.switch_to_block(b1);
        builder.br(value1, b6, b2);

        builder.switch_to_block(b2);
        builder.br(value1, b4, b3);
        builder.seal_block();

        builder.switch_to_block(b3);
        let value2 = builder.imm_i32(2);
        builder.def_var(var, value2);
        builder.jump(b5);
        builder.seal_block();

        builder.switch_to_block(b4);
        builder.jump(b5);
        builder.seal_block();

        builder.switch_to_block(b5);
        builder.jump(b1);
        builder.seal_block();

        builder.switch_to_block(b1);
        builder.seal_block();

        builder.switch_to_block(b6);
        let val = builder.use_var(var);
        builder.add(val, val);
        builder.ret(&[]);
        builder.seal_block();

        let f = builder.build();

        assert_eq!(
            dump_func(&f),
            "func %test_func():
    block0:
        v0.i32 = imm_i32 1;
        jump block1;

    block1:
        v4.i32 = phi (v0 block0) (v5 block5);
        br v0 block6 block2;

    block2:
        br v0 block4 block3;

    block3:
        v1.i32 = imm_i32 2;
        jump block5;

    block4:
        jump block5;

    block5:
        v5.i32 = phi (v1 block3) (v4 block4);
        jump block1;

    block6:
        v3.i32 = add v4 v4;
        return;

"
        );
    }

    #[test]
    fn use_var_global_complex_seal_all() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();

        builder.switch_to_block(b0);
        let value1 = builder.imm_i32(1);
        builder.def_var(var, value1);
        builder.jump(b1);

        builder.switch_to_block(b1);
        builder.br(value1, b6, b2);

        builder.switch_to_block(b2);
        builder.br(value1, b4, b3);

        builder.switch_to_block(b3);
        let value2 = builder.imm_i32(2);
        builder.def_var(var, value2);
        builder.jump(b5);

        builder.switch_to_block(b4);
        builder.jump(b5);

        builder.switch_to_block(b5);
        builder.jump(b1);

        builder.switch_to_block(b1);

        builder.switch_to_block(b6);
        let val = builder.use_var(var);
        builder.add(val, val);
        builder.ret(&[]);

        builder.seal_all();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func():
    block0:
        v0.i32 = imm_i32 1;
        jump block1;

    block1:
        v4.i32 = phi (v0 block0) (v5 block5);
        br v0 block6 block2;

    block2:
        br v0 block4 block3;

    block3:
        v1.i32 = imm_i32 2;
        jump block5;

    block4:
        jump block5;

    block5:
        v5.i32 = phi (v1 block3) (v4 block4);
        jump block1;

    block6:
        v3.i32 = add v4 v4;
        return;

"
        );
    }

    #[test]
    #[should_panic]
    fn undef_use() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);
        let b1 = builder.append_block();
        builder.switch_to_block(b1);
        builder.use_var(var);
        builder.seal_block();
    }

    #[test]
    #[should_panic]
    fn unreachable_use() {
        let mut builder = func_builder(&[], &[]);

        let var = builder.declare_var(Type::I32);
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b1);
        let imm = builder.imm_i32(1);
        builder.def_var(var, imm);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.use_var(var);
        builder.seal_block();
    }
}
