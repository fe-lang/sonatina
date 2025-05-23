//! SSA construction algorithm here is based on [`Simple and Efficient
//! Construction of Static Single Assignment Form`](https://link.springer.com/chapter/10.1007/978-3-642-37051-9_6).

use cranelift_entity::{packed_option::PackedOption, PrimaryMap, SecondaryMap, SparseSet};
use rustc_hash::FxHashMap;

use crate::{
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow,
    BlockId, Function, InstId, Type, Value, ValueId,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Variable(u32);
cranelift_entity::entity_impl!(Variable);

pub struct VariableData {
    ty: Type,
}

pub(super) struct SsaBuilder {
    blocks: SecondaryMap<BlockId, SsaBlock>,

    /// Records all declared variables.
    vars: PrimaryMap<Variable, VariableData>,

    /// Records trivial phis.
    trivial_phis: SparseSet<InstId>,
    aliases: FxHashMap<ValueId, ValueId>,
}

impl SsaBuilder {
    pub(super) fn new() -> Self {
        SsaBuilder {
            blocks: SecondaryMap::default(),
            vars: PrimaryMap::default(),
            trivial_phis: SparseSet::new(),
            aliases: FxHashMap::default(),
        }
    }
    pub(super) fn declare_var(&mut self, ty: Type) -> Variable {
        self.vars.push(VariableData { ty })
    }

    pub(super) fn def_var(&mut self, var: Variable, value: ValueId, block: BlockId) {
        self.blocks[block].def_var(var, value);
    }

    pub(super) fn use_var(
        &mut self,
        func: &mut Function,
        var: Variable,
        block: BlockId,
    ) -> ValueId {
        let value = if let Some(value) = self.blocks[block].use_var_local(var) {
            value
        } else {
            self.use_var_recursive(func, var, block)
        };
        *self.aliases.get(&value).unwrap_or(&value)
    }

    pub(super) fn var_ty(&mut self, var: Variable) -> Type {
        self.vars[var].ty
    }

    pub(super) fn append_pred(&mut self, block: BlockId, pred: BlockId) {
        self.blocks[block].append_pred(pred);
    }

    pub(super) fn seal_block(&mut self, func: &mut Function, block: BlockId) {
        if self.is_sealed(block) {
            return;
        }

        for (var, phi) in self.blocks[block].take_incomplete_phis() {
            self.add_phi_args(func, var, phi);
        }

        self.blocks[block].seal();
    }

    pub(super) fn seal_all(&mut self, func: &mut Function) {
        let mut next_block = func.layout.entry_block();
        while let Some(block) = next_block {
            self.seal_block(func, block);
            next_block = func.layout.next_block_of(block);
        }
    }

    pub(super) fn is_sealed(&self, block: BlockId) -> bool {
        self.blocks[block].is_sealed()
    }

    fn use_var_recursive(&mut self, func: &mut Function, var: Variable, block: BlockId) -> ValueId {
        if !self.is_sealed(block) {
            let (inst, value) = self.prepend_phi(func, var, block);
            self.blocks[block].push_incomplete_phi(var, inst);
            self.def_var(var, value, block);
            return value;
        }

        match *self.blocks[block].preds() {
            [pred] => self.use_var(func, var, pred),
            _ => {
                let (phi_inst, phi_value) = self.prepend_phi(func, var, block);
                // Break potential cycles by defining operandless phi.
                self.def_var(var, phi_value, block);
                self.add_phi_args(func, var, phi_inst);
                phi_value
            }
        }
    }

    fn add_phi_args(&mut self, func: &mut Function, var: Variable, phi: InstId) {
        let block = func.layout.inst_block(phi);
        let preds = std::mem::take(&mut self.blocks[block].preds);

        for pred in &preds {
            let value = self.use_var(func, var, *pred);
            func.dfg.append_phi_arg(phi, value, *pred);
        }
        self.blocks[block].preds = preds;

        self.remove_trivial_phi(func, phi);
    }

    fn remove_trivial_phi(&mut self, func: &mut Function, inst_id: InstId) {
        let phi_value = func.dfg.inst_result(inst_id).unwrap();
        let phi = func.dfg.cast_phi_mut(inst_id).unwrap();

        let phi_args = phi.args_mut();
        if phi_args.is_empty() {
            panic!("variable is undefined or used in unreachable block");
        }

        let first_value = phi_args[0].0;

        if phi_args.iter().any(|arg| arg.0 != first_value) {
            return;
        }

        self.change_to_alias(func, phi_value, first_value);
        self.trivial_phis.insert(inst_id);
        InstInserter::at_location(CursorLocation::At(inst_id)).remove_inst(func);

        for i in 0..func.dfg.users_num(phi_value) {
            let user = *func.dfg.users(phi_value).nth(i).unwrap();
            if func.dfg.cast_phi(user).is_some() && !self.trivial_phis.contains_key(user) {
                self.remove_trivial_phi(func, user);
            }
        }
    }

    fn prepend_phi(
        &mut self,
        func: &mut Function,
        var: Variable,
        block: BlockId,
    ) -> (InstId, ValueId) {
        let ty = self.var_ty(var);
        let is = func.dfg.inst_set();
        let phi = control_flow::Phi::new(is.phi(), Vec::new());
        let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(block));

        let inst = cursor.prepend_inst_data(func, phi);
        let value = func.dfg.make_value(Value::Inst { inst, ty });
        cursor.attach_result(func, inst, value);
        (inst, value)
    }

    fn change_to_alias(&mut self, func: &mut Function, value: ValueId, alias: ValueId) {
        func.dfg.change_to_alias(value, alias);
        self.aliases.insert(value, alias);
    }
}

#[derive(Default, Clone)]
struct SsaBlock {
    /// Records all predecessors of a block.
    preds: Vec<BlockId>,

    /// Records sealed blocks.
    is_sealed: bool,

    /// Records defined variables in an block.
    defs: SecondaryMap<Variable, PackedOption<ValueId>>,

    /// Records phis in an unsealed block.
    incomplete_phis: Vec<(Variable, InstId)>,
}

impl SsaBlock {
    fn def_var(&mut self, var: Variable, value: ValueId) {
        self.defs[var] = value.into();
    }

    fn use_var_local(&self, var: Variable) -> Option<ValueId> {
        self.defs[var].expand()
    }

    fn append_pred(&mut self, pred: BlockId) {
        self.preds.push(pred);
    }

    fn seal(&mut self) {
        self.is_sealed = true;
    }

    fn is_sealed(&self) -> bool {
        self.is_sealed
    }

    fn take_incomplete_phis(&mut self) -> Vec<(Variable, InstId)> {
        std::mem::take(&mut self.incomplete_phis)
    }

    fn push_incomplete_phi(&mut self, var: Variable, inst_id: InstId) {
        self.incomplete_phis.push((var, inst_id))
    }

    fn preds(&self) -> &[BlockId] {
        &self.preds
    }
}

#[cfg(test)]
mod tests {
    use control_flow::{Br, BrTable, Jump, Phi, Return};
    use macros::inst_set;

    use super::{super::test_util::*, *};
    use crate::{inst::arith::Add, isa::Isa};

    #[inst_set(InstKind = "TestInstKind")]
    struct TestInstSet(Phi, Jump, Add, Return, Br, BrTable);

    #[test]
    fn use_var_local() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let var = builder.declare_var(Type::I32);

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let v0 = builder.make_imm_value(1i32);
        builder.def_var(var, v0);
        let v1 = builder.use_var(var);
        let add = Add::new(is, v1, v0);
        builder.insert_inst(add, Type::I32);

        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);
        builder.seal_block();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        v1.i32 = add 1.i32 1.i32;
        return;
}
"
        );
    }

    #[test]
    fn use_var_global_if() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let imm = builder.make_imm_value(1i32);
        let br = Br::new(is, imm, b2, b1);
        builder.insert_inst_no_result(br);

        builder.seal_block();

        builder.switch_to_block(b1);
        let imm = builder.make_imm_value(2i32);
        builder.def_var(var, imm);
        let jump = Jump::new(is, b3);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b2);
        let imm = builder.make_imm_value(3i32);
        builder.def_var(var, imm);
        let jump = Jump::new(is, b3);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b3);
        builder.use_var(var);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);
        builder.seal_block();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        br 1.i32 block2 block1;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v3.i32 = phi (2.i32 block1) (3.i32 block2);
        return;
}
"
        );
    }

    #[test]
    fn use_var_global_many_preds() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let var0 = builder.declare_var(Type::I32);
        let var1 = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();
        let b7 = builder.append_block();

        builder.switch_to_block(b0);
        let v0 = builder.make_imm_value(0i32);
        builder.def_var(var1, v0);
        let br = Br::new(is, v0, b1, b2);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b1);
        let v1 = builder.make_imm_value(1i32);
        builder.def_var(var0, v1);
        builder.def_var(var1, v1);
        let jump = Jump::new(is, b7);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b2);
        let br = Br::new(is, v0, b3, b4);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b3);
        let v2 = builder.make_imm_value(2i32);
        builder.def_var(var0, v2);
        let jump = Jump::new(is, b7);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b4);
        let br = Br::new(is, v0, b5, b6);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b5);
        let v3 = builder.make_imm_value(3i32);
        builder.def_var(var0, v3);
        let jump = Jump::new(is, b7);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b6);
        let v4 = builder.make_imm_value(4i32);
        builder.def_var(var0, v4);
        let jump = Jump::new(is, b7);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b7);
        let v_var0 = builder.use_var(var0);
        let v_var1 = builder.use_var(var1);
        let add = Add::new(is, v_var0, v_var1);
        builder.insert_inst(add, Type::I32);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        br 0.i32 block1 block2;

    block1:
        jump block7;

    block2:
        br 0.i32 block3 block4;

    block3:
        jump block7;

    block4:
        br 0.i32 block5 block6;

    block5:
        jump block7;

    block6:
        jump block7;

    block7:
        v6.i32 = phi (1.i32 block1) (0.i32 block3) (0.i32 block5) (0.i32 block6);
        v5.i32 = phi (1.i32 block1) (2.i32 block3) (3.i32 block5) (4.i32 block6);
        v7.i32 = add v5 v6;
        return;
}
"
        )
    }

    #[test]
    fn use_var_global_loop() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let value = builder.make_imm_value(1i32);
        builder.def_var(var, value);
        let jump = Jump::new(is, b1);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b1);
        let br = Br::new(is, value, b2, b3);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b2);
        let value = builder.make_imm_value(10i32);
        builder.def_var(var, value);
        let jump = Jump::new(is, b1);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b1);
        builder.seal_block();

        builder.switch_to_block(b3);
        let val = builder.use_var(var);
        let add = Add::new(is, val, val);
        builder.insert_inst(add, Type::I32);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);
        builder.seal_block();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        jump block1;

    block1:
        v4.i32 = phi (1.i32 block0) (10.i32 block2);
        br 1.i32 block2 block3;

    block2:
        jump block1;

    block3:
        v3.i32 = add v4 v4;
        return;
}
"
        );
    }

    #[test]
    fn use_var_global_complex() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();

        builder.switch_to_block(b0);
        let value1 = builder.make_imm_value(1i32);
        builder.def_var(var, value1);
        let jump = Jump::new(is, b1);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b1);
        let br = Br::new(is, value1, b6, b2);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b2);
        let br = Br::new(is, value1, b4, b3);
        builder.insert_inst_no_result(br);
        builder.seal_block();

        builder.switch_to_block(b3);
        let value2 = builder.make_imm_value(2i32);
        builder.def_var(var, value2);
        let jump = Jump::new(is, b5);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b4);
        let jump = Jump::new(is, b5);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b5);
        let jump = Jump::new(is, b1);
        builder.insert_inst_no_result(jump);
        builder.seal_block();

        builder.switch_to_block(b1);
        builder.seal_block();

        builder.switch_to_block(b6);
        let val = builder.use_var(var);
        let add = Add::new(is, val, val);
        builder.insert_inst(add, Type::I32);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);
        builder.seal_block();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        jump block1;

    block1:
        v4.i32 = phi (1.i32 block0) (v5 block5);
        br 1.i32 block6 block2;

    block2:
        br 1.i32 block4 block3;

    block3:
        jump block5;

    block4:
        jump block5;

    block5:
        v5.i32 = phi (2.i32 block3) (v4 block4);
        jump block1;

    block6:
        v3.i32 = add v4 v4;
        return;
}
"
        );
    }

    #[test]
    fn use_var_global_complex_seal_all() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();

        builder.switch_to_block(b0);
        let value1 = builder.make_imm_value(1i32);
        builder.def_var(var, value1);
        let jump = Jump::new(is, b1);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b1);
        let br = Br::new(is, value1, b6, b2);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b2);
        let br = Br::new(is, value1, b4, b3);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b3);
        let value2 = builder.make_imm_value(2i32);
        builder.def_var(var, value2);
        let jump = Jump::new(is, b5);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b4);
        let jump = Jump::new(is, b5);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b5);
        let jump = Jump::new(is, b1);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b1);

        builder.switch_to_block(b6);
        let val = builder.use_var(var);
        let add = Add::new(is, val, val);
        builder.insert_inst(add, Type::I32);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        jump block1;

    block1:
        v4.i32 = phi (1.i32 block0) (v5 block5);
        br 1.i32 block6 block2;

    block2:
        br 1.i32 block4 block3;

    block3:
        jump block5;

    block4:
        jump block5;

    block5:
        v5.i32 = phi (2.i32 block3) (v4 block4);
        jump block1;

    block6:
        v3.i32 = add v4 v4;
        return;
}
"
        );
    }

    #[test]
    fn br_table() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32], Type::I32);
        let is = evm.inst_set();
        let var = builder.declare_var(Type::I32);

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();

        builder.switch_to_block(b0);
        let value0 = builder.make_imm_value(0i32);
        let value1 = builder.make_imm_value(1i32);
        let value2 = builder.make_imm_value(2i32);
        let value3 = builder.make_imm_value(3i32);

        builder.def_var(var, value0);

        let brt = BrTable::new(
            is,
            builder.args()[0],
            Some(b4),
            vec![(value1, b1), (value2, b2), (value3, b3)],
        );
        builder.insert_inst_no_result(brt);

        builder.switch_to_block(b1);
        builder.def_var(var, value1);
        let jump = Jump::new(is, b4);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b2);
        builder.def_var(var, value2);
        let jump = Jump::new(is, b4);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b3);
        builder.def_var(var, value3);
        let jump = Jump::new(is, b4);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(b4);
        let ret_val = builder.use_var(var);
        let ret = Return::new(is, ret_val.into());
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func(v0.i32) -> i32 {
    block0:
        br_table v0 block4 (1.i32 block1) (2.i32 block2) (3.i32 block3);

    block1:
        jump block4;

    block2:
        jump block4;

    block3:
        jump block4;

    block4:
        v5.i32 = phi (0.i32 block0) (1.i32 block1) (2.i32 block2) (3.i32 block3);
        return v5;
}
"
        )
    }

    #[test]
    #[should_panic]
    fn undef_use() {
        let mb = test_module_builder();
        let (_, mut builder) = test_func_builder(&mb, &[], Type::Unit);

        let var = builder.declare_var(Type::I32);
        let b1 = builder.append_block();
        builder.switch_to_block(b1);
        builder.use_var(var);
        builder.seal_block();
    }

    #[test]
    #[should_panic]
    fn unreachable_use() {
        let mb = test_module_builder();
        let (_, mut builder) = test_func_builder(&mb, &[], Type::Unit);

        let var = builder.declare_var(Type::I32);
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b1);
        let imm = builder.make_imm_value(1i32);
        builder.def_var(var, imm);
        builder.seal_block();

        builder.switch_to_block(b2);
        builder.use_var(var);
        builder.seal_block();
    }
}
