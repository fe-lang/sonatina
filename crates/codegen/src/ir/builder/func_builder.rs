use smallvec::SmallVec;

use crate::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{BinaryOp, CastOp, DataLocationKind, InsnData, JumpOp, UnaryOp},
    module::FuncRef,
    Block, Function, Immediate, Type, Value,
};

use super::{
    ssa::{SsaBuilder, Variable},
    ModuleBuilder,
};

pub struct FunctionBuilder<'a> {
    module_builder: &'a mut ModuleBuilder,
    func_ref: FuncRef,
    loc: CursorLocation,
    ssa_builder: SsaBuilder,
}

macro_rules! impl_unary_insn {
    ($name:ident, $code:path) => {
        pub fn $name(&mut self, lhs: Value) -> Value {
            let insn_data = InsnData::Unary {
                code: $code,
                args: [lhs],
            };

            self.insert_insn(insn_data).unwrap()
        }
    };
}

macro_rules! impl_binary_insn {
    ($name:ident, $code:path) => {
        pub fn $name(&mut self, lhs: Value, rhs: Value) -> Value {
            let insn_data = InsnData::Binary {
                code: $code,
                args: [lhs, rhs],
            };

            self.insert_insn(insn_data).unwrap()
        }
    };
}

macro_rules! impl_cast_insn {
    ($name:ident, $code:path) => {
        pub fn $name(&mut self, lhs: Value, ty: Type) -> Value {
            let insn_data = InsnData::Cast {
                code: $code,
                args: [lhs],
                ty,
            };

            self.insert_insn(insn_data).unwrap()
        }
    };
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(module_builder: &'a mut ModuleBuilder, func_ref: FuncRef) -> Self {
        Self {
            module_builder,
            func_ref,
            loc: CursorLocation::NoWhere,
            ssa_builder: SsaBuilder::new(),
        }
    }

    pub fn append_block(&mut self) -> Block {
        let block = self.cursor().make_block();
        self.cursor().append_block(block);
        block
    }

    pub fn switch_to_block(&mut self, block: Block) {
        self.loc = CursorLocation::BlockBottom(block);
    }

    pub fn make_imm_value<Imm>(&mut self, imm: Imm) -> Value
    where
        Imm: Into<Immediate>,
    {
        self.func_mut().dfg.make_imm_value(imm)
    }

    impl_unary_insn!(not, UnaryOp::Not);
    impl_unary_insn!(neg, UnaryOp::Neg);

    impl_binary_insn!(add, BinaryOp::Add);
    impl_binary_insn!(sub, BinaryOp::Sub);
    impl_binary_insn!(mul, BinaryOp::Mul);
    impl_binary_insn!(udiv, BinaryOp::Udiv);
    impl_binary_insn!(sdiv, BinaryOp::Sdiv);
    impl_binary_insn!(lt, BinaryOp::Lt);
    impl_binary_insn!(gt, BinaryOp::Gt);
    impl_binary_insn!(slt, BinaryOp::Slt);
    impl_binary_insn!(sgt, BinaryOp::Sgt);
    impl_binary_insn!(le, BinaryOp::Le);
    impl_binary_insn!(ge, BinaryOp::Ge);
    impl_binary_insn!(sle, BinaryOp::Sle);
    impl_binary_insn!(sge, BinaryOp::Sge);
    impl_binary_insn!(eq, BinaryOp::Eq);
    impl_binary_insn!(ne, BinaryOp::Ne);
    impl_binary_insn!(and, BinaryOp::And);
    impl_binary_insn!(or, BinaryOp::Or);

    impl_cast_insn!(sext, CastOp::Sext);
    impl_cast_insn!(zext, CastOp::Zext);
    impl_cast_insn!(trunc, CastOp::Trunc);

    /// Build memory load instruction.
    pub fn memory_load(&mut self, addr: Value) -> Value {
        let insn_data = InsnData::Load {
            args: [addr],
            loc: DataLocationKind::Memory,
        };
        self.insert_insn(insn_data).unwrap()
    }

    /// Build memory store instruction.
    pub fn memory_store(&mut self, addr: Value, data: Value) {
        let insn_data = InsnData::Store {
            args: [addr, data],
            loc: DataLocationKind::Memory,
        };
        self.insert_insn(insn_data);
    }

    /// Build storage load instruction.
    pub fn storage_load(&mut self, addr: Value) -> Value {
        let insn_data = InsnData::Load {
            args: [addr],
            loc: DataLocationKind::Storage,
        };
        self.insert_insn(insn_data).unwrap()
    }

    pub fn call(&mut self, func: FuncRef, args: &[Value]) -> Value {
        let sig = self.module_builder.funcs[func].sig.clone();
        let ret_ty = sig.ret_ty().clone();
        self.func_mut().callees.insert(func, sig);

        let insn_data = InsnData::Call {
            func,
            args: args.into(),
            ret_ty,
        };
        self.insert_insn(insn_data).unwrap()
    }

    /// Build storage store instruction.
    pub fn storage_store(&mut self, addr: Value, data: Value) {
        let insn_data = InsnData::Store {
            args: [addr, data],
            loc: DataLocationKind::Storage,
        };
        self.insert_insn(insn_data);
    }

    /// Build alloca instruction.
    pub fn alloca(&mut self, ty: Type) -> Value {
        let insn_data = InsnData::Alloca { ty };
        self.insert_insn(insn_data).unwrap()
    }

    pub fn jump(&mut self, dest: Block) {
        debug_assert!(!self.ssa_builder.is_sealed(dest));
        let insn_data = InsnData::Jump {
            code: JumpOp::Jump,
            dests: [dest],
        };

        let pred = self.cursor().block();
        self.ssa_builder.append_pred(dest, pred.unwrap());
        self.insert_insn(insn_data);
    }

    pub fn br_table(&mut self, cond: Value, default: Option<Block>, table: &[(Value, Block)]) {
        if cfg!(debug_assertions) {
            if let Some(default) = default {
                debug_assert!(!self.ssa_builder.is_sealed(default))
            }

            for (_, dest) in table {
                debug_assert!(!self.ssa_builder.is_sealed(*dest));
            }
        }

        let mut args = SmallVec::new();
        let mut blocks = SmallVec::new();
        args.push(cond);
        for (value, block) in table {
            args.push(*value);
            blocks.push(*block);
        }

        let insn_data = InsnData::BrTable {
            args,
            default,
            table: blocks,
        };
        let block = self.cursor().block().unwrap();

        if let Some(default) = default {
            self.ssa_builder.append_pred(default, block);
        }
        for (_, dest) in table {
            self.ssa_builder.append_pred(*dest, block);
        }
        self.insert_insn(insn_data);
    }

    pub fn br(&mut self, cond: Value, then: Block, else_: Block) {
        debug_assert!(!self.ssa_builder.is_sealed(then));
        debug_assert!(!self.ssa_builder.is_sealed(else_));

        let insn_data = InsnData::Branch {
            args: [cond],
            dests: [then, else_],
        };

        let block = self.cursor().block().unwrap();
        self.ssa_builder.append_pred(then, block);
        self.ssa_builder.append_pred(else_, block);
        self.insert_insn(insn_data);
    }

    pub fn ret(&mut self, args: Option<Value>) {
        let insn_data = InsnData::Return { args };
        self.insert_insn(insn_data);
    }

    pub fn phi(&mut self, args: &[(Value, Block)]) -> Value {
        let ty = self.func().dfg.value_ty(args[0].0).clone();
        let insn_data = InsnData::Phi {
            values: args.iter().map(|(val, _)| *val).collect(),
            blocks: args.iter().map(|(_, block)| *block).collect(),
            ty,
        };
        self.insert_insn(insn_data).unwrap()
    }

    pub fn append_phi_arg(&mut self, phi_value: Value, value: Value, block: Block) {
        let insn = self
            .func()
            .dfg
            .value_insn(phi_value)
            .expect("value must be the result of phi function");
        debug_assert!(
            self.func().dfg.is_phi(insn),
            "value must be the result of phi function"
        );
        self.func_mut().dfg.append_phi_arg(insn, value, block);
    }

    pub fn declare_var(&mut self, ty: Type) -> Variable {
        self.ssa_builder.declare_var(ty)
    }

    pub fn use_var(&mut self, var: Variable) -> Value {
        let block = self.cursor().block().unwrap();
        self.ssa_builder.use_var(
            &mut self.module_builder.funcs[self.func_ref],
            &self.module_builder.isa,
            var,
            block,
        )
    }

    pub fn def_var(&mut self, var: Variable, value: Value) {
        debug_assert_eq!(
            self.module_builder.funcs[self.func_ref].dfg.value_ty(value),
            self.ssa_builder.var_ty(var)
        );

        let block = self.cursor().block().unwrap();
        self.ssa_builder.def_var(var, value, block);
    }

    pub fn seal_block(&mut self) {
        let block = self.cursor().block().unwrap();
        self.ssa_builder.seal_block(
            &mut self.module_builder.funcs[self.func_ref],
            &self.module_builder.isa,
            block,
        );
    }

    pub fn seal_all(&mut self) {
        self.ssa_builder.seal_all(
            &mut self.module_builder.funcs[self.func_ref],
            &self.module_builder.isa,
        );
    }

    pub fn is_sealed(&self, block: Block) -> bool {
        self.ssa_builder.is_sealed(block)
    }

    pub fn finish(self) -> FuncRef {
        if cfg!(debug_assertions) {
            for block in self.func().layout.iter_block() {
                debug_assert!(self.is_sealed(block), "all blocks must be sealed");
            }
        }
        self.func_ref
    }

    pub fn type_of(&self, value: Value) -> &Type {
        self.func().dfg.value_ty(value)
    }

    pub fn args(&self) -> &[Value] {
        &self.func().arg_values
    }

    pub fn pointer_type(&self) -> Type {
        self.module_builder.isa.type_provider().pointer_type()
    }

    pub fn address_type(&self) -> Type {
        self.module_builder.isa.type_provider().address_type()
    }

    pub fn balance_type(&self) -> Type {
        self.module_builder.isa.type_provider().balance_type()
    }

    pub fn gas_type(&self) -> Type {
        self.module_builder.isa.type_provider().gas_type()
    }

    fn cursor(&mut self) -> InsnInserter {
        InsnInserter::new(
            &mut self.module_builder.funcs[self.func_ref],
            &self.module_builder.isa,
            self.loc,
        )
    }

    fn insert_insn(&mut self, insn_data: InsnData) -> Option<Value> {
        let mut cursor = self.cursor();
        let insn = cursor.insert_insn_data(insn_data);
        let result = cursor.make_result(insn);
        if let Some(result) = result {
            cursor.attach_result(insn, result);
        }
        self.loc = CursorLocation::At(insn);
        result
    }
    fn func(&self) -> &Function {
        &self.module_builder.funcs[self.func_ref]
    }

    fn func_mut(&mut self) -> &mut Function {
        &mut self.module_builder.funcs[self.func_ref]
    }
}

#[cfg(test)]
mod tests {
    use super::{super::test_util::*, *};

    #[test]
    fn entry_block() {
        let mut test_module_builder = TestModuleBuilder::new();
        let mut builder = test_module_builder.func_builder(&[], &Type::Void);

        let b0 = builder.append_block();
        builder.switch_to_block(b0);
        let v0 = builder.make_imm_value(1i8);
        let v1 = builder.make_imm_value(2i8);
        let v2 = builder.add(v0, v1);
        builder.sub(v2, v0);
        builder.ret(None);

        builder.seal_all();
        let func_ref = builder.finish();

        let module = test_module_builder.build();
        assert_eq!(
            dump_func(&module.funcs[func_ref]),
            "func public %test_func() -> void:
    block0:
        v2.i8 = add 1.i8 2.i8;
        v3.i8 = sub v2 1.i8;
        return;

"
        );
    }

    #[test]
    fn entry_block_with_args() {
        let mut test_module_builder = TestModuleBuilder::new();
        let mut builder = test_module_builder.func_builder(&[Type::I32, Type::I64], &Type::Void);

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let args = builder.args();
        let (arg0, arg1) = (args[0], args[1]);
        assert_eq!(args.len(), 2);
        let v3 = builder.sext(arg0, Type::I64);
        builder.mul(v3, arg1);
        builder.ret(None);

        builder.seal_all();
        let func_ref = builder.finish();

        let module = test_module_builder.build();
        assert_eq!(
            dump_func(&module.funcs[func_ref]),
            "func public %test_func(v0.i32, v1.i64) -> void:
    block0:
        v2.i64 = sext v0;
        v3.i64 = mul v2 v1;
        return;

"
        );
    }

    #[test]
    fn entry_block_with_return() {
        let mut test_module_builder = TestModuleBuilder::new();
        let mut builder = test_module_builder.func_builder(&[], &Type::I32);

        let entry_block = builder.append_block();

        builder.switch_to_block(entry_block);
        let v0 = builder.make_imm_value(1i32);
        builder.ret(Some(v0));
        builder.seal_all();
        let func_ref = builder.finish();

        let module = test_module_builder.build();
        assert_eq!(
            dump_func(&module.funcs[func_ref]),
            "func public %test_func() -> i32:
    block0:
        return 1.i32;

"
        );
    }

    #[test]
    fn then_else_merge_block() {
        let mut test_module_builder = TestModuleBuilder::new();
        let mut builder = test_module_builder.func_builder(&[Type::I64], &Type::Void);

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        builder.br(arg0, then_block, else_block);

        builder.switch_to_block(then_block);
        let v1 = builder.make_imm_value(1i64);
        builder.jump(merge_block);

        builder.switch_to_block(else_block);
        let v2 = builder.make_imm_value(2i64);
        builder.jump(merge_block);

        builder.switch_to_block(merge_block);
        let v3 = builder.phi(&[(v1, then_block), (v2, else_block)]);
        builder.add(v3, arg0);
        builder.ret(None);

        builder.seal_all();
        let func_ref = builder.finish();

        let module = test_module_builder.build();
        assert_eq!(
            dump_func(&module.funcs[func_ref]),
            "func public %test_func(v0.i64) -> void:
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v3.i64 = phi (1.i64 block1) (2.i64 block2);
        v4.i64 = add v3 v0;
        return;

"
        );
    }
}
