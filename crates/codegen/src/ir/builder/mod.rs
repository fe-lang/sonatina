mod ssa;

pub use ssa::Variable;

// TODO: verifier.

use crate::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{BinaryOp, CastOp, InsnData, JumpOp, UnaryOp},
    Immediate,
};

use crate::{Block, Function, Signature, Type, Value};

use ssa::SsaBuilder;

pub trait Context {
    fn hash_type(&self) -> Type;
    fn address_type(&self) -> Type;
    fn balance_type(&self) -> Type;
    fn gas_type(&self) -> Type;
}

pub struct FunctionBuilder {
    ctxt: Box<dyn Context>,
    func: Function,
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

impl FunctionBuilder {
    pub fn new(name: String, sig: Signature, ctxt: Box<dyn Context>) -> Self {
        let func = Function::new(name, sig);
        Self {
            ctxt,
            func,
            loc: CursorLocation::NoWhere,
            ssa_builder: SsaBuilder::default(),
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
        self.func.dfg.make_imm_value(imm)
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
    impl_binary_insn!(eq, BinaryOp::Eq);
    impl_binary_insn!(ne, BinaryOp::Ne);
    impl_binary_insn!(and, BinaryOp::And);
    impl_binary_insn!(or, BinaryOp::Or);

    impl_cast_insn!(sext, CastOp::Sext);
    impl_cast_insn!(zext, CastOp::Zext);
    impl_cast_insn!(trunc, CastOp::Trunc);

    pub fn load(&mut self, addr: Value, ty: Type) -> Value {
        let insn_data = InsnData::Load { args: [addr], ty };
        self.insert_insn(insn_data).unwrap()
    }

    pub fn store(&mut self, addr: Value, data: Value) {
        let insn_data = InsnData::Store { args: [addr, data] };
        self.insert_insn(insn_data);
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

    pub fn br(&mut self, cond: Value, then: Block, else_: Block) {
        debug_assert!(!self.ssa_builder.is_sealed(then));
        debug_assert!(!self.ssa_builder.is_sealed(else_));
        let insn_data = InsnData::Branch {
            args: [cond],
            dests: [then, else_],
        };

        let pred = self.cursor().block();
        self.ssa_builder.append_pred(then, pred.unwrap());
        self.ssa_builder.append_pred(else_, pred.unwrap());
        self.insert_insn(insn_data);
    }

    pub fn ret(&mut self, args: &[Value]) {
        let insn_data = InsnData::Return { args: args.into() };
        self.insert_insn(insn_data);
    }

    pub fn phi(&mut self, args: &[(Value, Block)]) -> Value {
        let ty = self.func.dfg.value_ty(args[0].0).clone();
        let insn_data = InsnData::Phi {
            values: args.iter().map(|(val, _)| *val).collect(),
            blocks: args.iter().map(|(_, block)| *block).collect(),
            ty,
        };
        self.insert_insn(insn_data).unwrap()
    }

    pub fn append_phi_arg(&mut self, phi_value: Value, value: Value, block: Block) {
        let insn = self
            .func
            .dfg
            .value_insn(phi_value)
            .expect("value must be the result of phi function");
        debug_assert!(
            self.func.dfg.is_phi(insn),
            "value must be the result of phi function"
        );
        self.func.dfg.append_phi_arg(insn, value, block);
    }

    pub fn declare_var(&mut self, ty: Type) -> Variable {
        self.ssa_builder.declare_var(ty)
    }

    pub fn use_var(&mut self, var: Variable) -> Value {
        let block = self.cursor().block().unwrap();
        self.ssa_builder.use_var(&mut self.func, var, block)
    }

    pub fn def_var(&mut self, var: Variable, value: Value) {
        debug_assert_eq!(self.func.dfg.value_ty(value), self.ssa_builder.var_ty(var));

        let block = self.cursor().block().unwrap();
        self.ssa_builder.def_var(var, value, block);
    }

    pub fn seal_block(&mut self) {
        let block = self.cursor().block().unwrap();
        self.ssa_builder.seal_block(&mut self.func, block);
    }

    pub fn seal_all(&mut self) {
        self.ssa_builder.seal_all(&mut self.func);
    }

    pub fn is_sealed(&self, block: Block) -> bool {
        self.ssa_builder.is_sealed(block)
    }

    pub fn build(self) -> Function {
        if cfg!(debug_assertions) {
            for block in self.func.layout.iter_block() {
                debug_assert!(self.is_sealed(block), "all blocks must be sealed");
            }
        }

        self.func
    }

    pub fn type_of(&self, value: Value) -> &Type {
        self.func.dfg.value_ty(value)
    }

    pub fn args(&self) -> &[Value] {
        &self.func.arg_values
    }

    pub fn hash_type(&self) -> Type {
        self.ctxt.hash_type()
    }

    pub fn address_type(&self) -> Type {
        self.ctxt.address_type()
    }

    pub fn balance_type(&self) -> Type {
        self.ctxt.balance_type()
    }

    pub fn gas_type(&self) -> Type {
        self.ctxt.gas_type()
    }

    fn cursor(&mut self) -> InsnInserter {
        InsnInserter::new(&mut self.func, self.loc)
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
}

#[cfg(test)]
mod tests {
    use super::test_util::*;
    use super::*;

    #[test]
    fn entry_block() {
        let mut builder = func_builder(&[], &[]);

        let b0 = builder.append_block();
        builder.switch_to_block(b0);
        let v0 = builder.make_imm_value(1i8);
        let v1 = builder.make_imm_value(2i8);
        let v2 = builder.add(v0, v1);
        builder.sub(v2, v0);
        builder.ret(&[]);

        builder.seal_all();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func():
    block0:
        v2.i8 = add 1.i8 2.i8;
        v3.i8 = sub v2 1.i8;
        return;

"
        );
    }

    #[test]
    fn entry_block_with_args() {
        let mut builder = func_builder(&[Type::I32, Type::I64], &[]);

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let args = builder.args();
        let (arg0, arg1) = (args[0], args[1]);
        assert_eq!(args.len(), 2);
        let v3 = builder.sext(arg0, Type::I64);
        builder.mul(v3, arg1);
        builder.ret(&[]);

        builder.seal_all();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func(v0.i32, v1.i64):
    block0:
        v2.i64 = sext v0;
        v3.i64 = mul v2 v1;
        return;

"
        );
    }

    #[test]
    fn entry_block_with_return() {
        let mut builder = func_builder(&[], &[Type::I32, Type::I64]);

        let entry_block = builder.append_block();

        builder.switch_to_block(entry_block);
        let v0 = builder.make_imm_value(1i32);
        let v1 = builder.make_imm_value(2i64);
        builder.ret(&[v0, v1]);
        builder.seal_all();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func() -> i32, i64:
    block0:
        return 1.i32 2.i64;

"
        );
    }

    #[test]
    fn then_else_merge_block() {
        let mut builder = func_builder(&[Type::I64], &[]);

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
        builder.ret(&[]);

        builder.seal_all();

        assert_eq!(
            dump_func(&builder.build()),
            "func %test_func(v0.i64):
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

#[cfg(test)]
pub(crate) mod test_util {
    use super::*;

    use crate::ir::ir_writer::FuncWriter;

    use crate::{Function, Signature, Type};

    pub struct TestContext {}

    impl Context for TestContext {
        fn hash_type(&self) -> Type {
            Type::I256
        }

        fn address_type(&self) -> Type {
            Type::make_array(Type::I8, 20)
        }

        fn balance_type(&self) -> Type {
            Type::I256
        }

        fn gas_type(&self) -> Type {
            Type::I256
        }
    }

    pub(crate) fn func_builder(args: &[Type], rets: &[Type]) -> FunctionBuilder {
        let sig = Signature::new(args, rets);
        let ctxt = TestContext {};
        FunctionBuilder::new("test_func".into(), sig, Box::new(ctxt))
    }

    pub(crate) fn dump_func(func: &Function) -> String {
        let mut writer = FuncWriter::new(func);
        writer.dump_string().unwrap()
    }
}
