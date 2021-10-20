// TODO: verifier.

use sonatina_codegen::ir::{
    function::{CursorLocation, FunctionCursor},
    insn::{BinaryOp, BranchOp, CastOp, ImmediateOp, InsnData, JumpOp},
    types::U256,
    Function, Signature,
};

use super::{ssa::SsaBuilder, Block, Type, Value, Variable};

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

macro_rules! impl_immediate_insn {
    ($name:ident, $code:path, $ty:ty) => {
        pub fn $name(&mut self, value: $ty) -> Value {
            let insn_data = InsnData::Immediate { code: $code(value) };

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

macro_rules! impl_branch_insn {
    ($name:ident, $code:path) => {
        pub fn $name(&mut self, dest: Block, cond: Value) {
            debug_assert!(!self.ssa_builder.is_sealed(dest));
            let insn_data = InsnData::Branch {
                code: $code,
                args: [cond],
                dest,
            };

            let pred = self.cursor().block();
            self.ssa_builder.append_pred(dest, pred.unwrap());
            self.insert_insn(insn_data);
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

    pub fn append_block(&mut self, name: &str) -> Block {
        self.cursor().append_block(name)
    }

    pub fn switch_to_block(&mut self, block: Block) {
        self.loc = CursorLocation::BlockBottom(block);
    }

    impl_immediate_insn!(imm_i8, ImmediateOp::I8, i8);
    impl_immediate_insn!(imm_i16, ImmediateOp::I16, i16);
    impl_immediate_insn!(imm_i32, ImmediateOp::I32, i32);
    impl_immediate_insn!(imm_i64, ImmediateOp::I64, i64);
    impl_immediate_insn!(imm_i128, ImmediateOp::I128, i128);
    impl_immediate_insn!(imm_u8, ImmediateOp::U8, u8);
    impl_immediate_insn!(imm_u16, ImmediateOp::U16, u16);
    impl_immediate_insn!(imm_u32, ImmediateOp::U32, u32);
    impl_immediate_insn!(imm_u64, ImmediateOp::U64, u64);
    impl_immediate_insn!(imm_u128, ImmediateOp::U128, u128);
    impl_immediate_insn!(imm_u256, ImmediateOp::U256, U256);

    impl_binary_insn!(add, BinaryOp::Add);
    impl_binary_insn!(sub, BinaryOp::Sub);
    impl_binary_insn!(mul, BinaryOp::Mul);
    impl_binary_insn!(div, BinaryOp::Div);
    impl_binary_insn!(lt, BinaryOp::Lt);
    impl_binary_insn!(gt, BinaryOp::Gt);
    impl_binary_insn!(slt, BinaryOp::Slt);
    impl_binary_insn!(sgt, BinaryOp::Sgt);
    impl_binary_insn!(eq, BinaryOp::Eq);
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
            dest,
        };

        let pred = self.cursor().block();
        self.ssa_builder.append_pred(dest, pred.unwrap());
        self.insert_insn(insn_data);
    }

    impl_branch_insn!(brz, BranchOp::Brz);
    impl_branch_insn!(brnz, BranchOp::Brnz);

    pub fn phi(&mut self, args: &[Value]) -> Value {
        debug_assert!(!args.is_empty());

        let ty = self.func.dfg.value_ty(args[0]).clone();
        let insn_data = InsnData::Phi {
            args: args.to_vec(),
            ty,
        };
        self.insert_insn(insn_data).unwrap()
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

    fn cursor(&mut self) -> FunctionCursor {
        FunctionCursor::new(&mut self.func, self.loc)
    }

    fn insert_insn(&mut self, insn_data: InsnData) -> Option<Value> {
        let (insn, value) = self.cursor().insert_insn(insn_data);
        self.loc = CursorLocation::At(insn);
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::*;

    #[test]
    fn entry_block() {
        let mut builder = func_builder(vec![], vec![]);

        let entry_block = builder.append_block("entry");
        builder.switch_to_block(entry_block);
        let v0 = builder.imm_i8(1);
        let v1 = builder.imm_i8(2);
        let v2 = builder.add(v0, v1);
        builder.sub(v2, v0);

        builder.seal_all();

        assert_eq!(
            dump_func(builder),
            "func %test_func():
    entry:
        %v0.i8 = imm.i8 1
        %v1.i8 = imm.i8 2
        %v2.i8 = add %v0.i8 %v1.i8
        %v3.i8 = sub %v2.i8 %v0.i8

"
        );
    }

    #[test]
    fn entry_block_with_args() {
        let mut builder = func_builder(vec![Type::I32, Type::I64], vec![]);

        let entry_block = builder.append_block("entry");
        builder.switch_to_block(entry_block);
        let args = builder.args();
        let (arg0, arg1) = (args[0], args[1]);
        assert_eq!(args.len(), 2);
        let v3 = builder.sext(arg0, Type::I64);
        builder.mul(v3, arg1);

        builder.seal_all();

        assert_eq!(
            dump_func(builder),
            "func %test_func(i32, i64):
    entry:
        %v2.i64 = sext %v0.i32
        %v3.i64 = mul %v2.i64 %v1.i64

"
        );
    }

    #[test]
    fn then_else_merge_block() {
        let mut builder = func_builder(vec![Type::I64], vec![]);

        let entry_block = builder.append_block("entry");
        let then_block = builder.append_block("then");
        let else_block = builder.append_block("else");
        let merge_block = builder.append_block("merge");

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        builder.brz(then_block, arg0);
        builder.jump(else_block);

        builder.switch_to_block(then_block);
        let v1 = builder.imm_i64(1);
        builder.jump(merge_block);

        builder.switch_to_block(else_block);
        let v2 = builder.imm_i64(2);
        builder.jump(merge_block);

        builder.switch_to_block(merge_block);
        let v3 = builder.phi(&[v1, v2]);
        builder.add(v3, arg0);

        builder.seal_all();

        assert_eq!(
            dump_func(builder),
            "func %test_func(i64):
    entry:
        brz %v0.i64 then
        jump else

    then:
        %v1.i64 = imm.i64 1
        jump merge

    else:
        %v2.i64 = imm.i64 2
        jump merge

    merge:
        %v3.i64 = phi %v1.i64 %v2.i64
        %v4.i64 = add %v3.i64 %v0.i64

"
        );
    }
}
