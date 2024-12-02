use super::{
    ssa::{SsaBuilder, Variable},
    ModuleBuilder,
};
use crate::{
    func_cursor::{CursorLocation, FuncCursor},
    module::{FuncRef, ModuleCtx},
    BlockId, Function, GlobalVariableRef, Immediate, Inst, InstId, InstSetBase, Type, Value,
    ValueId,
};

pub struct FunctionBuilder<C> {
    pub module_builder: ModuleBuilder,
    pub func: Function,
    func_ref: FuncRef,
    pub cursor: C,
    ssa_builder: SsaBuilder,
}

impl<C> FunctionBuilder<C>
where
    C: FuncCursor,
{
    pub fn new(module_builder: ModuleBuilder, func_ref: FuncRef, cursor: C) -> Self {
        let func = module_builder
            .ctx
            .func_sig(func_ref, |sig| Function::new(&module_builder.ctx, sig));

        Self {
            module_builder,
            func,
            func_ref,
            cursor,
            ssa_builder: SsaBuilder::new(),
        }
    }

    pub fn finish(self) {
        if cfg!(debug_assertions) {
            for block in self.func.layout.iter_block() {
                debug_assert!(
                    self.is_sealed(block),
                    "all blocks must be sealed: `{block}` is not sealed"
                );
            }
        }

        let Self {
            module_builder,
            func,
            func_ref,
            ..
        } = self;

        module_builder.func_store.update(func_ref, func);
    }

    pub fn append_parameter(&mut self, ty: Type) -> ValueId {
        let idx = self.func.arg_values.len();

        let value_data = self.func.dfg.make_arg_value(ty, idx);
        let value = self.func.dfg.make_value(value_data);
        self.func.arg_values.push(value);
        value
    }

    pub fn append_block(&mut self) -> BlockId {
        let block = self.cursor.make_block(&mut self.func);
        self.cursor.append_block(&mut self.func, block);
        block
    }

    pub fn make_block(&mut self) -> BlockId {
        self.cursor.make_block(&mut self.func)
    }

    pub fn append_phi_arg(&mut self, phi_res: ValueId, value: ValueId, block: BlockId) {
        let phi_inst = self
            .func
            .dfg
            .value_inst(phi_res)
            .expect("`phi_res` should be a result of phi inst");

        self.func.dfg.append_phi_arg(phi_inst, value, block);
    }

    pub fn switch_to_block(&mut self, block: BlockId) {
        self.cursor.set_location(CursorLocation::BlockBottom(block));
    }

    pub fn make_imm_value<Imm>(&mut self, imm: Imm) -> ValueId
    where
        Imm: Into<Immediate>,
    {
        self.func.dfg.make_imm_value(imm)
    }

    pub fn make_undef_value(&mut self, ty: Type) -> ValueId {
        self.func.dfg.make_undef_value(ty)
    }

    /// Return pointer value to the global variable.
    pub fn make_global_value(&mut self, gv: GlobalVariableRef) -> ValueId {
        self.func.dfg.make_global_value(gv)
    }

    pub fn ptr_type(&mut self, ty: Type) -> Type {
        self.module_builder.ptr_type(ty)
    }

    pub fn declare_array_type(&mut self, elem: Type, len: usize) -> Type {
        self.module_builder.declare_array_type(elem, len)
    }

    pub fn declare_struct_type(&mut self, name: &str, fields: &[Type], packed: bool) -> Type {
        self.module_builder
            .declare_struct_type(name, fields, packed)
    }

    /// Inserts an instruction into the current position and returns a `ValueId`
    /// for the result.
    ///
    /// # Parameters
    /// - `inst`: The instruction to insert, which must implement the `Inst`
    ///   trait.
    /// - `ret_ty`: The return type of the instruction. A result value will be
    ///   created with this type and associated with the instruction.
    ///
    /// # Returns
    /// - `ValueId`: The ID of the result value associated with the inserted
    ///   instruction.
    pub fn insert_inst<I: Inst>(&mut self, inst: I, ret_ty: Type) -> ValueId {
        let inst_id = self.cursor.insert_inst_data(&mut self.func, inst);
        self.append_pred(inst_id);

        let result = Value::Inst {
            inst: inst_id,
            ty: ret_ty,
        };
        let result = self.func.dfg.make_value(result);
        self.func.dfg.attach_result(inst_id, result);

        self.cursor.set_location(CursorLocation::At(inst_id));
        result
    }

    pub fn insert_inst_dyn(&mut self, inst: Box<dyn Inst>, ret_ty: Type) -> ValueId {
        let inst_id = self.cursor.insert_inst_data_dyn(&mut self.func, inst);
        self.append_pred(inst_id);

        let result = Value::Inst {
            inst: inst_id,
            ty: ret_ty,
        };
        let result = self.func.dfg.make_value(result);
        self.func.dfg.attach_result(inst_id, result);

        self.cursor.set_location(CursorLocation::At(inst_id));
        result
    }

    pub fn insert_inst_with<F, I>(&mut self, f: F, ret_ty: Type) -> ValueId
    where
        F: FnOnce() -> I,
        I: Inst,
    {
        let i = f();
        self.insert_inst(i, ret_ty)
    }

    /// Inserts an instruction into the function without creating a result value
    /// (i.e., for instructions that have no return type).
    ///
    /// Please refer to [`Self::insert_inst`] if the instruction has a result.
    ///
    /// # Parameters
    /// - `inst`: The instruction to insert, which must implement the `Inst`
    ///   trait.
    pub fn insert_inst_no_result<I: Inst>(&mut self, inst: I) {
        let inst_id = self.cursor.insert_inst_data(&mut self.func, inst);
        self.append_pred(inst_id);
        self.cursor.set_location(CursorLocation::At(inst_id));
    }

    pub fn insert_inst_no_result_dyn(&mut self, inst: Box<dyn Inst>) {
        let inst_id = self.cursor.insert_inst_data_dyn(&mut self.func, inst);
        self.append_pred(inst_id);
        self.cursor.set_location(CursorLocation::At(inst_id));
    }

    pub fn insert_inst_no_result_with<F, I>(&mut self, f: F)
    where
        F: FnOnce() -> I,
        I: Inst,
    {
        let i = f();
        self.insert_inst_no_result(i);
    }

    pub fn declare_var(&mut self, ty: Type) -> Variable {
        self.ssa_builder.declare_var(ty)
    }

    pub fn use_var(&mut self, var: Variable) -> ValueId {
        let block = self.cursor.block(&self.func).unwrap();
        self.ssa_builder.use_var(&mut self.func, var, block)
    }

    pub fn def_var(&mut self, var: Variable, value: ValueId) {
        debug_assert_eq!(self.func.dfg.value_ty(value), self.ssa_builder.var_ty(var));

        let block = self.cursor.block(&self.func).unwrap();
        self.ssa_builder.def_var(var, value, block);
    }

    pub fn current_block(&self) -> Option<BlockId> {
        self.cursor.block(&self.func)
    }

    pub fn last_inst(&self) -> Option<InstId> {
        let current_block = self.current_block()?;
        self.last_inst_of(current_block)
    }

    pub fn last_inst_of(&self, block: BlockId) -> Option<InstId> {
        self.func.layout.last_inst_of(block)
    }

    pub fn is_terminator(&self, inst: InstId) -> bool {
        self.func.dfg.is_terminator(inst)
    }

    pub fn seal_block(&mut self) {
        let block = self.cursor.block(&self.func).unwrap();
        self.ssa_builder.seal_block(&mut self.func, block);
    }

    pub fn seal_all(&mut self) {
        self.ssa_builder.seal_all(&mut self.func);
    }

    pub fn is_sealed(&self, block: BlockId) -> bool {
        self.ssa_builder.is_sealed(block)
    }

    pub fn type_of(&self, value: ValueId) -> Type {
        self.func.dfg.value_ty(value)
    }

    pub fn args(&self) -> &[ValueId] {
        &self.func.arg_values
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.module_builder.inst_set()
    }

    pub fn ctx(&self) -> &ModuleCtx {
        &self.module_builder.ctx
    }

    fn append_pred(&mut self, inst_id: InstId) {
        let Some(branch_info) = self.func.dfg.branch_info(inst_id) else {
            return;
        };

        let current_block = self.cursor.block(&self.func).unwrap();
        for dest in branch_info.dests() {
            self.ssa_builder.append_pred(dest, current_block)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{super::test_util::*, *};
    use crate::{
        inst::{
            arith::{Add, Mul, Sub},
            cast::Sext,
            control_flow::{Br, Jump, Phi, Return},
        },
        isa::Isa,
    };

    #[test]
    fn entry_block() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        builder.switch_to_block(b0);
        let v0 = builder.make_imm_value(1i8);
        let v1 = builder.make_imm_value(2i8);
        let add = Add::new(is, v0, v1);
        let v2 = builder.insert_inst(add, Type::I8);

        let sub = Sub::new(is, v2, v0);
        builder.insert_inst(sub, Type::I8);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() -> unit {
    block0:
        v2.i8 = add 1.i8 2.i8;
        v3.i8 = sub v2 1.i8;
        return;
}
"
        );
    }

    #[test]
    fn entry_block_with_args() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32, Type::I64], Type::Unit);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let args = builder.args();
        let (arg0, arg1) = (args[0], args[1]);
        assert_eq!(args.len(), 2);
        let sext = Sext::new(is, arg0, Type::I64);
        let v3 = builder.insert_inst(sext, Type::I64);
        let mul = Mul::new(is, v3, arg1);
        builder.insert_inst(mul, Type::I64);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func(v0.i32, v1.i64) -> unit {
    block0:
        v2.i64 = sext v0 i64;
        v3.i64 = mul v2 v1;
        return;
}
"
        );
    }

    #[test]
    fn entry_block_with_return() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I32);
        let is = evm.inst_set();

        let entry_block = builder.append_block();

        builder.switch_to_block(entry_block);
        let v0 = builder.make_imm_value(1i32);
        let ret = Return::new(is, Some(v0));
        builder.insert_inst_no_result(ret);
        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() -> i32 {
    block0:
        return 1.i32;
}
"
        );
    }

    #[test]
    fn then_else_merge_block() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I64], Type::Unit);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        let br = Br::new(is, arg0, then_block, else_block);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(then_block);
        let v1 = builder.make_imm_value(1i64);
        let jump = Jump::new(is, merge_block);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(else_block);
        let v2 = builder.make_imm_value(2i64);
        let jump = Jump::new(is, merge_block);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(merge_block);
        let phi = Phi::new(is, vec![(v1, then_block), (v2, else_block)]);
        let v3 = builder.insert_inst(phi, Type::I64);
        let add = Add::new(is, v3, arg0);
        builder.insert_inst(add, Type::I64);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func(v0.i64) -> unit {
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
}
"
        );
    }
}
