use super::{
    ModuleBuilder,
    ssa::{SsaBuilder, Variable},
};
use crate::{
    BlockId, Function, GlobalVariableRef, Immediate, Inst, InstId, InstSetBase, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor},
    inst::{
        arith::{Saddo, Smulo, Snego, Ssubo, Uaddo, Umulo, Usubo},
        control_flow,
        evm::{EvmSdivo, EvmSmodo, EvmUdivo, EvmUmodo},
    },
    module::{FuncRef, ModuleCtx},
};
use smallvec::SmallVec;

pub struct FunctionBuilder<C> {
    pub module_builder: ModuleBuilder,
    pub func: Function,
    pub func_ref: FuncRef,
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

        let value = self.ssa_builder.resolve_alias(value);
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

    pub fn insert_inst_results<I: Inst>(
        &mut self,
        inst: I,
        ret_tys: &[Type],
    ) -> SmallVec<[ValueId; 2]> {
        self.insert_inst_dyn_results(Box::new(inst), ret_tys)
    }

    pub fn insert_inst_dyn_results(
        &mut self,
        inst: Box<dyn Inst>,
        ret_tys: &[Type],
    ) -> SmallVec<[ValueId; 2]> {
        let mut inst = inst;
        inst.for_each_value_mut(&mut |v| {
            *v = self.ssa_builder.resolve_alias(*v);
        });

        let inst_id = self.cursor.insert_inst_data_dyn(&mut self.func, inst);
        self.append_pred(inst_id);
        let results = self.cursor.make_results(&mut self.func, inst_id, ret_tys);
        self.cursor
            .attach_results(&mut self.func, inst_id, &results);

        self.cursor.set_location(CursorLocation::At(inst_id));
        results
    }

    /// Inserts an instruction into the current position and returns a `ValueId`
    /// for the result.
    ///
    /// This is a strict single-result convenience wrapper over
    /// [`Self::insert_inst_results`].
    pub fn insert_inst<I: Inst>(&mut self, inst: I, ret_ty: Type) -> ValueId {
        let results = self.insert_inst_results(inst, &[ret_ty]);
        debug_assert_eq!(results.len(), 1);
        results[0]
    }

    pub fn insert_inst_dyn(&mut self, inst: Box<dyn Inst>, ret_ty: Type) -> ValueId {
        let results = self.insert_inst_dyn_results(inst, &[ret_ty]);
        debug_assert_eq!(results.len(), 1);
        results[0]
    }

    pub fn insert_inst_results_with<F, I>(
        &mut self,
        f: F,
        ret_tys: &[Type],
    ) -> SmallVec<[ValueId; 2]>
    where
        F: FnOnce() -> I,
        I: Inst,
    {
        self.insert_inst_results(f(), ret_tys)
    }

    pub fn insert_inst_with<F, I>(&mut self, f: F, ret_ty: Type) -> ValueId
    where
        F: FnOnce() -> I,
        I: Inst,
    {
        let results = self.insert_inst_results_with(f, &[ret_ty]);
        debug_assert_eq!(results.len(), 1);
        results[0]
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
        let _ = self.insert_inst_results(inst, &[]);
    }

    pub fn insert_inst_no_result_dyn(&mut self, inst: Box<dyn Inst>) {
        let _ = self.insert_inst_dyn_results(inst, &[]);
    }

    pub fn insert_inst_no_result_with<F, I>(&mut self, f: F)
    where
        F: FnOnce() -> I,
        I: Inst,
    {
        let i = f();
        self.insert_inst_no_result(i);
    }

    fn insert_checked_results<I: Inst>(&mut self, inst: I, value_ty: Type) -> [ValueId; 2] {
        let results = self.insert_inst_results(inst, &[value_ty, Type::I1]);
        debug_assert_eq!(results.len(), 2);
        [results[0], results[1]]
    }

    fn insert_checked_binary<I: Inst>(
        &mut self,
        inst: I,
        lhs: ValueId,
        rhs: ValueId,
    ) -> [ValueId; 2] {
        let lhs_ty = self.type_of(lhs);
        let rhs_ty = self.type_of(rhs);
        assert_eq!(
            lhs_ty, rhs_ty,
            "checked binary operands must have the same type"
        );
        assert!(
            lhs_ty.is_integral(),
            "checked binary operands must be integral"
        );
        self.insert_checked_results(inst, lhs_ty)
    }

    fn insert_checked_unary<I: Inst>(&mut self, inst: I, arg: ValueId) -> [ValueId; 2] {
        let arg_ty = self.type_of(arg);
        assert!(
            arg_ty.is_integral(),
            "checked unary operand must be integral"
        );
        self.insert_checked_results(inst, arg_ty)
    }

    pub fn insert_uaddo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            Uaddo::new(
                self.inst_set()
                    .has_uaddo()
                    .expect("target ISA must support `uaddo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_saddo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            Saddo::new(
                self.inst_set()
                    .has_saddo()
                    .expect("target ISA must support `saddo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_usubo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            Usubo::new(
                self.inst_set()
                    .has_usubo()
                    .expect("target ISA must support `usubo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_ssubo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            Ssubo::new(
                self.inst_set()
                    .has_ssubo()
                    .expect("target ISA must support `ssubo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_umulo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            Umulo::new(
                self.inst_set()
                    .has_umulo()
                    .expect("target ISA must support `umulo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_smulo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            Smulo::new(
                self.inst_set()
                    .has_smulo()
                    .expect("target ISA must support `smulo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_snego(&mut self, arg: ValueId) -> [ValueId; 2] {
        self.insert_checked_unary(
            Snego::new(
                self.inst_set()
                    .has_snego()
                    .expect("target ISA must support `snego`"),
                arg,
            ),
            arg,
        )
    }

    pub fn insert_evm_udivo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            EvmUdivo::new(
                self.inst_set()
                    .has_evm_udivo()
                    .expect("target ISA must support `evm_udivo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_evm_sdivo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            EvmSdivo::new(
                self.inst_set()
                    .has_evm_sdivo()
                    .expect("target ISA must support `evm_sdivo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_evm_umodo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            EvmUmodo::new(
                self.inst_set()
                    .has_evm_umodo()
                    .expect("target ISA must support `evm_umodo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_evm_smodo(&mut self, lhs: ValueId, rhs: ValueId) -> [ValueId; 2] {
        self.insert_checked_binary(
            EvmSmodo::new(
                self.inst_set()
                    .has_evm_smodo()
                    .expect("target ISA must support `evm_smodo`"),
                lhs,
                rhs,
            ),
            lhs,
            rhs,
        )
    }

    pub fn insert_call_results(
        &mut self,
        callee: FuncRef,
        args: SmallVec<[ValueId; 8]>,
    ) -> SmallVec<[ValueId; 2]> {
        let ret_tys = self
            .module_builder
            .sig(callee, |sig| sig.ret_tys().to_vec());
        let call = control_flow::Call::new(
            self.inst_set()
                .has_call()
                .expect("target ISA must support `call`"),
            callee,
            args,
        );
        self.insert_inst_results(call, &ret_tys)
    }

    pub fn insert_call(
        &mut self,
        callee: FuncRef,
        args: SmallVec<[ValueId; 8]>,
    ) -> Option<ValueId> {
        let results = self.insert_call_results(callee, args);
        assert!(
            results.len() <= 1,
            "insert_call called on multi-return callee"
        );
        results.first().copied()
    }

    pub fn insert_return_values(&mut self, values: &[ValueId]) {
        self.insert_inst_no_result(control_flow::Return::new(
            self.inst_set()
                .has_return()
                .expect("target ISA must support `return`"),
            SmallVec::from_slice(values).into(),
        ));
    }

    pub fn insert_return(&mut self, value: ValueId) {
        self.insert_inst_no_result(control_flow::Return::new_single(
            self.inst_set()
                .has_return()
                .expect("target ISA must support `return`"),
            value,
        ));
    }

    pub fn insert_return_unit(&mut self) {
        self.insert_inst_no_result(control_flow::Return::new_unit(
            self.inst_set()
                .has_return()
                .expect("target ISA must support `return`"),
        ));
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
    use smallvec::smallvec;

    use super::{super::test_util::*, *};
    use crate::{
        I256, Immediate, Linkage, Signature, Value,
        inst::{
            arith::{Add, Mul, Sub, Uaddo},
            cast::Sext,
            control_flow::{Br, Jump, Phi, Return},
            evm::EvmRevert,
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
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
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
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func(v0.i32, v1.i64) {
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
        let ret = Return::new_single(is, v0);
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
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func(v0.i64) {
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

    #[test]
    fn insert_inst_results_tracks_result_order() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32, Type::I32], Type::Unit);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);

        let args = builder.args();
        let results =
            builder.insert_inst_results(Uaddo::new(is, args[0], args[1]), &[Type::I32, Type::I1]);
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        assert_eq!(results.len(), 2);
        let inst = builder.func.dfg.value_inst(results[0]).unwrap();
        assert_eq!(builder.func.dfg.inst_results(inst), results.as_slice());
        assert_eq!(
            builder.func.dfg.value_inst_result(results[0]),
            Some((inst, 0))
        );
        assert_eq!(
            builder.func.dfg.value_inst_result(results[1]),
            Some((inst, 1))
        );

        match builder.func.dfg.value(results[0]) {
            Value::Inst {
                inst: owner,
                result_idx,
                ty,
            } => {
                assert_eq!(*owner, inst);
                assert_eq!(*result_idx, 0);
                assert_eq!(*ty, Type::I32);
            }
            other => panic!("unexpected first result value: {other:?}"),
        }

        match builder.func.dfg.value(results[1]) {
            Value::Inst {
                inst: owner,
                result_idx,
                ty,
            } => {
                assert_eq!(*owner, inst);
                assert_eq!(*result_idx, 1);
                assert_eq!(*ty, Type::I1);
            }
            other => panic!("unexpected second result value: {other:?}"),
        }
    }

    #[test]
    fn insert_call_handles_unit_single_and_multi_return_callees() {
        let mb = test_module_builder();
        let unit = mb
            .declare_function(Signature::new_unit("unit", Linkage::Private, &[Type::I32]))
            .unwrap();
        let single = mb
            .declare_function(Signature::new_single(
                "single",
                Linkage::Private,
                &[Type::I32],
                Type::I32,
            ))
            .unwrap();
        let pair = mb
            .declare_function(Signature::new(
                "pair",
                Linkage::Private,
                &[Type::I32],
                &[Type::I32, Type::I1],
            ))
            .unwrap();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32], Type::Unit);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let arg = builder.args()[0];

        assert_eq!(builder.insert_call(unit, smallvec![arg]), None);
        assert!(builder.insert_call(single, smallvec![arg]).is_some());

        let multi_return = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = builder.insert_call(pair, smallvec![arg]);
        }));
        assert!(multi_return.is_err(), "multi-return insert_call must panic");

        builder.insert_inst_no_result(Return::new_unit(is));
    }

    #[test]
    fn checked_overflow_helpers_infer_result_types() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256, Type::I256], Type::Unit);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        builder.switch_to_block(entry_block);
        let lhs = builder.args()[0];
        let rhs = builder.args()[1];

        let checked_results = [
            builder.insert_uaddo(lhs, rhs),
            builder.insert_saddo(lhs, rhs),
            builder.insert_usubo(lhs, rhs),
            builder.insert_ssubo(lhs, rhs),
            builder.insert_umulo(lhs, rhs),
            builder.insert_smulo(lhs, rhs),
            builder.insert_snego(lhs),
            builder.insert_evm_udivo(lhs, rhs),
            builder.insert_evm_sdivo(lhs, rhs),
            builder.insert_evm_umodo(lhs, rhs),
            builder.insert_evm_smodo(lhs, rhs),
        ];
        builder.insert_inst_no_result(Return::new_unit(is));

        for [value, overflow] in checked_results {
            assert_eq!(builder.type_of(value), Type::I256);
            assert_eq!(builder.type_of(overflow), Type::I1);
            let inst = builder.func.dfg.value_inst(value).unwrap();
            assert_eq!(builder.func.dfg.value_inst_result(value), Some((inst, 0)));
            assert_eq!(
                builder.func.dfg.value_inst_result(overflow),
                Some((inst, 1))
            );
        }
    }

    #[test]
    fn checked_add_can_branch_to_evm_revert_on_overflow() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256, Type::I256], Type::I256);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let overflow_block = builder.append_block();
        let ok_block = builder.append_block();

        builder.switch_to_block(entry);
        let lhs = builder.args()[0];
        let rhs = builder.args()[1];
        let [sum, overflow] = builder.insert_uaddo(lhs, rhs);
        builder.insert_inst_no_result(Br::new(is, overflow, overflow_block, ok_block));

        builder.switch_to_block(overflow_block);
        let zero = builder.make_imm_value(Immediate::from_i256(I256::from(0), Type::I256));
        builder.insert_inst_no_result(EvmRevert::new(is, zero, zero));

        builder.switch_to_block(ok_block);
        builder.insert_return(sum);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func(v0.i256, v1.i256) -> i256 {
    block0:
        (v2.i256, v3.i1) = uaddo v0 v1;
        br v3 block1 block2;

    block1:
        evm_revert 0.i256 0.i256;

    block2:
        return v2;
}
"
        );
    }
}
