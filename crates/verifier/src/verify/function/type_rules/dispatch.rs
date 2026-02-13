use macros::inst_prop;
use rustc_hash::FxHashSet;
use sonatina_ir::{
    Inst, InstId, Type, ValueId,
    inst::{
        arith, cast, cmp,
        control_flow::{self},
        data, evm, logic,
    },
    types::CompoundType,
};

use crate::{
    diagnostic::{Diagnostic, DiagnosticCode},
    verify::type_utils::{is_integral_or_pointer, is_pointer_ty},
};

use super::FunctionVerifier;

#[inst_prop]
pub(super) trait VerifyInst {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId);

    fn actual_arity(&self) -> Option<usize> {
        None
    }

    type Members = All;
}

macro_rules! impl_unary_integral_same_rule {
    ($($ty:ty => $opname:literal),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_unary_integral_same(inst_id, *self.arg(), $opname);
                }
            }
        )+
    };
}

impl_unary_integral_same_rule!(
    arith::Neg => "neg",
    logic::Not => "not",
);

macro_rules! impl_binary_integral_same_rule {
    ($($ty:ty => $opname:literal),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_binary_integral_same(inst_id, *self.lhs(), *self.rhs(), $opname);
                }
            }
        )+
    };
}

impl_binary_integral_same_rule!(
    arith::Add => "add",
    arith::Sub => "sub",
    arith::Mul => "mul",
    arith::Sdiv => "sdiv",
    arith::Udiv => "udiv",
    arith::Smod => "smod",
    arith::Umod => "umod",
    logic::And => "and",
    logic::Or => "or",
    logic::Xor => "xor",
);

macro_rules! impl_shift_rule {
    ($($ty:ty => $opname:literal),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_shift(inst_id, *self.bits(), *self.value(), $opname);
                }
            }
        )+
    };
}

impl_shift_rule!(
    arith::Shl => "shl",
    arith::Shr => "shr",
    arith::Sar => "sar",
);

macro_rules! impl_cmp_rule {
    ($($ty:ty => $opname:literal),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_cmp(inst_id, *self.lhs(), *self.rhs(), $opname);
                }
            }
        )+
    };
}

impl_cmp_rule!(
    cmp::Lt => "lt",
    cmp::Gt => "gt",
    cmp::Slt => "slt",
    cmp::Sgt => "sgt",
    cmp::Le => "le",
    cmp::Ge => "ge",
    cmp::Sle => "sle",
    cmp::Sge => "sge",
    cmp::Eq => "eq",
    cmp::Ne => "ne",
);

macro_rules! impl_ext_cast_rule {
    ($($ty:ty => ($is_ext:expr, $opname:literal)),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_ext_cast(inst_id, *self.from(), *self.ty(), $is_ext, $opname);
                }
            }
        )+
    };
}

impl_ext_cast_rule!(
    cast::Sext => (true, "sext"),
    cast::Zext => (true, "zext"),
    cast::Trunc => (false, "trunc"),
);

impl VerifyInst for cmp::IsZero {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(arg_ty) = verifier.value_ty(*self.lhs()) else {
            return;
        };
        if !arg_ty.is_integral() && !is_pointer_ty(verifier.ctx, arg_ty) {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "iszero operand must be integral or pointer",
                    location.clone(),
                )
                .with_note(format!("found operand type {arg_ty:?}")),
            );
        }
        verifier.expect_result_ty(inst_id, Type::I1, location);
    }
}

impl VerifyInst for cast::Bitcast {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(from_ty) = verifier.value_ty(*self.from()) else {
            return;
        };
        let to_ty = *self.ty();
        if verifier.is_function_ty(from_ty) || verifier.is_function_ty(to_ty) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "bitcast does not allow function types",
                location.clone(),
            ));
        }

        let from_size = verifier.type_size(from_ty);
        let to_size = verifier.type_size(to_ty);
        if from_size.is_none() || to_size.is_none() || from_size != to_size {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "bitcast requires source and target types with identical size",
                    location.clone(),
                )
                .with_note(format!(
                    "from {:?} ({from_size:?}), to {:?} ({to_size:?})",
                    from_ty, to_ty
                )),
            );
        }

        verifier.expect_result_ty(inst_id, to_ty, location);
    }
}

impl VerifyInst for cast::IntToPtr {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(from_ty) = verifier.value_ty(*self.from()) else {
            return;
        };
        let to_ty = *self.ty();
        if !from_ty.is_integral() || !is_pointer_ty(verifier.ctx, to_ty) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "int_to_ptr requires integral source and pointer target",
                location.clone(),
            ));
        }
        verifier.expect_result_ty(inst_id, to_ty, location);
    }
}

impl VerifyInst for cast::PtrToInt {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(from_ty) = verifier.value_ty(*self.from()) else {
            return;
        };
        let to_ty = *self.ty();
        if !is_pointer_ty(verifier.ctx, from_ty) || !to_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "ptr_to_int requires pointer source and integral target",
                location.clone(),
            ));
        }
        verifier.expect_result_ty(inst_id, to_ty, location);
    }
}

impl VerifyInst for data::Mload {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(addr_ty) = verifier.value_ty(*self.addr()) else {
            return;
        };
        if !is_integral_or_pointer(verifier.ctx, addr_ty) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "mload address must be integral or pointer",
                location.clone(),
            ));
        }
        if !verifier.is_storable_type(*self.ty()) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::UnstorableTypeInMemoryOp,
                "mload type is not storable",
                location.clone(),
            ));
        }
        verifier.expect_result_ty(inst_id, *self.ty(), location);
    }
}

impl VerifyInst for data::Mstore {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(addr_ty) = verifier.value_ty(*self.addr()) else {
            return;
        };
        if !is_integral_or_pointer(verifier.ctx, addr_ty) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "mstore address must be integral or pointer",
                location.clone(),
            ));
        }
        if let Some(value_ty) = verifier.value_ty(*self.value())
            && value_ty != *self.ty()
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "mstore value type must match explicit type",
                    location.clone(),
                )
                .with_note(format!(
                    "expected {:?}, found {:?}",
                    self.ty(),
                    value_ty
                )),
            );
        }
        if !verifier.is_storable_type(*self.ty()) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::UnstorableTypeInMemoryOp,
                "mstore type is not storable",
                location.clone(),
            ));
        }
        verifier.expect_no_result(inst_id, location);
    }
}

impl VerifyInst for data::Alloca {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        if !verifier.is_storable_type(*self.ty()) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::UnstorableTypeInMemoryOp,
                "alloca type is not storable",
                location.clone(),
            ));
        }
        let Some(result_ty) = verifier.inst_result_ty(inst_id) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "alloca must produce a pointer result",
                location,
            ));
            return;
        };
        if verifier.pointee_ty(result_ty) != Some(*self.ty()) {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "alloca result type must be pointer to allocated type",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!(
                    "expected pointer to {:?}, found {:?}",
                    self.ty(),
                    result_ty
                )),
            );
        }
    }
}

impl VerifyInst for data::Gep {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(expected_pointee) = verifier.gep_result_pointee(self.values(), location.clone())
        else {
            return;
        };
        let Some(result_ty) = verifier.inst_result_ty(inst_id) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "gep must produce a pointer result",
                location,
            ));
            return;
        };
        if verifier.pointee_ty(result_ty) != Some(expected_pointee) {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "gep result type does not match computed pointee type",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!(
                    "expected pointer to {:?}, found {:?}",
                    expected_pointee, result_ty
                )),
            );
        }
    }
}

impl VerifyInst for data::InsertValue {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(dest_ty) = verifier.value_ty(*self.dest()) else {
            return;
        };
        let Some(index_ty) = verifier.value_ty(*self.idx()) else {
            return;
        };
        if !index_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "insert_value index must be integral",
                location.clone(),
            ));
            return;
        }
        let Some(field_ty) =
            verifier.aggregate_field_ty(dest_ty, *self.idx(), true, location.clone())
        else {
            return;
        };
        if let Some(value_ty) = verifier.value_ty(*self.value())
            && value_ty != field_ty
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "insert_value payload type does not match aggregate field type",
                    location.clone(),
                )
                .with_note(format!("expected {:?}, found {:?}", field_ty, value_ty)),
            );
        }
        verifier.expect_result_ty(inst_id, dest_ty, location);
    }
}

impl VerifyInst for data::ExtractValue {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(dest_ty) = verifier.value_ty(*self.dest()) else {
            return;
        };
        let Some(index_ty) = verifier.value_ty(*self.idx()) else {
            return;
        };
        if !index_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "extract_value index must be integral",
                location.clone(),
            ));
            return;
        }
        let Some(field_ty) =
            verifier.aggregate_field_ty(dest_ty, *self.idx(), false, location.clone())
        else {
            return;
        };
        verifier.expect_result_ty(inst_id, field_ty, location);
    }
}

impl VerifyInst for data::GetFunctionPtr {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(sig) = verifier.ctx.get_sig(*self.func()) else {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InvalidFuncRef,
                    "get_function_ptr references unknown function",
                    location,
                )
                .with_note(format!("missing function id {}", self.func().as_u32())),
            );
            return;
        };
        let Some(result_ty) = verifier.inst_result_ty(inst_id) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "get_function_ptr must produce a result",
                verifier.inst_location(inst_id),
            ));
            return;
        };
        let Some(Type::Compound(func_cmpd_ref)) = verifier.pointee_ty(result_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "get_function_ptr result must be a pointer to function type",
                verifier.inst_location(inst_id),
            ));
            return;
        };
        let matches = verifier.ctx.with_ty_store(|store| {
            let Some(cmpd) = store.get_compound(func_cmpd_ref) else {
                return false;
            };
            matches!(cmpd, CompoundType::Func { args, ret_ty } if args.as_slice() == sig.args() && *ret_ty == sig.ret_ty())
        });
        if !matches {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "get_function_ptr result type does not match callee signature",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!(
                    "callee signature is {}({:?}) -> {:?}",
                    sig.name(),
                    sig.args(),
                    sig.ret_ty()
                )),
            );
        }
    }
}

impl VerifyInst for data::SymAddr {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        verifier.verify_symbol_ref(self.sym(), location.clone());
        verifier.expect_result_ty(inst_id, verifier.ctx.type_layout.pointer_repl(), location);
    }

    fn actual_arity(&self) -> Option<usize> {
        Some(1)
    }
}

impl VerifyInst for data::SymSize {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        verifier.verify_symbol_ref(self.sym(), location.clone());
        verifier.expect_result_ty(inst_id, verifier.ctx.type_layout.pointer_repl(), location);
    }

    fn actual_arity(&self) -> Option<usize> {
        Some(1)
    }
}

impl VerifyInst for control_flow::Jump {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        verifier.expect_no_result(inst_id, verifier.inst_location(inst_id));
    }
}

impl VerifyInst for control_flow::Br {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        if let Some(cond_ty) = verifier.value_ty(*self.cond())
            && cond_ty != Type::I1
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "branch condition type must be i1",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!("found condition type {:?}", cond_ty)),
            );
        }
        verifier.expect_no_result(inst_id, verifier.inst_location(inst_id));
    }
}

impl VerifyInst for control_flow::BrTable {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(scrutinee_ty) = verifier.value_ty(*self.scrutinee()) else {
            verifier.expect_no_result(inst_id, location);
            return;
        };
        if !scrutinee_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "br_table scrutinee must be integral",
                location.clone(),
            ));
        }
        let mut seen_keys = FxHashSet::default();
        for (key, _) in self.table() {
            let Some(key_ty) = verifier.value_ty(*key) else {
                continue;
            };
            if key_ty != scrutinee_ty {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "br_table key type must match scrutinee type",
                        location.clone(),
                    )
                    .with_note(format!("scrutinee {:?}, key {:?}", scrutinee_ty, key_ty)),
                );
            }
            let Some(imm) = verifier.value_imm(*key) else {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "br_table keys must be immediate values",
                    location.clone(),
                ));
                continue;
            };
            if !seen_keys.insert(imm) {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "br_table has duplicate key",
                    location.clone(),
                ));
            }
        }
        verifier.expect_no_result(inst_id, location);
    }

    fn actual_arity(&self) -> Option<usize> {
        Some(1 + usize::from(self.default().is_some()) + self.table().len())
    }
}

impl VerifyInst for control_flow::Phi {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let _ = verifier.ensure_result_exists(inst_id, verifier.inst_location(inst_id));
    }

    fn actual_arity(&self) -> Option<usize> {
        Some(self.args().len())
    }
}

impl VerifyInst for control_flow::Call {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(callee_sig) = verifier.ctx.get_sig(*self.callee()) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InvalidFuncRef,
                "call references unknown callee",
                location,
            ));
            return;
        };
        if self.args().len() != callee_sig.args().len() {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::CallArityMismatch,
                    "call argument count does not match callee signature",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!(
                    "expected {}, found {}",
                    callee_sig.args().len(),
                    self.args().len()
                )),
            );
        }
        for (index, (arg, expected_ty)) in self.args().iter().zip(callee_sig.args()).enumerate() {
            if let Some(actual_ty) = verifier.value_ty(*arg)
                && actual_ty != *expected_ty
            {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::CallArgTypeMismatch,
                        "call argument type does not match callee signature",
                        verifier.inst_location(inst_id),
                    )
                    .with_note(format!(
                        "arg {index}: expected {:?}, found {:?}",
                        expected_ty, actual_ty
                    )),
                );
            }
        }
        if callee_sig.ret_ty().is_unit() {
            verifier.expect_no_result(inst_id, verifier.inst_location(inst_id));
        } else {
            verifier.expect_result_ty(
                inst_id,
                callee_sig.ret_ty(),
                verifier.inst_location(inst_id),
            );
        }
    }
}

impl VerifyInst for control_flow::Return {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let expected_ret_ty = verifier
            .sig
            .as_ref()
            .map(|sig| sig.ret_ty())
            .unwrap_or(Type::Unit);
        match (expected_ret_ty, self.arg()) {
            (ret_ty, None) if !ret_ty.is_unit() => {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::ReturnTypeMismatch,
                    "non-unit function return requires an argument",
                    location,
                ));
            }
            (ret_ty, Some(_)) if ret_ty.is_unit() => {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::ReturnTypeMismatch,
                    "unit function return must not carry a value",
                    location,
                ));
            }
            (ret_ty, Some(value)) => {
                if let Some(actual_ty) = verifier.value_ty(*value)
                    && actual_ty != ret_ty
                {
                    verifier.emit(
                        Diagnostic::error(
                            DiagnosticCode::ReturnTypeMismatch,
                            "return value type does not match function return type",
                            verifier.inst_location(inst_id),
                        )
                        .with_note(format!("expected {:?}, found {:?}", ret_ty, actual_ty)),
                    );
                }
            }
            _ => {}
        }
        verifier.expect_no_result(inst_id, verifier.inst_location(inst_id));
    }
}

impl VerifyInst for control_flow::Unreachable {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        verifier.expect_no_result(inst_id, verifier.inst_location(inst_id));
    }
}

macro_rules! impl_evm_no_result_rule {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_evm_rule_common(inst_id, &self.collect_values(), true);
                }
            }
        )+
    };
}

impl_evm_no_result_rule!(
    evm::EvmStop,
    evm::EvmInvalid,
    evm::EvmCalldataCopy,
    evm::EvmCodeCopy,
    evm::EvmExtCodeCopy,
    evm::EvmReturnDataCopy,
    evm::EvmMstore8,
    evm::EvmSstore,
    evm::EvmTstore,
    evm::EvmMcopy,
    evm::EvmLog0,
    evm::EvmLog1,
    evm::EvmLog2,
    evm::EvmLog3,
    evm::EvmLog4,
    evm::EvmReturn,
    evm::EvmRevert,
    evm::EvmSelfDestruct,
);

macro_rules! impl_evm_arithmetic_rule {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    let operands = self.collect_values();
                    verifier.verify_evm_rule_common(inst_id, &operands, false);
                    verifier.verify_evm_arithmetic_rule(inst_id, &operands);
                }
            }
        )+
    };
}

impl_evm_arithmetic_rule!(
    evm::EvmUdiv,
    evm::EvmSdiv,
    evm::EvmUmod,
    evm::EvmSmod,
    evm::EvmExp,
    evm::EvmByte,
    evm::EvmAddMod,
    evm::EvmMulMod,
    evm::EvmClz,
);

impl VerifyInst for evm::EvmMalloc {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        verifier.verify_evm_rule_common(inst_id, &self.collect_values(), false);
        verifier.verify_evm_malloc_rule(inst_id);
    }
}

macro_rules! impl_evm_general_result_rule {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verifier.verify_evm_rule_common(inst_id, &self.collect_values(), false);
                    verifier.verify_evm_general_result_rule(inst_id);
                }
            }
        )+
    };
}

impl_evm_general_result_rule!(
    evm::EvmKeccak256,
    evm::EvmAddress,
    evm::EvmBalance,
    evm::EvmOrigin,
    evm::EvmCaller,
    evm::EvmCallValue,
    evm::EvmCalldataLoad,
    evm::EvmCalldataSize,
    evm::EvmCodeSize,
    evm::EvmGasPrice,
    evm::EvmExtCodeSize,
    evm::EvmReturnDataSize,
    evm::EvmExtCodeHash,
    evm::EvmBlockHash,
    evm::EvmCoinBase,
    evm::EvmTimestamp,
    evm::EvmNumber,
    evm::EvmPrevRandao,
    evm::EvmGasLimit,
    evm::EvmChainId,
    evm::EvmSelfBalance,
    evm::EvmBaseFee,
    evm::EvmBlobHash,
    evm::EvmBlobBaseFee,
    evm::EvmSload,
    evm::EvmMsize,
    evm::EvmGas,
    evm::EvmTload,
    evm::EvmCreate,
    evm::EvmCall,
    evm::EvmCallCode,
    evm::EvmDelegateCall,
    evm::EvmCreate2,
    evm::EvmStaticCall,
);

impl FunctionVerifier<'_> {
    fn verify_evm_rule_common(&mut self, inst_id: InstId, operands: &[ValueId], no_result: bool) {
        let location = self.inst_location(inst_id);
        if no_result {
            self.expect_no_result(inst_id, location.clone());
        } else {
            let _ = self.ensure_result_exists(inst_id, location.clone());
        }

        for value in operands {
            let Some(ty) = self.value_ty(*value) else {
                continue;
            };
            if !is_integral_or_pointer(self.ctx, ty) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "EVM instruction operands must be integral or pointer values",
                        location.clone(),
                    )
                    .with_note(format!(
                        "operand v{} has type {:?}",
                        value.as_u32(),
                        ty
                    )),
                );
            }
        }
    }

    fn verify_evm_arithmetic_rule(&mut self, inst_id: InstId, operands: &[ValueId]) {
        let location = self.inst_location(inst_id);
        let mut operand_ty = None;
        for value in operands {
            let Some(ty) = self.value_ty(*value) else {
                continue;
            };
            if !ty.is_integral() {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "EVM arithmetic operand must be integral",
                        location.clone(),
                    )
                    .with_note(format!(
                        "operand v{} has type {:?}",
                        value.as_u32(),
                        ty
                    )),
                );
            }

            if let Some(expected) = operand_ty {
                if expected != ty {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InstOperandTypeMismatch,
                            "EVM arithmetic operands must have identical type",
                            location.clone(),
                        )
                        .with_note(format!("expected {:?}, found {:?}", expected, ty)),
                    );
                }
            } else {
                operand_ty = Some(ty);
            }
        }

        if let (Some(expected), Some(result_ty)) = (operand_ty, self.inst_result_ty(inst_id))
            && expected != result_ty
        {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "EVM arithmetic result type must match operand type",
                    location,
                )
                .with_note(format!("expected {:?}, found {:?}", expected, result_ty)),
            );
        }
    }

    fn verify_evm_malloc_rule(&mut self, inst_id: InstId) {
        let location = self.inst_location(inst_id);
        if let Some(result_ty) = self.inst_result_ty(inst_id)
            && !is_pointer_ty(self.ctx, result_ty)
        {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "evm_malloc result must be a pointer type",
                    location,
                )
                .with_note(format!("found result type {:?}", result_ty)),
            );
        }
    }

    fn verify_evm_general_result_rule(&mut self, inst_id: InstId) {
        let location = self.inst_location(inst_id);
        if let Some(result_ty) = self.inst_result_ty(inst_id)
            && !result_ty.is_integral()
            && !is_pointer_ty(self.ctx, result_ty)
        {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "EVM instruction result must be integral or pointer",
                    location,
                )
                .with_note(format!("found result type {:?}", result_ty)),
            );
        }
    }
}
