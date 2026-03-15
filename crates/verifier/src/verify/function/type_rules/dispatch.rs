use macros::inst_prop;
use rustc_hash::FxHashSet;
use sonatina_ir::{
    Inst, InstId, Type, ValueId,
    inst::{
        arith, cast, cmp,
        control_flow::{self},
        data, evm, logic,
    },
    types::{CompoundType, CompoundTypeRef, EnumVariantRef},
};

use crate::{
    diagnostic::{Diagnostic, DiagnosticCode},
    verify::type_utils::{is_integral_or_pointer, is_obj_ref_ty, is_pointer_ty},
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

fn verify_binary_overflow_inst(
    verifier: &mut FunctionVerifier<'_>,
    inst_id: InstId,
    lhs: ValueId,
    rhs: ValueId,
    opname: &str,
) {
    let location = verifier.inst_location(inst_id);
    let Some(lhs_ty) = verifier.value_ty(lhs) else {
        return;
    };
    let Some(rhs_ty) = verifier.value_ty(rhs) else {
        return;
    };

    if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
        verifier.emit(
            Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} operands must be integral"),
                location.clone(),
            )
            .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
        );
    }
    if lhs_ty != rhs_ty {
        verifier.emit(
            Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} operands must have identical types"),
                location.clone(),
            )
            .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
        );
    }

    verifier.expect_result_tys(inst_id, &[lhs_ty, Type::I1], location);
}

fn verify_unary_overflow_inst(
    verifier: &mut FunctionVerifier<'_>,
    inst_id: InstId,
    arg: ValueId,
    opname: &str,
) {
    let location = verifier.inst_location(inst_id);
    let Some(arg_ty) = verifier.value_ty(arg) else {
        return;
    };

    if !arg_ty.is_integral() {
        verifier.emit(
            Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} operand must be integral"),
                location.clone(),
            )
            .with_note(format!("arg {:?}", arg_ty)),
        );
    }

    verifier.expect_result_tys(inst_id, &[arg_ty, Type::I1], location);
}

macro_rules! impl_binary_overflow_rule {
    ($($ty:ty => $opname:literal),+ $(,)?) => {
        $(
            impl VerifyInst for $ty {
                fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
                    verify_binary_overflow_inst(verifier, inst_id, *self.lhs(), *self.rhs(), $opname);
                }
            }
        )+
    };
}

impl_binary_overflow_rule!(
    arith::Uaddo => "uaddo",
    arith::Saddo => "saddo",
    arith::Usubo => "usubo",
    arith::Ssubo => "ssubo",
    arith::Umulo => "umulo",
    arith::Smulo => "smulo",
    evm::EvmUdivo => "evm_udivo",
    evm::EvmSdivo => "evm_sdivo",
    evm::EvmUmodo => "evm_umodo",
    evm::EvmSmodo => "evm_smodo",
);

impl VerifyInst for arith::Snego {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        verify_unary_overflow_inst(verifier, inst_id, *self.arg(), "snego");
    }
}

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

fn object_field_ty(
    verifier: &mut FunctionVerifier<'_>,
    base_ty: Type,
    idx_value: ValueId,
    location: crate::diagnostic::Location,
) -> Option<Type> {
    let Type::Compound(cmpd_ref) = base_ty else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InstOperandTypeMismatch,
            "object projection requires struct or array object type",
            location,
        ));
        return None;
    };

    let Some(cmpd) = verifier
        .ctx
        .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
    else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InvalidTypeRef,
            "object projection references unknown type",
            location,
        ));
        return None;
    };

    match cmpd {
        CompoundType::Array { elem, .. } => Some(elem),
        CompoundType::Struct(s) => {
            let Some(imm) = verifier.value_imm(idx_value) else {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "object struct projection index must be an immediate value",
                    location,
                ));
                return None;
            };
            if imm.is_negative() {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "object projection index must be non-negative",
                        location,
                    )
                    .with_note(format!("index immediate {:?}", imm)),
                );
                return None;
            }
            let index = imm.as_usize();
            let Some(field_ty) = s.fields.get(index).copied() else {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "object projection index is out of bounds",
                        location,
                    )
                    .with_note(format!("index {index}, fields {}", s.fields.len())),
                );
                return None;
            };
            Some(field_ty)
        }
        CompoundType::Enum(_) => {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "object projection requires struct or array object type; use enum.proj for enums",
                location,
            ));
            None
        }
        CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::Func { .. } => {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "object projection requires struct or array object type",
                location,
            ));
            None
        }
    }
}

fn enum_value_ty(
    verifier: &mut FunctionVerifier<'_>,
    ty: Type,
    location: crate::diagnostic::Location,
    opname: &str,
) -> Option<CompoundTypeRef> {
    let Type::Compound(cmpd_ref) = ty else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InstOperandTypeMismatch,
            format!("{opname} operand must have enum type"),
            location,
        ));
        return None;
    };

    let Some(cmpd) = verifier
        .ctx
        .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
    else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InvalidTypeRef,
            format!("{opname} references unknown enum type"),
            location,
        ));
        return None;
    };

    if matches!(cmpd, CompoundType::Enum(_)) {
        Some(cmpd_ref)
    } else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InstOperandTypeMismatch,
            format!("{opname} operand must have enum type"),
            location,
        ));
        None
    }
}

fn enum_object_ty(
    verifier: &mut FunctionVerifier<'_>,
    object_ty: Type,
    location: crate::diagnostic::Location,
    opname: &str,
) -> Option<CompoundTypeRef> {
    let Some(enum_ty) = verifier.objref_ty(object_ty) else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InstOperandTypeMismatch,
            format!("{opname} operand must be an object reference to an enum"),
            location,
        ));
        return None;
    };
    enum_value_ty(verifier, enum_ty, location, opname)
}

fn enum_variant_field_ty(
    verifier: &mut FunctionVerifier<'_>,
    enum_ty: CompoundTypeRef,
    variant: EnumVariantRef,
    field_value: ValueId,
    location: crate::diagnostic::Location,
    opname: &str,
) -> Option<Type> {
    if variant.enum_ty() != enum_ty {
        verifier.emit(
            Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} variant does not belong to the operand enum type"),
                location.clone(),
            )
            .with_note(format!(
                "expected enum {}, found variant for enum {}",
                enum_ty.as_u32(),
                variant.enum_ty().as_u32()
            )),
        );
        return None;
    }

    let Some(field_ty) = verifier.ctx.with_ty_store(|store| {
        let idx = store.enum_variant_data(variant).and_then(|variant_data| {
            let imm = verifier.value_imm(field_value)?;
            if imm.is_negative() {
                return None;
            }
            let index = imm.as_usize();
            variant_data.fields.get(index).copied()
        })?;
        Some(idx)
    }) else {
        let index_ty = verifier.value_ty(field_value)?;
        if !index_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} field index must be integral"),
                location,
            ));
            return None;
        }

        if let Some(imm) = verifier.value_imm(field_value)
            && imm.is_negative()
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} field index must be non-negative"),
                    location,
                )
                .with_note(format!("index immediate {:?}", imm)),
            );
            return None;
        }

        verifier.emit(Diagnostic::error(
            DiagnosticCode::InstOperandTypeMismatch,
            format!("{opname} field index is out of bounds for the selected variant"),
            location,
        ));
        return None;
    };

    Some(field_ty)
}

fn variant_payload_tys(
    verifier: &mut FunctionVerifier<'_>,
    enum_ty: CompoundTypeRef,
    variant: EnumVariantRef,
    location: crate::diagnostic::Location,
    opname: &str,
) -> Option<Vec<Type>> {
    if variant.enum_ty() != enum_ty {
        verifier.emit(
            Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} variant does not belong to the operand enum type"),
                location.clone(),
            )
            .with_note(format!(
                "expected enum {}, found variant for enum {}",
                enum_ty.as_u32(),
                variant.enum_ty().as_u32()
            )),
        );
        return None;
    }

    verifier.ctx.with_ty_store(|store| {
        store
            .enum_variant_data(variant)
            .map(|variant_data| variant_data.fields.clone())
    })
}

fn same_block_dominating_enum_assert(
    verifier: &FunctionVerifier<'_>,
    use_inst: InstId,
    value: ValueId,
    variant: EnumVariantRef,
) -> bool {
    let Some(block) = verifier.inst_to_block.get(&use_inst).copied() else {
        return false;
    };
    let Some(insts) = verifier.block_to_insts.get(&block) else {
        return false;
    };

    for &inst in insts {
        if inst == use_inst {
            break;
        }
        if let Some(assert_variant) = sonatina_ir::inst::downcast::<&data::EnumAssertVariant>(
            verifier.ctx.inst_set,
            verifier.func.dfg.inst(inst),
        ) && *assert_variant.value() == value
            && *assert_variant.variant() == variant
        {
            return true;
        }
    }

    false
}

#[derive(Clone, Copy, Debug, Default)]
struct EnumFieldLoadProof {
    active_variant: bool,
    field_initialized: bool,
}

fn predecessor_edge_proves_enum_assert_ref(
    verifier: &FunctionVerifier<'_>,
    use_inst: InstId,
    object: ValueId,
    variant: EnumVariantRef,
) -> bool {
    let Some(block) = verifier.inst_to_block.get(&use_inst).copied() else {
        return false;
    };
    let Some(preds) = verifier.preds.get(&block) else {
        return false;
    };

    let mut saw_reachable_pred = false;
    for &pred in preds {
        if !verifier.reachable.contains(&pred) {
            continue;
        }
        saw_reachable_pred = true;
        if !br_table_edge_proves_enum_variant(verifier, pred, block, object, variant) {
            return false;
        }
    }

    saw_reachable_pred
}

fn same_block_enum_field_load_proof(
    verifier: &FunctionVerifier<'_>,
    use_inst: InstId,
    root_object: ValueId,
    field_object: ValueId,
    variant: EnumVariantRef,
) -> EnumFieldLoadProof {
    let pred_proof =
        predecessor_edge_proves_enum_assert_ref(verifier, use_inst, root_object, variant);
    let mut proof = EnumFieldLoadProof {
        active_variant: pred_proof,
        field_initialized: pred_proof,
    };
    let Some(block) = verifier.inst_to_block.get(&use_inst).copied() else {
        return proof;
    };
    let Some(insts) = verifier.block_to_insts.get(&block) else {
        return proof;
    };

    for &inst in insts {
        if inst == use_inst {
            break;
        }
        let inst_data = verifier.func.dfg.inst(inst);
        if let Some(assert_variant_ref) = sonatina_ir::inst::downcast::<&data::EnumAssertVariantRef>(
            verifier.ctx.inst_set,
            inst_data,
        ) && *assert_variant_ref.object() == root_object
        {
            if *assert_variant_ref.variant() == variant {
                proof.active_variant = true;
                proof.field_initialized = true;
            } else {
                proof = EnumFieldLoadProof::default();
            }
            continue;
        }
        if let Some(set_tag) =
            sonatina_ir::inst::downcast::<&data::EnumSetTag>(verifier.ctx.inst_set, inst_data)
            && *set_tag.object() == root_object
        {
            if *set_tag.variant() == variant {
                proof.active_variant = true;
            } else {
                proof = EnumFieldLoadProof::default();
            }
            continue;
        }
        if let Some(write_variant) =
            sonatina_ir::inst::downcast::<&data::EnumWriteVariant>(verifier.ctx.inst_set, inst_data)
            && *write_variant.object() == root_object
        {
            if *write_variant.variant() == variant {
                proof.active_variant = true;
                proof.field_initialized = true;
            } else {
                proof = EnumFieldLoadProof::default();
            }
            continue;
        }
        if let Some(store) =
            sonatina_ir::inst::downcast::<&data::ObjStore>(verifier.ctx.inst_set, inst_data)
        {
            if *store.object() == root_object {
                proof = EnumFieldLoadProof::default();
                continue;
            }
            if *store.object() == field_object {
                proof.field_initialized = true;
            }
        }
    }

    proof
}

fn br_table_edge_proves_enum_variant(
    verifier: &FunctionVerifier<'_>,
    pred: sonatina_ir::BlockId,
    succ: sonatina_ir::BlockId,
    object: ValueId,
    variant: EnumVariantRef,
) -> bool {
    let Some(term) = verifier.func.layout.last_inst_of(pred) else {
        return false;
    };
    let Some(br_table) = sonatina_ir::inst::downcast::<&control_flow::BrTable>(
        verifier.ctx.inst_set,
        verifier.func.dfg.inst(term),
    ) else {
        return false;
    };
    br_table_edge_variant(verifier, br_table, succ).is_some_and(
        |(proved_object, proved_variant)| proved_object == object && proved_variant == variant,
    )
}

fn br_table_edge_variant(
    verifier: &FunctionVerifier<'_>,
    br_table: &control_flow::BrTable,
    succ: sonatina_ir::BlockId,
) -> Option<(ValueId, EnumVariantRef)> {
    let enum_get_tag = enum_get_tag_of_value(verifier, *br_table.scrutinee())?;
    let object = *enum_get_tag.object();
    let Type::EnumTag(enum_ty) = verifier.value_ty(*br_table.scrutinee())? else {
        return None;
    };

    let mut matched_variant = None;
    for &(case_value, dest) in br_table.table() {
        if dest != succ {
            continue;
        }
        let case_variant = enum_variant_for_tag_value(verifier, enum_ty, case_value)?;
        if matched_variant.is_some_and(|matched| matched != case_variant) {
            return None;
        }
        matched_variant = Some(case_variant);
    }
    if let Some(matched_variant) = matched_variant {
        return Some((object, matched_variant));
    }

    if *br_table.default() != Some(succ) {
        return None;
    }

    let remaining_variant = remaining_br_table_variant(verifier, enum_ty, br_table)?;
    Some((object, remaining_variant))
}

fn remaining_br_table_variant(
    verifier: &FunctionVerifier<'_>,
    enum_ty: CompoundTypeRef,
    br_table: &control_flow::BrTable,
) -> Option<EnumVariantRef> {
    let variant_count = verifier.ctx.with_ty_store(|store| {
        let CompoundType::Enum(enum_data) = store.get_compound(enum_ty)? else {
            return None;
        };
        Some(enum_data.variants.len())
    })?;

    let mut uncovered_variant = None;
    for idx in 0..variant_count {
        let variant = EnumVariantRef::new(
            enum_ty,
            u32::try_from(idx).expect("enum variant index overflow"),
        );
        let mut covered = false;
        for &(case_value, _) in br_table.table() {
            if enum_variant_for_tag_value(verifier, enum_ty, case_value) == Some(variant) {
                covered = true;
                break;
            }
        }
        if covered {
            continue;
        }
        if uncovered_variant.is_some() {
            return None;
        }
        uncovered_variant = Some(variant);
    }

    uncovered_variant
}

fn enum_variant_for_tag_value(
    verifier: &FunctionVerifier<'_>,
    enum_ty: CompoundTypeRef,
    value: ValueId,
) -> Option<EnumVariantRef> {
    let idx = verifier.value_imm(value)?.as_i256().to_u256().as_usize();
    let variant_count = verifier.ctx.with_ty_store(|store| {
        let CompoundType::Enum(enum_data) = store.get_compound(enum_ty)? else {
            return None;
        };
        Some(enum_data.variants.len())
    })?;
    (idx < variant_count).then_some(EnumVariantRef::new(
        enum_ty,
        u32::try_from(idx).expect("enum variant index overflow"),
    ))
}

fn enum_get_tag_of_value(
    verifier: &FunctionVerifier<'_>,
    value: ValueId,
) -> Option<data::EnumGetTag> {
    let inst = verifier.func.dfg.value_inst(value)?;
    sonatina_ir::inst::downcast::<&data::EnumGetTag>(
        verifier.ctx.inst_set,
        verifier.func.dfg.inst(inst),
    )
    .cloned()
}

fn expect_objref_result(
    verifier: &mut FunctionVerifier<'_>,
    inst_id: InstId,
    elem_ty: Type,
    location: crate::diagnostic::Location,
    opname: &str,
) {
    let Some(result_ty) = verifier.inst_result_ty(inst_id) else {
        verifier.emit(Diagnostic::error(
            DiagnosticCode::InstResultTypeMismatch,
            format!("{opname} must produce an object-reference result"),
            location,
        ));
        return;
    };
    if verifier.objref_ty(result_ty) != Some(elem_ty) {
        verifier.emit(
            Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                format!("{opname} result type must be objref<{elem_ty:?}>"),
                verifier.inst_location(inst_id),
            )
            .with_note(format!("found {:?}", result_ty)),
        );
    }
}

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
        if verifier.objref_ty(from_ty).is_some() || verifier.objref_ty(to_ty).is_some() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "bitcast does not allow object-reference types",
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

impl VerifyInst for data::ObjAlloc {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        if verifier.is_function_ty(*self.ty()) || is_obj_ref_ty(verifier.ctx, *self.ty()) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.alloc type must be a non-function, non-object-reference type",
                location.clone(),
            ));
        }
        if !verifier.is_type_valid(*self.ty()) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InvalidTypeRef,
                "obj.alloc type is invalid",
                location.clone(),
            ));
        }
        expect_objref_result(verifier, inst_id, *self.ty(), location, "obj.alloc");
    }
}

impl VerifyInst for data::ObjProj {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some((&object, indices)) = self.values().split_first() else {
            return;
        };
        let Some(object_ty) = verifier.value_ty(object) else {
            return;
        };
        let Some(mut current_ty) = verifier.objref_ty(object_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.proj base must be an object reference",
                location.clone(),
            ));
            return;
        };
        for &idx_value in indices {
            let Some(idx_ty) = verifier.value_ty(idx_value) else {
                return;
            };
            if !idx_ty.is_integral() {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "object projection indices must be integral",
                    location.clone(),
                ));
                return;
            }
            let Some(field_ty) = object_field_ty(verifier, current_ty, idx_value, location.clone())
            else {
                return;
            };
            current_ty = field_ty;
        }
        expect_objref_result(verifier, inst_id, current_ty, location, "obj.proj");
    }
}

impl VerifyInst for data::ObjIndex {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(index_ty) = verifier.value_ty(*self.index()) else {
            return;
        };
        let Some(base_ty) = verifier.objref_ty(object_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.index base must be an object reference",
                location.clone(),
            ));
            return;
        };
        if !index_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.index index must be integral",
                location.clone(),
            ));
            return;
        }
        let Some(Type::Compound(cmpd_ref)) = Some(base_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.index requires an array object type",
                location.clone(),
            ));
            return;
        };
        let Some(cmpd) = verifier
            .ctx
            .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
        else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InvalidTypeRef,
                "obj.index references unknown object type",
                location.clone(),
            ));
            return;
        };
        let CompoundType::Array { elem, .. } = cmpd else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.index requires an array object type",
                location.clone(),
            ));
            return;
        };
        expect_objref_result(verifier, inst_id, elem, location, "obj.index");
    }
}

impl VerifyInst for data::ObjLoad {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(value_ty) = verifier.objref_ty(object_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.load operand must be an object reference",
                location.clone(),
            ));
            return;
        };
        if verifier.is_function_ty(value_ty) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.load cannot load function values",
                location.clone(),
            ));
        }
        if let Some(proj_inst) = verifier.func.dfg.value_inst(*self.object())
            && let Some(enum_proj) = sonatina_ir::inst::downcast::<&data::EnumProj>(
                verifier.ctx.inst_set,
                verifier.func.dfg.inst(proj_inst),
            )
        {
            let proof = same_block_enum_field_load_proof(
                verifier,
                inst_id,
                *enum_proj.object(),
                *self.object(),
                *enum_proj.variant(),
            );
            if !proof.active_variant || !proof.field_initialized {
                verifier.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "obj.load from enum.proj requires a proven initialized active variant field",
                    location.clone(),
                ));
            }
        }
        verifier.expect_result_ty(inst_id, value_ty, location);
    }
}

impl VerifyInst for data::ObjStore {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(expected_ty) = verifier.objref_ty(object_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.store destination must be an object reference",
                location.clone(),
            ));
            return;
        };
        if verifier.is_function_ty(expected_ty) {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.store cannot store function values",
                location.clone(),
            ));
        }
        if let Some(value_ty) = verifier.value_ty(*self.value())
            && value_ty != expected_ty
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "obj.store value type must match the referenced object field type",
                    location.clone(),
                )
                .with_note(format!("expected {:?}, found {:?}", expected_ty, value_ty)),
            );
        }
        verifier.expect_no_result(inst_id, location);
    }
}

impl VerifyInst for data::EnumMake {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(enum_ty) = enum_value_ty(verifier, *self.ty(), location.clone(), "enum.make")
        else {
            return;
        };
        let Some(payload_tys) = variant_payload_tys(
            verifier,
            enum_ty,
            *self.variant(),
            location.clone(),
            "enum.make",
        ) else {
            return;
        };

        if payload_tys.len() != self.values().len() {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "enum.make payload arity does not match variant payload",
                    location.clone(),
                )
                .with_note(format!(
                    "expected {}, found {}",
                    payload_tys.len(),
                    self.values().len()
                )),
            );
        }

        for (&value, &expected_ty) in self.values().iter().zip(payload_tys.iter()) {
            let Some(actual_ty) = verifier.value_ty(value) else {
                return;
            };
            if actual_ty != expected_ty {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "enum.make payload type does not match the selected variant field type",
                        location.clone(),
                    )
                    .with_note(format!("expected {:?}, found {:?}", expected_ty, actual_ty)),
                );
            }
        }

        verifier.expect_result_ty(inst_id, *self.ty(), location);
    }
}

impl VerifyInst for data::EnumTag {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(value_ty) = verifier.value_ty(*self.value()) else {
            return;
        };
        let Some(enum_ty) = enum_value_ty(verifier, value_ty, location.clone(), "enum.tag") else {
            return;
        };
        verifier.expect_result_ty(inst_id, Type::EnumTag(enum_ty), location);
    }
}

impl VerifyInst for data::EnumIsVariant {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(value_ty) = verifier.value_ty(*self.value()) else {
            return;
        };
        let Some(enum_ty) = enum_value_ty(verifier, value_ty, location.clone(), "enum.is_variant")
        else {
            return;
        };
        if variant_payload_tys(
            verifier,
            enum_ty,
            *self.variant(),
            location.clone(),
            "enum.is_variant",
        )
        .is_none()
        {
            return;
        }
        verifier.expect_result_ty(inst_id, Type::I1, location);
    }
}

impl VerifyInst for data::EnumAssertVariant {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(value_ty) = verifier.value_ty(*self.value()) else {
            return;
        };
        let Some(enum_ty) =
            enum_value_ty(verifier, value_ty, location.clone(), "enum.assert_variant")
        else {
            return;
        };
        if variant_payload_tys(
            verifier,
            enum_ty,
            *self.variant(),
            location.clone(),
            "enum.assert_variant",
        )
        .is_none()
        {
            return;
        }
        verifier.expect_no_result(inst_id, location);
    }
}

impl VerifyInst for data::EnumExtract {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(value_ty) = verifier.value_ty(*self.value()) else {
            return;
        };
        let Some(enum_ty) = enum_value_ty(verifier, value_ty, location.clone(), "enum.extract")
        else {
            return;
        };
        let Some(field_ty) = enum_variant_field_ty(
            verifier,
            enum_ty,
            *self.variant(),
            *self.field(),
            location.clone(),
            "enum.extract",
        ) else {
            return;
        };

        let proven = verifier
            .func
            .dfg
            .value_inst(*self.value())
            .and_then(|def_inst| {
                sonatina_ir::inst::downcast::<&data::EnumMake>(
                    verifier.ctx.inst_set,
                    verifier.func.dfg.inst(def_inst),
                )
                .map(|make| *make.variant() == *self.variant())
            })
            .unwrap_or(false)
            || same_block_dominating_enum_assert(verifier, inst_id, *self.value(), *self.variant());

        if !proven {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "enum.extract requires a proven active variant at the use site",
                location.clone(),
            ));
        }

        verifier.expect_result_ty(inst_id, field_ty, location);
    }
}

impl VerifyInst for data::EnumAssertVariantRef {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(enum_ty) = enum_object_ty(
            verifier,
            object_ty,
            location.clone(),
            "enum.assert_variant_ref",
        ) else {
            return;
        };
        if variant_payload_tys(
            verifier,
            enum_ty,
            *self.variant(),
            location.clone(),
            "enum.assert_variant_ref",
        )
        .is_none()
        {
            return;
        }
        verifier.expect_no_result(inst_id, location);
    }
}

impl VerifyInst for data::EnumSetTag {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(enum_ty) = enum_object_ty(verifier, object_ty, location.clone(), "enum.set_tag")
        else {
            return;
        };
        if variant_payload_tys(
            verifier,
            enum_ty,
            *self.variant(),
            location.clone(),
            "enum.set_tag",
        )
        .is_none()
        {
            return;
        }
        verifier.expect_no_result(inst_id, location);
    }
}

impl VerifyInst for data::EnumWriteVariant {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(enum_ty) =
            enum_object_ty(verifier, object_ty, location.clone(), "enum.write_variant")
        else {
            return;
        };
        let Some(payload_tys) = variant_payload_tys(
            verifier,
            enum_ty,
            *self.variant(),
            location.clone(),
            "enum.write_variant",
        ) else {
            return;
        };

        if payload_tys.len() != self.values().len() {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "enum.write_variant payload arity does not match variant payload",
                    location.clone(),
                )
                .with_note(format!(
                    "expected {}, found {}",
                    payload_tys.len(),
                    self.values().len()
                )),
            );
        }

        for (&value, &expected_ty) in self.values().iter().zip(payload_tys.iter()) {
            let Some(actual_ty) = verifier.value_ty(value) else {
                return;
            };
            if actual_ty != expected_ty {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "enum.write_variant payload type does not match the selected variant field type",
                        location.clone(),
                    )
                    .with_note(format!("expected {:?}, found {:?}", expected_ty, actual_ty)),
                );
            }
        }

        verifier.expect_no_result(inst_id, location);
    }
}

impl VerifyInst for data::EnumGetTag {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(enum_ty) = enum_object_ty(verifier, object_ty, location.clone(), "enum.get_tag")
        else {
            return;
        };
        verifier.expect_result_ty(inst_id, Type::EnumTag(enum_ty), location);
    }
}

impl VerifyInst for data::EnumProj {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(enum_ty) = enum_object_ty(verifier, object_ty, location.clone(), "enum.proj")
        else {
            return;
        };
        let Some(field_ty) = enum_variant_field_ty(
            verifier,
            enum_ty,
            *self.variant(),
            *self.field(),
            location.clone(),
            "enum.proj",
        ) else {
            return;
        };
        expect_objref_result(verifier, inst_id, field_ty, location, "enum.proj");
    }
}

impl VerifyInst for data::ObjMaterializeStack {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(elem_ty) = verifier.objref_ty(object_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.materialize.stack operand must be an object reference",
                location.clone(),
            ));
            return;
        };
        if verifier.pointee_ty(verifier.inst_result_ty(inst_id).unwrap_or(Type::Unit))
            != Some(elem_ty)
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "obj.materialize.stack result must be a raw pointer to the object type",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!(
                    "expected pointer to {:?}, found {:?}",
                    elem_ty,
                    verifier.inst_result_ty(inst_id)
                )),
            );
        }
    }
}

impl VerifyInst for data::ObjMaterializeHeap {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(object_ty) = verifier.value_ty(*self.object()) else {
            return;
        };
        let Some(elem_ty) = verifier.objref_ty(object_ty) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "obj.materialize.heap operand must be an object reference",
                location.clone(),
            ));
            return;
        };
        if verifier.pointee_ty(verifier.inst_result_ty(inst_id).unwrap_or(Type::Unit))
            != Some(elem_ty)
        {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "obj.materialize.heap result must be a raw pointer to the object type",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!(
                    "expected pointer to {:?}, found {:?}",
                    elem_ty,
                    verifier.inst_result_ty(inst_id)
                )),
            );
        }
    }
}

impl VerifyInst for data::MemAllocDynamic {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let Some(size_ty) = verifier.value_ty(*self.size()) else {
            return;
        };
        if !size_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "mem.alloc_dynamic size must be integral",
                location.clone(),
            ));
        }
        let Some(result_ty) = verifier.inst_result_ty(inst_id) else {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "mem.alloc_dynamic must produce a pointer result",
                location,
            ));
            return;
        };
        if !is_pointer_ty(verifier.ctx, result_ty) {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "mem.alloc_dynamic result must be a raw pointer",
                    verifier.inst_location(inst_id),
                )
                .with_note(format!("found {:?}", result_ty)),
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
            matches!(cmpd, CompoundType::Func { args, ret_tys } if args.as_slice() == sig.args() && ret_tys.as_slice() == sig.ret_tys())
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
                    sig.ret_tys()
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
        let enum_tag_scrutinee = scrutinee_ty.is_enum_tag();
        if !enum_tag_scrutinee && !scrutinee_ty.is_integral() {
            verifier.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "br_table scrutinee must be integral or an enum tag",
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
        verifier.expect_result_tys(
            inst_id,
            callee_sig.ret_tys(),
            verifier.inst_location(inst_id),
        );
    }
}

impl VerifyInst for control_flow::Return {
    fn verify_inst(&self, verifier: &mut FunctionVerifier<'_>, inst_id: InstId) {
        let location = verifier.inst_location(inst_id);
        let expected_ret_tys = verifier
            .sig
            .as_ref()
            .map(|sig| sig.ret_tys().to_vec())
            .unwrap_or_default();
        let actual_args = self.args().as_slice();
        if expected_ret_tys.len() != actual_args.len() {
            verifier.emit(
                Diagnostic::error(
                    DiagnosticCode::ReturnTypeMismatch,
                    "return value count does not match function signature",
                    location,
                )
                .with_note(format!(
                    "expected {}, found {}",
                    expected_ret_tys.len(),
                    actual_args.len()
                )),
            );
        }
        for (index, (value, expected_ty)) in actual_args.iter().zip(expected_ret_tys).enumerate() {
            if let Some(actual_ty) = verifier.value_ty(*value)
                && actual_ty != expected_ty
            {
                verifier.emit(
                    Diagnostic::error(
                        DiagnosticCode::ReturnTypeMismatch,
                        "return value type does not match function return type",
                        verifier.inst_location(inst_id),
                    )
                    .with_note(format!(
                        "return {index}: expected {:?}, found {:?}",
                        expected_ty, actual_ty
                    )),
                );
            }
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
