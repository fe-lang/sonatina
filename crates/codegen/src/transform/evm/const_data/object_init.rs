use smallvec::smallvec;
use sonatina_ir::{
    Function, Immediate, InstId, Type, ValueId,
    global_variable::GvInitializer,
    inst::{cast, data, evm},
    types::CompoundType,
};

use super::{
    const_addr_with_offset, emit_const_load_from_addr,
    encoding::{const_leaf_count, word_blob_copy_len_bytes},
    imm_i256, insert_before_no_result, insert_before_one,
};
use crate::transform::aggregate::shape;

pub(super) fn emit_obj_init(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    init: &GvInitializer,
) {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            panic!("integral obj.init.const source must be immediate");
        };
        let value = func.dfg.make_imm_value(*imm);
        insert_before_no_result(
            func,
            before,
            data::ObjStore::new_unchecked(func.inst_set(), object, value),
        );
        return;
    }

    match (ty.resolve_compound(func.ctx()), init) {
        (Some(CompoundType::Array { elem, len }), GvInitializer::Array(items)) => {
            assert_eq!(items.len(), len, "array initializer length mismatch");
            for (idx, item) in items.iter().enumerate() {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjIndex::new_unchecked(func.inst_set(), object, index),
                    elem.to_obj_ref(func.ctx()),
                );
                emit_obj_init(func, before, slot, elem, item);
            }
        }
        (Some(CompoundType::Struct(s)), GvInitializer::Struct(fields)) => {
            assert!(
                !s.packed,
                "packed structs are unsupported in obj.init.const"
            );
            assert_eq!(
                fields.len(),
                s.fields.len(),
                "struct initializer length mismatch"
            );
            for (idx, (field_ty, field)) in s.fields.iter().copied().zip(fields.iter()).enumerate()
            {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, index]),
                    field_ty.to_obj_ref(func.ctx()),
                );
                emit_obj_init(func, before, slot, field_ty, field);
            }
        }
        _ => panic!("unsupported obj.init.const type {ty:?}"),
    }
}

pub(super) fn emit_obj_zero_fill(func: &mut Function, before: InstId, object: ValueId, ty: Type) {
    let len = shape::runtime_size_bytes(func.ctx(), ty)
        .expect("zero obj.init.const requires a concrete runtime size");
    if len == 0 {
        return;
    }

    let dst = insert_before_one(
        func,
        before,
        data::ObjMaterializeStack::new_unchecked(func.inst_set(), object),
        ty.to_ptr(func.ctx()),
    );
    let code_size = insert_before_one(
        func,
        before,
        evm::EvmCodeSize::new_unchecked(func.inst_set()),
        Type::I256,
    );
    let len = imm_i256(func, len);
    insert_before_no_result(
        func,
        before,
        evm::EvmCodeCopy::new_unchecked(func.inst_set(), dst, code_size, len),
    );
}

pub(super) fn emit_obj_splat_fill(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    value: Immediate,
) -> bool {
    let Some(total_len) = word_blob_copy_len_bytes(func.ctx(), ty) else {
        return false;
    };
    if total_len <= 32 {
        return false;
    }

    let dst = insert_before_one(
        func,
        before,
        data::ObjMaterializeStack::new_unchecked(func.inst_set(), object),
        ty.to_ptr(func.ctx()),
    );
    let word_ptr_ty = Type::I256.to_ptr(func.ctx());
    let dst = insert_before_one(
        func,
        before,
        cast::Bitcast::new_unchecked(func.inst_set(), dst, word_ptr_ty),
        word_ptr_ty,
    );
    let value_id = func.dfg.make_imm_value(value);
    insert_before_no_result(
        func,
        before,
        data::Mstore::new_unchecked(func.inst_set(), dst, value_id, value.ty()),
    );

    let mut filled = 32u32;
    while filled < total_len {
        let chunk = filled.min(total_len - filled);
        let dest = gep_word_offset(func, before, dst, filled / 32);
        let copy_len = imm_i256(func, chunk);
        insert_before_no_result(
            func,
            before,
            evm::EvmMcopy::new_unchecked(func.inst_set(), dest, dst, copy_len),
        );
        filled += chunk;
    }
    true
}

pub(super) fn gep_word_offset(
    func: &mut Function,
    before: InstId,
    base: ValueId,
    word_offset: u32,
) -> ValueId {
    if word_offset == 0 {
        return base;
    }
    let index = imm_i256(func, word_offset);
    insert_before_one(
        func,
        before,
        data::Gep::new_unchecked(func.inst_set(), smallvec![base, index]),
        Type::I256.to_ptr(func.ctx()),
    )
}

pub(super) fn emit_obj_init_from_codecopy(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    addr: ValueId,
    copy_len_bytes: u32,
) {
    let dst = insert_before_one(
        func,
        before,
        data::ObjMaterializeStack::new_unchecked(func.inst_set(), object),
        ty.to_ptr(func.ctx()),
    );
    let copy_len = imm_i256(func, copy_len_bytes);
    insert_before_no_result(
        func,
        before,
        evm::EvmCodeCopy::new_unchecked(func.inst_set(), dst, addr, copy_len),
    );
}

pub(super) fn emit_obj_init_from_addr(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    addr: ValueId,
) {
    let scratch = insert_before_one(
        func,
        before,
        data::Alloca::new_unchecked(func.inst_set(), Type::I256),
        Type::I256.to_ptr(func.ctx()),
    );
    emit_obj_init_from_addr_with_scratch(func, before, object, ty, addr, scratch);
}

fn emit_obj_init_from_addr_with_scratch(
    func: &mut Function,
    before: InstId,
    object: ValueId,
    ty: Type,
    addr: ValueId,
    scratch: ValueId,
) {
    if ty.is_integral() {
        let value = emit_const_load_from_addr(func, before, addr, ty, Some(scratch));
        insert_before_no_result(
            func,
            before,
            data::ObjStore::new_unchecked(func.inst_set(), object, value),
        );
        return;
    }

    match ty.resolve_compound(func.ctx()) {
        Some(CompoundType::Array { elem, len }) => {
            let stride = const_leaf_count(func.ctx(), elem)
                .and_then(|count| count.checked_mul(32))
                .unwrap_or_else(|| {
                    panic!("unsupported obj.init.const array element type {elem:?}")
                });
            for idx in 0..len {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjIndex::new_unchecked(func.inst_set(), object, index),
                    elem.to_obj_ref(func.ctx()),
                );
                let child_addr = const_addr_with_offset(
                    func,
                    before,
                    addr,
                    u32::try_from(idx)
                        .expect("index overflow")
                        .checked_mul(stride)
                        .expect("const array offset overflow"),
                    Vec::new(),
                    false,
                );
                emit_obj_init_from_addr_with_scratch(func, before, slot, elem, child_addr, scratch);
            }
        }
        Some(CompoundType::Struct(s)) => {
            assert!(
                !s.packed,
                "packed structs are unsupported in obj.init.const"
            );
            let mut field_offset = 0u32;
            for (idx, field_ty) in s.fields.iter().copied().enumerate() {
                let index = func
                    .dfg
                    .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
                let slot = insert_before_one(
                    func,
                    before,
                    data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, index]),
                    field_ty.to_obj_ref(func.ctx()),
                );
                let child_addr =
                    const_addr_with_offset(func, before, addr, field_offset, Vec::new(), false);
                emit_obj_init_from_addr_with_scratch(
                    func, before, slot, field_ty, child_addr, scratch,
                );
                field_offset = field_offset
                    .checked_add(
                        const_leaf_count(func.ctx(), field_ty)
                            .and_then(|count| count.checked_mul(32))
                            .unwrap_or_else(|| {
                                panic!("unsupported obj.init.const struct field type {field_ty:?}")
                            }),
                    )
                    .expect("const struct field offset overflow");
            }
        }
        _ => panic!("unsupported obj.init.const type {ty:?}"),
    }
}
