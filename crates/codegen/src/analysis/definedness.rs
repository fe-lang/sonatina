//! Conservative SSA definedness, with optional point-specific memory evidence.
//!
//! Memory reads, call results and parameters are never undef: uninitialized
//! memory holds arbitrary fixed bits, and an undef argument or return value
//! reaches the other side as one arbitrary value. Undef arises only from
//! `undef` itself and from operations with undefined results, and spreads
//! through the instructions that use it.

use std::cell::RefCell;

use cranelift_entity::EntityRef;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, Type, Value, ValueId,
    effects::AccessKind,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{BinaryInstKind, InstClassKind, data},
    types::{CompoundType, EnumVariantRef, TypeStore},
};

pub(crate) fn value_may_be_undef(
    func: &Function,
    value: ValueId,
    cache: &mut FxHashMap<ValueId, bool>,
    mut override_value: impl FnMut(ValueId) -> Option<bool>,
) -> bool {
    let mut visiting = FxHashSet::default();
    let mut stack = vec![(value, false)];
    while let Some((value, post_order)) = stack.pop() {
        if cache.contains_key(&value) {
            continue;
        }
        if let Some(may_be_undef) = override_value(value) {
            cache.insert(value, may_be_undef);
            continue;
        }
        if post_order {
            visiting.remove(&value);
            let may_be_undef = match func.dfg.value(value) {
                Value::Undef { .. } => true,
                Value::Immediate { .. } | Value::Arg { .. } | Value::Global { .. } => false,
                Value::Inst { inst, .. } => inst_result_may_be_undef(func, *inst, |used| {
                    cache.get(&used).copied().unwrap_or(true)
                }),
            };
            cache.insert(value, may_be_undef);
            continue;
        }
        if !visiting.insert(value) {
            cache.insert(value, true);
            continue;
        }
        stack.push((value, true));
        if let Value::Inst { inst, .. } = func.dfg.value(value)
            && !is_freeze(func, *inst)
        {
            for used in func.dfg.inst(*inst).collect_values().into_iter().rev() {
                if cache.contains_key(&used) {
                    continue;
                }
                if visiting.contains(&used) {
                    cache.insert(used, true);
                } else {
                    stack.push((used, false));
                }
            }
        }
    }
    cache.get(&value).copied().unwrap_or(true)
}

fn is_freeze(func: &Function, inst: InstId) -> bool {
    func.dfg.downcast::<&data::Freeze>(inst).is_some()
}

/// The values of `func` that may be undef, including the `undef` operands
/// themselves: those an `undef` or an operation with an undefined result
/// reaches. Unlike [`value_may_be_undef`], a cycle
/// of phis that no such source reaches stays defined.
pub(crate) fn maybe_undef_values(func: &Function) -> FxHashSet<ValueId> {
    let mut maybe_undef = FxHashSet::default();
    loop {
        let mut changed = false;
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                for value in func.dfg.inst(inst).collect_values() {
                    if matches!(func.dfg.value(value), Value::Undef { .. }) {
                        changed |= maybe_undef.insert(value);
                    }
                }
                if inst_result_may_be_undef(func, inst, |value| maybe_undef.contains(&value)) {
                    for &result in func.dfg.inst_results(inst) {
                        changed |= maybe_undef.insert(result);
                    }
                }
            }
        }
        if !changed {
            return maybe_undef;
        }
    }
}

/// The scalar values a `freeze` takes: integers, pointers and enum tags.
/// Undef taint is exact for these; an aggregate built from `undef` taints
/// every part of it, even the parts later inserts define.
pub(crate) fn is_scalar(func: &Function, ty: Type) -> bool {
    ty.is_integral() || ty.is_enum_tag() || ty.is_pointer(func.ctx())
}

/// Reads and calls, whose results are never undef.
pub(crate) fn is_read_or_call(func: &Function, inst: InstId) -> bool {
    func.dfg.is_call(inst)
        || func.dfg.downcast::<&data::ObjLoad>(inst).is_some()
        || func.dfg.downcast::<&data::EnumGetTag>(inst).is_some()
        || func
            .dfg
            .effects(inst)
            .accesses
            .iter()
            .any(|access| access.kind == AccessKind::Read)
}

/// Whether `value` is a parameter, global, immediate, read or call result.
fn is_defined_source(func: &Function, value: ValueId) -> bool {
    match func.dfg.value(value) {
        Value::Inst { inst, .. } => is_read_or_call(func, *inst),
        Value::Undef { .. } => false,
        Value::Arg { .. } | Value::Immediate { .. } | Value::Global { .. } => true,
    }
}

/// Whether a value of `ty` holds data: a reference or the unit value holds
/// none, so no part of it is ever undef.
fn holds_data(func: &Function, ty: Type) -> bool {
    !ty.is_unit()
        && func.ctx().with_ty_store(|store| {
            !(store.is_obj_ref(ty) || store.is_const_ref(ty) || store.is_func(ty))
        })
}

/// The field types of a struct or array type.
fn field_tys(func: &Function, ty: Type) -> Option<Vec<Type>> {
    match ty.resolve_compound(func.ctx())? {
        CompoundType::Struct(s) => Some(s.fields),
        CompoundType::Array { elem, len } => Some(vec![elem; len]),
        _ => None,
    }
}

/// Whether one `freeze` per scalar part defines every part of a `ty` value.
/// An enum's parts depend on its variant, and nothing rebuilds an enum from
/// frozen parts.
fn is_freezable(func: &Function, ty: Type) -> bool {
    fn freezable(store: &TypeStore, ty: Type) -> bool {
        let Type::Compound(compound) = ty else {
            return true;
        };
        match store.resolve_compound(compound) {
            CompoundType::Struct(s) => s.fields.iter().all(|&field| freezable(store, field)),
            CompoundType::Array { elem, .. } => freezable(store, *elem),
            CompoundType::Enum(_) => false,
            _ => true,
        }
    }
    func.ctx().with_ty_store(|store| freezable(store, ty))
}

/// Where a field of an aggregate comes from.
enum FieldOrigin {
    /// The value an `insert_value` put there.
    Inserted(ValueId),
    /// A part of this value, which no insert sets.
    Base(ValueId),
}

/// Follows the `insert_value`s that built `aggregate`, and the
/// `extract_value`s it came from, to the origin of field `idx`.
fn field_origin(func: &Function, mut aggregate: ValueId, idx: I256) -> FieldOrigin {
    loop {
        let Some(inst) = func.dfg.value_inst(aggregate) else {
            return FieldOrigin::Base(aggregate);
        };
        if let Some(insert) = func.dfg.downcast::<&data::InsertValue>(inst) {
            match func.dfg.value_imm(*insert.idx()) {
                Some(field) if field.as_i256() == idx => {
                    return FieldOrigin::Inserted(*insert.value());
                }
                Some(_) => aggregate = *insert.dest(),
                None => return FieldOrigin::Base(aggregate),
            }
        } else if let Some(extract) = func.dfg.downcast::<&data::ExtractValue>(inst)
            && let Some(field) = func.dfg.value_imm(*extract.idx())
        {
            match field_origin(func, *extract.dest(), field.as_i256()) {
                FieldOrigin::Inserted(part) => aggregate = part,
                base => return base,
            }
        } else {
            return FieldOrigin::Base(aggregate);
        }
    }
}

/// Inserts `data`, with one result of type `ty`, just before `inst`.
fn insert_before(func: &mut Function, inst: InstId, data: impl Inst, ty: Type) -> ValueId {
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let new = cursor.insert_inst_data_from(func, inst, data);
    let result = cursor.make_result(func, new, ty);
    cursor.attach_result(func, new, result);
    result
}

/// Undef taint while a pass changes a function: [`maybe_undef_values`] for
/// the values that existed when it was made, and a search of the operands of
/// the values created since; the default searches every value. A pass that
/// keeps it must give every value it replaces a defined replacement, as
/// forwarding and inlining here do.
#[derive(Default)]
pub(crate) struct UndefTaint {
    maybe_undef: FxHashSet<ValueId>,
    known: usize,
    new_undef: RefCell<FxHashSet<ValueId>>,
}

impl UndefTaint {
    pub(crate) fn new(func: &Function) -> Self {
        Self {
            maybe_undef: maybe_undef_values(func),
            known: func.dfg.num_values(),
            new_undef: RefCell::default(),
        }
    }

    fn may_be_undef(&self, func: &Function, value: ValueId) -> bool {
        self.search(func, value, &RefCell::default())
    }

    /// Whether an `undef` or an operation with an undefined result reaches
    /// `value`. Each value is searched once; a cycle adds no undef.
    fn search(&self, func: &Function, value: ValueId, seen: &RefCell<FxHashSet<ValueId>>) -> bool {
        if value.index() < self.known {
            return self.maybe_undef.contains(&value);
        }
        if self.new_undef.borrow().contains(&value) {
            return true;
        }
        if !seen.borrow_mut().insert(value) {
            return false;
        }
        let undef = match func.dfg.value(value) {
            Value::Undef { .. } => true,
            Value::Inst { inst, .. } => {
                inst_result_may_be_undef(func, *inst, |used| self.search(func, used, seen))
            }
            _ => false,
        };
        if undef {
            self.new_undef.borrow_mut().insert(value);
        }
        undef
    }

    /// Whether some part of `value` may be undef: a scalar, a field of a
    /// struct or array, or an enum's tag or field. Unlike
    /// [`Self::may_be_undef`], a field is as defined as the value last
    /// inserted there, even into an aggregate that started as undef.
    pub(crate) fn holds_undef(&self, func: &Function, value: ValueId) -> bool {
        self.part_holds_undef(func, value, &mut FxHashSet::default())
    }

    /// [`Self::holds_undef`], entering each phi once: a cycle adds no undef,
    /// and a phi entered again adds nothing new.
    fn part_holds_undef(
        &self,
        func: &Function,
        value: ValueId,
        entered: &mut FxHashSet<ValueId>,
    ) -> bool {
        let ty = func.dfg.value_ty(value);
        if !holds_data(func, ty) || is_defined_source(func, value) {
            return false;
        }
        let Some(inst) = func.dfg.value_inst(value) else {
            return true;
        };
        if let Some(extract) = func.dfg.downcast::<&data::ExtractValue>(inst)
            && let Some(idx) = func.dfg.value_imm(*extract.idx())
        {
            match field_origin(func, *extract.dest(), idx.as_i256()) {
                FieldOrigin::Inserted(part) => return self.part_holds_undef(func, part, entered),
                FieldOrigin::Base(base) if is_defined_source(func, base) => return false,
                FieldOrigin::Base(_) => {}
            }
        }
        if is_scalar(func, ty) {
            return self.may_be_undef(func, value);
        }
        if func.dfg.downcast::<&data::InsertValue>(inst).is_some() {
            return self.fields_hold_undef(func, value, entered);
        }
        if let Some(make) = func.dfg.downcast::<&data::EnumMake>(inst) {
            return make
                .values()
                .iter()
                .any(|&field| self.part_holds_undef(func, field, entered));
        }
        if let Some(phi) = func.dfg.cast_phi(inst) {
            return entered.insert(value)
                && phi
                    .args()
                    .iter()
                    .any(|&(arg, _)| self.part_holds_undef(func, arg, entered));
        }
        self.may_be_undef(func, value)
    }

    /// Whether a field of the `insert_value` chain `value` may hold undef: a
    /// field holds what the last insert into it put there, and the others
    /// what the chain starts from.
    fn fields_hold_undef(
        &self,
        func: &Function,
        mut value: ValueId,
        entered: &mut FxHashSet<ValueId>,
    ) -> bool {
        let len = field_tys(func, func.dfg.value_ty(value)).map_or(0, |fields| fields.len());
        let mut inserted = FxHashSet::default();
        while let Some(insert) = func
            .dfg
            .value_inst(value)
            .and_then(|inst| func.dfg.downcast::<&data::InsertValue>(inst))
        {
            let field = func
                .dfg
                .value_imm(*insert.idx())
                .and_then(Immediate::to_nonnegative_usize)
                .filter(|&field| field < len);
            if field.is_none_or(|field| inserted.insert(field))
                && self.part_holds_undef(func, *insert.value(), entered)
            {
                return true;
            }
            if inserted.len() == len {
                return false;
            }
            value = *insert.dest();
        }
        self.part_holds_undef(func, value, entered)
    }

    /// Whether [`Self::define_before`] leaves no part of `value` undef: any
    /// part of a scalar, struct or array can be frozen, but no enum part.
    pub(crate) fn can_define(&self, func: &Function, value: ValueId) -> bool {
        is_freezable(func, func.dfg.value_ty(value)) || !self.holds_undef(func, value)
    }

    /// `value` with each part that may be undef frozen just before `inst`, for
    /// a transform that puts it where a read, call result or parameter was. A
    /// value [`Self::can_define`] rejects stays as it is.
    pub(crate) fn define_before(
        &self,
        func: &mut Function,
        inst: InstId,
        value: ValueId,
    ) -> ValueId {
        if !self.holds_undef(func, value) || !is_freezable(func, func.dfg.value_ty(value)) {
            return value;
        }
        self.freeze_parts(func, inst, value)
    }

    /// Freezes a scalar `value`, or rebuilds a struct or array from `undef`
    /// with every field, each one that may hold undef in turn frozen, so no
    /// part keeps the undef of the value it came from.
    fn freeze_parts(&self, func: &mut Function, inst: InstId, value: ValueId) -> ValueId {
        let ty = func.dfg.value_ty(value);
        let Some(field_tys) = field_tys(func, ty) else {
            let freeze = data::Freeze::new_unchecked(func.inst_set(), value);
            return insert_before(func, inst, freeze, ty);
        };
        let mut rebuilt = func.dfg.make_undef_value(ty);
        for (idx, field_ty) in field_tys.into_iter().enumerate() {
            let idx = I256::from(idx);
            let idx_value = func.dfg.make_imm_value(idx);
            let mut field = match field_origin(func, value, idx) {
                FieldOrigin::Inserted(field) => field,
                FieldOrigin::Base(base) if matches!(func.dfg.value(base), Value::Undef { .. }) => {
                    func.dfg.make_undef_value(field_ty)
                }
                FieldOrigin::Base(_) => {
                    let extract =
                        data::ExtractValue::new_unchecked(func.inst_set(), value, idx_value);
                    insert_before(func, inst, extract, field_ty)
                }
            };
            if self.holds_undef(func, field) {
                field = self.freeze_parts(func, inst, field);
            }
            let insert =
                data::InsertValue::new_unchecked(func.inst_set(), rebuilt, idx_value, field);
            rebuilt = insert_before(func, inst, insert, ty);
        }
        rebuilt
    }
}

/// Whether field `idx` of `aggregate` may be undef, following `insert_value`
/// and phis to the values that set it. A cycle of phis adds no undef.
fn field_may_be_undef(
    func: &Function,
    aggregate: ValueId,
    idx: I256,
    operand_may_be_undef: &impl Fn(ValueId) -> bool,
    visiting: &mut FxHashSet<ValueId>,
) -> bool {
    if !visiting.insert(aggregate) {
        return false;
    }
    let Some(inst) = func.dfg.value_inst(aggregate) else {
        return operand_may_be_undef(aggregate);
    };
    if let Some(insert) = func.dfg.downcast::<&data::InsertValue>(inst) {
        return match func.dfg.value_imm(*insert.idx()) {
            Some(field) if field.as_i256() == idx => operand_may_be_undef(*insert.value()),
            Some(_) => {
                field_may_be_undef(func, *insert.dest(), idx, operand_may_be_undef, visiting)
            }
            None => operand_may_be_undef(aggregate),
        };
    }
    if let Some(phi) = func.dfg.cast_phi(inst) {
        return phi
            .args()
            .iter()
            .any(|&(arg, _)| field_may_be_undef(func, arg, idx, operand_may_be_undef, visiting));
    }
    operand_may_be_undef(aggregate)
}

/// Whether `field` of `variant` in the enum `value` may be undef, following
/// phis to the `enum.make`s that built it.
fn variant_field_may_be_undef(
    func: &Function,
    value: ValueId,
    variant: EnumVariantRef,
    field: I256,
    operand_may_be_undef: &impl Fn(ValueId) -> bool,
    visiting: &mut FxHashSet<ValueId>,
) -> bool {
    if !visiting.insert(value) {
        return false;
    }
    let Some(inst) = func.dfg.value_inst(value) else {
        return operand_may_be_undef(value);
    };
    if let Some(make) = func.dfg.downcast::<&data::EnumMake>(inst) {
        // An extract runs only on its own variant, which a variant check
        // ensures; another variant's `enum.make` never reaches it.
        return *make.variant() == variant
            && usize::try_from(field.to_u256().low_u64())
                .ok()
                .and_then(|field| make.values().get(field))
                .is_none_or(|&field| operand_may_be_undef(field));
    }
    if let Some(phi) = func.dfg.cast_phi(inst) {
        return phi.args().iter().any(|&(arg, _)| {
            variant_field_may_be_undef(func, arg, variant, field, operand_may_be_undef, visiting)
        });
    }
    operand_may_be_undef(value)
}

fn inst_result_may_be_undef(
    func: &Function,
    inst: InstId,
    operand_may_be_undef: impl Fn(ValueId) -> bool,
) -> bool {
    if is_freeze(func, inst) {
        return false;
    }
    // A field is as defined as the value last inserted there, even into an
    // aggregate that started as undef.
    if let Some(extract) = func.dfg.downcast::<&data::ExtractValue>(inst)
        && let Some(idx) = func.dfg.value_imm(*extract.idx())
    {
        return field_may_be_undef(
            func,
            *extract.dest(),
            idx.as_i256(),
            &operand_may_be_undef,
            &mut FxHashSet::default(),
        );
    }
    if let Some(extract) = func.dfg.downcast::<&data::EnumExtract>(inst)
        && let Some(field) = func.dfg.value_imm(*extract.field())
    {
        return variant_field_may_be_undef(
            func,
            *extract.value(),
            *extract.variant(),
            field.as_i256(),
            &operand_may_be_undef,
            &mut FxHashSet::default(),
        );
    }
    let inst_data = func.dfg.inst(inst);
    let values = inst_data.collect_values();
    if values.iter().copied().any(&operand_may_be_undef) {
        return true;
    }

    if let InstClassKind::Binary(kind) = inst_data.kind()
        && matches!(
            kind,
            BinaryInstKind::Udiv
                | BinaryInstKind::Sdiv
                | BinaryInstKind::Umod
                | BinaryInstKind::Smod
        )
    {
        let [_, rhs] = values.as_slice() else {
            return true;
        };
        return func.dfg.value_imm(*rhs).is_none_or(Immediate::is_zero);
    }

    false
}

#[cfg(test)]
mod tests {
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;

    use super::UndefTaint;

    const SOURCE: &str = r#"
target = "evm-ethereum-osaka"

type @pair = {i256, i256};
type @nested = {i256, @pair};
type @opt = enum {
    #None,
    #Some(i256),
};

func private %source() -> @pair {
block0:
    return undef.@pair;
}

func public %f(v0.i256, v1.@pair, v2.i1) {
block0:
    v3.@pair = insert_value undef.@pair 0.i8 v0;
    v4.@pair = insert_value v3 1.i8 v0;
    v5.@nested = insert_value undef.@nested 1.i8 v4;
    v6.@nested = insert_value v5 0.i8 v0;
    v7.@pair = extract_value v6 1.i8;
    v8.i256 = extract_value v3 1.i8;
    v9.i256 = extract_value v3 0.i8;
    v10.@pair = call %source;
    v11.i256 = extract_value v10 1.i8;
    v12.@pair = insert_value v1 0.i8 undef.i256;
    v13.@opt = enum.make @opt #Some (v0);
    v14.@opt = enum.make @opt #Some (undef.i256);
    v15.@nested = insert_value v6 1.i8 v3;
    br v2 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    v16.@pair = phi (v4 block1) (v3 block2);
    v17.@pair = phi (v4 block1) (v1 block2);
    jump block4;

block4:
    v18.@pair = phi (v4 block3) (v19 block4);
    v19.@pair = insert_value v18 0.i8 v0;
    br v2 block4 block5;

block5:
    return;
}
"#;

    #[test]
    fn holds_undef_follows_each_field() {
        let parsed = parse_module(SOURCE).unwrap();
        let func_ref = parsed.debug.func_order[1];
        let v = |n: usize| parsed.debug.value(func_ref, &format!("v{n}")).unwrap();
        parsed.module.func_store.view(func_ref, |func| {
            let taint = UndefTaint::new(func);
            for (n, holds) in [
                (1, false),
                (3, true),
                (4, false),
                (5, true),
                (6, false),
                (7, false),
                (8, true),
                (9, false),
                (10, false),
                (11, false),
                (12, true),
                (13, false),
                (14, true),
                (15, true),
                (16, true),
                (17, false),
                (18, false),
                (19, false),
            ] {
                assert_eq!(taint.holds_undef(func, v(n)), holds, "v{n}");
            }
            for n in [3, 5, 12, 15] {
                assert!(taint.can_define(func, v(n)), "v{n}");
            }
            assert!(!taint.can_define(func, v(14)));
        });
    }

    #[test]
    fn define_before_freezes_only_undefined_fields() {
        let parsed = parse_module(SOURCE).unwrap();
        let func_ref = parsed.debug.func_order[1];
        let v = |n: usize| parsed.debug.value(func_ref, &format!("v{n}")).unwrap();
        parsed.module.func_store.modify(func_ref, |func| {
            let taint = UndefTaint::new(func);
            let at = func.dfg.value_inst(v(15)).unwrap();
            let next = func.layout.next_inst_of(at).unwrap();
            for n in [3, 5, 12, 15] {
                let defined = taint.define_before(func, next, v(n));
                assert_ne!(defined, v(n), "v{n}");
                assert!(!taint.holds_undef(func, defined), "v{n}");
            }
            assert_eq!(taint.define_before(func, next, v(4)), v(4));
            assert_eq!(taint.define_before(func, next, v(14)), v(14));

            let dumped = FuncWriter::new(func_ref, func).dump_string();
            // `v3` keeps `v0` in its defined field and freezes the other;
            // `v12` takes its defined field out of itself.
            assert!(dumped.contains("freeze undef.i256;"), "{dumped}");
            assert!(dumped.contains("= extract_value v12 1.i256;"), "{dumped}");
            assert!(!dumped.contains("freeze v0"), "{dumped}");
        });
    }
}
