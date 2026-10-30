//! Enum lowering. Natively, `EnumTagLower` turns tags into integers and keeps
//! enums for the backend to lay out. On EVM, object lowering replaces each
//! enum by a struct of its tag and the payload parts its variants share.

use std::{cmp::Reverse, rc::Rc};

use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, Module, Type, Value, ValueId,
    global_variable::GvInitializer,
    inst::{cast, cmp, data},
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeRef, EnumData, EnumVariantRef},
};

use crate::type_rewrite::{TypeRewrite, rewrite_function_type_uses};

/// Rewrites enum tags to their integer types for a backend that lays out
/// enums itself, keeping enum types and instructions.
#[derive(Default)]
pub struct EnumTagLower;

impl EnumTagLower {
    pub fn run(&mut self, module: &Module) -> bool {
        let mut lowerer = TagLowerer::default();
        let mut changed = rewrite_declared_signatures(module, &mut lowerer);
        changed |= lower_global_tags(module, &mut lowerer);
        for func_ref in module.funcs() {
            changed |= module.func_store.modify(func_ref, |function| {
                let tags = lower_tag_immediates(function);
                rewrite_function_type_uses(function, &mut lowerer, |_, _, _| None) || tags
            });
        }
        changed || lowerer.changed
    }
}

#[derive(Default)]
struct TagLowerer {
    changed: bool,
    compound_map: FxHashMap<CompoundTypeRef, Type>,
}

impl TypeRewrite for TagLowerer {
    fn compound_map(&mut self) -> &mut FxHashMap<CompoundTypeRef, Type> {
        &mut self.compound_map
    }

    fn rewrite_leaf_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type {
        tag_int_ty(ctx, ty)
    }

    fn note_compound_remap(&mut self, _compound: CompoundTypeRef, _mapped: Type) {
        self.changed = true;
    }

    fn note_named_compound_update(&mut self, _compound: CompoundTypeRef) {
        self.changed = true;
    }
}

/// `ty`'s integer type if it is an enum tag, else `ty`.
pub(super) fn tag_int_ty(ctx: &ModuleCtx, ty: Type) -> Type {
    let Type::EnumTag(enum_ty) = ty else {
        return ty;
    };
    ctx.with_ty_store(|store| {
        store
            .enum_data(enum_ty)
            .expect("enum tag must reference an enum")
            .tag_ty()
    })
}

fn tag_imm(ctx: &ModuleCtx, variant: EnumVariantRef) -> Immediate {
    let tag_ty = tag_int_ty(ctx, Type::EnumTag(variant.enum_ty()));
    Immediate::from_i256(I256::from(u64::from(variant.index())), tag_ty)
}

fn rewrite_declared_signatures(module: &Module, lowerer: &mut impl TypeRewrite) -> bool {
    // Declaration maps iterate in hash order; rewriting in that order would
    // create lowered types in a different order on each run.
    let mut funcs: Vec<_> = module
        .ctx
        .declared_funcs
        .iter()
        .map(|entry| *entry.key())
        .collect();
    funcs.sort_unstable();
    let mut changed = false;

    for func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        let new_args: Vec<_> = sig
            .args()
            .iter()
            .map(|&arg| lowerer.rewrite_type(&module.ctx, arg))
            .collect();
        let new_rets: Vec<_> = sig
            .ret_tys()
            .iter()
            .map(|&ret| lowerer.rewrite_type(&module.ctx, ret))
            .collect();
        if new_args == sig.args() && new_rets == sig.ret_tys() {
            continue;
        }

        module
            .ctx
            .declared_funcs
            .get_mut(&func)
            .expect("declared signature must exist")
            .clone_from(&sonatina_ir::Signature::new(
                sig.name(),
                sig.linkage(),
                &new_args,
                &new_rets,
            ));
        changed = true;
    }

    changed
}

/// Rewrites global types with `lowerer` and enum tag immediates in their
/// initializers to integers. Initializers hold no enums.
pub(super) fn lower_global_tags(module: &Module, lowerer: &mut impl TypeRewrite) -> bool {
    let globals: Vec<_> = module
        .ctx
        .with_gv_store(|store| store.all_gv_refs().collect());
    let mut changed = false;

    for gv in globals {
        let Some(gv_data) = module.ctx.with_gv_store(|store| store.get(gv).cloned()) else {
            continue;
        };
        let new_ty = lowerer.rewrite_type(&module.ctx, gv_data.ty);
        let new_initializer = gv_data
            .initializer
            .clone()
            .map(|init| lower_initializer_tags(&module.ctx, init));
        if new_ty != gv_data.ty || new_initializer != gv_data.initializer {
            module.ctx.with_gv_store_mut(|store| {
                store.update_ty(gv, new_ty);
                store.update_initializer(gv, new_initializer);
            });
            changed = true;
        }
    }

    changed
}

fn lower_initializer_tags(ctx: &ModuleCtx, init: GvInitializer) -> GvInitializer {
    match init {
        GvInitializer::Immediate(imm) => GvInitializer::Immediate(lower_imm_tag(ctx, imm)),
        GvInitializer::Array(items) => GvInitializer::Array(
            items
                .into_iter()
                .map(|item| lower_initializer_tags(ctx, item))
                .collect(),
        ),
        GvInitializer::Struct(fields) => GvInitializer::Struct(
            fields
                .into_iter()
                .map(|field| lower_initializer_tags(ctx, field))
                .collect(),
        ),
    }
}

fn lower_imm_tag(ctx: &ModuleCtx, imm: Immediate) -> Immediate {
    match imm {
        Immediate::EnumTag { enum_ty, value } => {
            Immediate::from_i256(value, tag_int_ty(ctx, Type::EnumTag(enum_ty)))
        }
        imm => imm,
    }
}

/// Replaces `function`'s enum tag immediates by integers, which a type
/// rewrite cannot retype.
pub(super) fn lower_tag_immediates(function: &mut Function) -> bool {
    let tags: Vec<_> = function
        .dfg
        .immediates
        .iter()
        .filter(|(imm, _)| matches!(imm, Immediate::EnumTag { .. }))
        .map(|(&imm, &value)| (imm, value))
        .collect();
    for &(imm, value) in &tags {
        let lowered = lower_imm_tag(function.ctx(), imm);
        function.dfg.immediates.remove(&imm);
        function.dfg.immediates.entry(lowered).or_insert(value);
        function.dfg.values[value] = Value::Immediate {
            imm: lowered,
            ty: lowered.ty(),
        };
    }
    !tags.is_empty()
}

/// An enum lowered for EVM memory, where every type with bytes takes whole
/// 32-byte words: a struct of its tag and payload parts. Every variant's
/// fields start at the payload's first word.
///
/// Each payload word has the type of every variant's leaf there joined: the
/// widest integer, or a pointer if any variant has one. A part is the largest
/// field, or child of a field, whose leaves are the joined words it covers;
/// other variants' fields there map to its nodes and leaves.
#[derive(Debug)]
pub(super) struct LoweredEnum {
    ty: Type,
    tag_ty: Type,
    /// The struct's fields after the tag: each part's first word and type.
    parts: Vec<(u32, Type)>,
    /// Each variant's fields: their first words and lowered types.
    fields: Vec<Vec<(u32, Type)>>,
}

impl LoweredEnum {
    fn field(&self, variant: EnumVariantRef, field: usize) -> (u32, Type) {
        self.fields[variant.index() as usize][field]
    }

    /// The path from the struct to the node of type `ty` at payload `word`,
    /// or else to the word's leaf, with each step's index and type.
    fn path(&self, ctx: &ModuleCtx, word: u32, ty: Type) -> SmallVec<[(u32, Type); 4]> {
        let part = self.parts.partition_point(|&(at, _)| at <= word) - 1;
        let (mut at, mut node) = self.parts[part];
        let mut path = smallvec![(part as u32 + 1, node)];
        while !(at == word && node == ty)
            && let Some(children) = children(ctx, node)
        {
            let (index, child) = children
                .into_iter()
                .enumerate()
                .find(|&(_, child)| {
                    let end = at + words(ctx, child);
                    let contains = word < end;
                    if !contains {
                        at = end;
                    }
                    contains
                })
                .expect("a part covers its words");
            node = child;
            path.push((index as u32, node));
        }
        path
    }
}

/// The enums a type rewrite has lowered to structs, by enum.
#[derive(Default)]
pub(super) struct LoweredEnums(FxHashMap<CompoundTypeRef, Rc<LoweredEnum>>);

/// A type rewrite that lowers enums to their EVM structs.
pub(super) trait EnumWordRewrite: TypeRewrite + Sized {
    fn lowered_enums(&mut self) -> &mut LoweredEnums;
}

/// Lowers `enum_ty` to a struct of its tag and shared payload parts, its
/// fields lowered by `rewriter`.
pub(super) fn lower_enum_type<R: EnumWordRewrite>(
    rewriter: &mut R,
    ctx: &ModuleCtx,
    enum_ty: CompoundTypeRef,
    data: &EnumData,
) -> Type {
    let name = format!("__enum_lowered_{}_{}", data.name, enum_ty.as_u32());
    let lowered = ctx.with_ty_store_mut(|store| {
        store
            .lookup_struct(&name)
            .map(Type::Compound)
            .unwrap_or_else(|| store.make_struct(&name, &[], false))
    });
    // A payload may point back to this enum.
    rewriter.compound_map().insert(enum_ty, lowered);

    let variants: Vec<Vec<Type>> = data
        .variants
        .iter()
        .map(|variant| {
            variant
                .fields
                .iter()
                .map(|&field| rewriter.rewrite_type(ctx, field))
                .collect()
        })
        .collect();
    let parts = payload_parts(ctx, &variants);
    let fields = variants
        .into_iter()
        .map(|fields| {
            let mut word = 0;
            fields
                .into_iter()
                .map(|ty| {
                    let at = word;
                    word += words(ctx, ty);
                    (at, ty)
                })
                .collect()
        })
        .collect();
    let tag_ty = data.tag_ty();
    let struct_fields: Vec<_> = std::iter::once(tag_ty)
        .chain(parts.iter().map(|&(_, ty)| ty))
        .collect();
    ctx.with_ty_store_mut(|store| store.update_struct_fields(&name, &struct_fields));
    rewriter.lowered_enums().0.insert(
        enum_ty,
        Rc::new(LoweredEnum {
            ty: lowered,
            tag_ty,
            parts,
            fields,
        }),
    );
    lowered
}

/// The parts that `variants`' fields, lowered, share: see `LoweredEnum`.
fn payload_parts(ctx: &ModuleCtx, variants: &[Vec<Type>]) -> Vec<(u32, Type)> {
    // The type each payload word must hold: every variant's leaf there joined.
    let leaves: Vec<Vec<Type>> = variants
        .iter()
        .map(|fields| fields.iter().flat_map(|&ty| word_leaves(ctx, ty)).collect())
        .collect();
    let width = leaves.iter().map(Vec::len).max().unwrap_or(0);
    let joined: Vec<Type> = (0..width)
        .map(|word| {
            let tys: Vec<Type> = leaves
                .iter()
                .filter_map(|tys| tys.get(word).copied())
                .collect();
            join_words(ctx, &tys)
        })
        .collect();

    // Each variant's fields not yet placed, the next on top, starting at `word`.
    let mut pending: Vec<Vec<Type>> = variants
        .iter()
        .map(|fields| fields.iter().rev().copied().collect())
        .collect();
    let mut parts = Vec::new();
    let mut word = 0;
    while word < width {
        for fields in &mut pending {
            while fields.last().is_some_and(|&ty| words(ctx, ty) == 0) {
                fields.pop();
            }
        }
        // The first of the largest fields starting here whose leaves are the
        // joined words.
        let part = pending
            .iter()
            .filter_map(|fields| fields.last().copied())
            .filter(|&ty| {
                let leaves = word_leaves(ctx, ty);
                !leaves.is_empty() && joined[word..].starts_with(&leaves)
            })
            .min_by_key(|&ty| Reverse(words(ctx, ty)));
        let Some(part) = part else {
            for fields in &mut pending {
                if let Some(&ty) = fields.last()
                    && let Some(children) = children(ctx, ty)
                {
                    fields.pop();
                    fields.extend(children.into_iter().rev());
                }
            }
            continue;
        };
        let end = word + words(ctx, part) as usize;
        for fields in &mut pending {
            let mut at = word;
            while at < end
                && let Some(ty) = fields.pop()
            {
                let size = words(ctx, ty) as usize;
                if at + size <= end {
                    at += size;
                } else {
                    // Only an aggregate straddles a part's end.
                    fields.extend(children(ctx, ty).unwrap().into_iter().rev());
                }
            }
        }
        parts.push((word as u32, part));
        word = end;
    }
    parts
}

/// The single-word leaves of `ty` in EVM memory order.
fn word_leaves(ctx: &ModuleCtx, ty: Type) -> Vec<Type> {
    match children(ctx, ty) {
        Some(children) => children
            .into_iter()
            .flat_map(|child| word_leaves(ctx, child))
            .collect(),
        None if words(ctx, ty) == 0 => Vec::new(),
        None => vec![ty],
    }
}

/// The words `ty` takes in EVM memory.
fn words(ctx: &ModuleCtx, ty: Type) -> u32 {
    let size = ctx
        .size_of(ty)
        .unwrap_or_else(|err| panic!("enum payload type {ty:?} has no EVM layout: {err:?}"));
    u32::try_from(size / 32).expect("enum payload too large")
}

/// The fields or elements of aggregate `ty`.
fn children(ctx: &ModuleCtx, ty: Type) -> Option<Vec<Type>> {
    match ty.resolve_compound(ctx)? {
        CompoundType::Struct(data) => Some(data.fields),
        CompoundType::Array { elem, len } => Some(vec![elem; len]),
        _ => None,
    }
}

/// One word type that holds every single-word type in `tys`: the first
/// pointer, else the widest integer.
fn join_words(ctx: &ModuleCtx, tys: &[Type]) -> Type {
    if let Some(&ptr) = tys
        .iter()
        .find(|&&ty| ctx.with_ty_store(|store| store.is_ptr(ty)))
    {
        return ptr;
    }
    tys.iter()
        .copied()
        .reduce(|a, b| {
            assert!(
                a.is_integral() && b.is_integral(),
                "an EVM enum payload word cannot hold both {a:?} and {b:?}"
            );
            if a >= b { a } else { b }
        })
        .expect("a payload word holds a field")
}

/// Lowers enum instruction `inst` in `func`, whose types `rewriter` has
/// lowered and whose objects are pointers. Returns whether it was one.
pub(super) fn lower_enum_inst<R: EnumWordRewrite>(
    rewriter: &mut R,
    func: &mut Function,
    inst: InstId,
) -> bool {
    let mut layout = |func: &Function, variant: EnumVariantRef| {
        rewriter.rewrite_type(func.ctx(), Type::Compound(variant.enum_ty()));
        Rc::clone(&rewriter.lowered_enums().0[&variant.enum_ty()])
    };
    let replacement = if let Some(make) = func.dfg.downcast::<&data::EnumMake>(inst).cloned() {
        let layout = layout(func, *make.variant());
        let tag = func
            .dfg
            .make_imm_value(tag_imm(func.ctx(), *make.variant()));
        let mut value = func.dfg.make_undef_value(layout.ty);
        value = insert_value(func, inst, value, 0, tag);
        for (field, &payload) in make.values().iter().enumerate() {
            let (word, ty) = layout.field(*make.variant(), field);
            value = write_word_value(func, inst, &layout, value, word, ty, payload);
        }
        Some(value)
    } else if let Some(tag) = func.dfg.downcast::<&data::EnumTag>(inst).cloned() {
        let tag_ty = func.dfg.value_ty(func.dfg.inst_result(inst).unwrap());
        Some(extract_value(func, inst, *tag.value(), 0, tag_ty))
    } else if let Some(is_variant) = func.dfg.downcast::<&data::EnumIsVariant>(inst).cloned() {
        let layout = layout(func, *is_variant.variant());
        let tag = extract_value(func, inst, *is_variant.value(), 0, layout.tag_ty);
        let expected = func
            .dfg
            .make_imm_value(tag_imm(func.ctx(), *is_variant.variant()));
        let is = func.inst_set();
        Some(insert_before(
            func,
            inst,
            cmp::Eq::new_unchecked(is, tag, expected),
            Type::I1,
        ))
    } else if func
        .dfg
        .downcast::<&data::EnumAssertVariant>(inst)
        .is_some()
    {
        None
    } else if let Some(assert) = func.dfg.downcast::<&data::EnumAssertVariantRef>(inst) {
        Some(*assert.object())
    } else if let Some(extract) = func.dfg.downcast::<&data::EnumExtract>(inst).cloned() {
        let layout = layout(func, *extract.variant());
        let (word, ty) = layout.field(*extract.variant(), field_index(func, *extract.field()));
        Some(read_word_value(
            func,
            inst,
            &layout,
            *extract.value(),
            word,
            ty,
        ))
    } else if let Some(proj) = func.dfg.downcast::<&data::EnumProj>(inst).cloned() {
        let layout = layout(func, *proj.variant());
        let (word, ty) = layout.field(*proj.variant(), field_index(func, *proj.field()));
        Some(field_ptr(func, inst, &layout, *proj.object(), word, ty))
    } else if let Some(get_tag) = func.dfg.downcast::<&data::EnumGetTag>(inst).cloned() {
        let tag_ty = func.dfg.value_ty(func.dfg.inst_result(inst).unwrap());
        let tag_ptr = part_ptr(func, inst, *get_tag.object(), 0, tag_ty);
        let is = func.inst_set();
        Some(insert_before(
            func,
            inst,
            data::Mload::new_unchecked(is, tag_ptr, tag_ty),
            tag_ty,
        ))
    } else if let Some(set_tag) = func.dfg.downcast::<&data::EnumSetTag>(inst).cloned() {
        let layout = layout(func, *set_tag.variant());
        store_tag(func, inst, &layout, *set_tag.object(), *set_tag.variant());
        None
    } else if let Some(write) = func.dfg.downcast::<&data::EnumWriteVariant>(inst).cloned() {
        let layout = layout(func, *write.variant());
        for (field, &payload) in write.values().iter().enumerate() {
            let (word, ty) = layout.field(*write.variant(), field);
            if words(func.ctx(), ty) != 0 {
                let ptr = field_ptr(func, inst, &layout, *write.object(), word, ty);
                let is = func.inst_set();
                insert_before_no_result(
                    func,
                    inst,
                    data::Mstore::new_unchecked(is, ptr, payload, ty),
                );
            }
        }
        store_tag(func, inst, &layout, *write.object(), *write.variant());
        None
    } else {
        return false;
    };

    if let Some(result) = func.dfg.inst_result(inst)
        && let Some(replacement) = replacement
    {
        func.dfg.change_to_alias(result, replacement);
    }
    func.layout.remove_inst(inst);
    func.erase_inst(inst);
    true
}

fn field_index(func: &Function, field: ValueId) -> usize {
    func.dfg
        .value_imm(field)
        .and_then(|imm| imm.to_nonnegative_usize())
        .expect("enum field index must be a non-negative immediate")
}

/// Inserts `value`, of type `ty` at payload `word`, into enum value `dest`.
fn write_word_value(
    func: &mut Function,
    before: InstId,
    layout: &LoweredEnum,
    dest: ValueId,
    word: u32,
    ty: Type,
    value: ValueId,
) -> ValueId {
    if words(func.ctx(), ty) == 0 {
        return dest;
    }
    let path = layout.path(func.ctx(), word, ty);
    let node_ty = path.last().unwrap().1;
    if node_ty == ty {
        return insert_path(func, before, dest, &path, value);
    }
    let Some(children) = children(func.ctx(), ty) else {
        let value = cast_word(func, before, value, node_ty);
        return insert_path(func, before, dest, &path, value);
    };
    let mut dest = dest;
    let mut at = word;
    for (index, child) in children.into_iter().enumerate() {
        let child_value = extract_value(func, before, value, index as u32, child);
        dest = write_word_value(func, before, layout, dest, at, child, child_value);
        at += words(func.ctx(), child);
    }
    dest
}

/// The value of type `ty` at payload `word` of enum value `src`.
fn read_word_value(
    func: &mut Function,
    before: InstId,
    layout: &LoweredEnum,
    src: ValueId,
    word: u32,
    ty: Type,
) -> ValueId {
    if words(func.ctx(), ty) == 0 {
        return func.dfg.make_undef_value(ty);
    }
    let path = layout.path(func.ctx(), word, ty);
    let node_ty = path.last().unwrap().1;
    if node_ty == ty {
        return extract_path(func, before, src, &path);
    }
    let Some(children) = children(func.ctx(), ty) else {
        let leaf = extract_path(func, before, src, &path);
        return cast_word(func, before, leaf, ty);
    };
    let mut value = func.dfg.make_undef_value(ty);
    let mut at = word;
    for (index, child) in children.into_iter().enumerate() {
        let child_value = read_word_value(func, before, layout, src, at, child);
        value = insert_value(func, before, value, index as u32, child_value);
        at += words(func.ctx(), child);
    }
    value
}

fn extract_path(
    func: &mut Function,
    before: InstId,
    src: ValueId,
    path: &[(u32, Type)],
) -> ValueId {
    path.iter().fold(src, |value, &(index, ty)| {
        extract_value(func, before, value, index, ty)
    })
}

fn insert_path(
    func: &mut Function,
    before: InstId,
    dest: ValueId,
    path: &[(u32, Type)],
    value: ValueId,
) -> ValueId {
    let Some((&(index, ty), rest)) = path.split_first() else {
        return value;
    };
    let value = if rest.is_empty() {
        value
    } else {
        let child = inserted_part(func, dest, index)
            .unwrap_or_else(|| extract_value(func, before, dest, index, ty));
        insert_path(func, before, child, rest, value)
    };
    insert_value(func, before, dest, index, value)
}

/// Part `index` of `value` when `value` is undef or inserts its parts
/// directly, as an enum value under construction does.
fn inserted_part(func: &mut Function, value: ValueId, index: u32) -> Option<ValueId> {
    if let Value::Undef { ty } = *func.dfg.value(value) {
        let part_ty = children(func.ctx(), ty)?[index as usize];
        return Some(func.dfg.make_undef_value(part_ty));
    }
    let insert = func
        .dfg
        .downcast::<&data::InsertValue>(func.dfg.value_inst(value)?)?
        .clone();
    if func.dfg.value_imm(*insert.idx())?.to_nonnegative_usize()? == index as usize {
        Some(*insert.value())
    } else {
        inserted_part(func, *insert.dest(), index)
    }
}

/// A pointer to the field of type `ty` at payload `word` of the enum at
/// `base`.
fn field_ptr(
    func: &mut Function,
    before: InstId,
    layout: &LoweredEnum,
    base: ValueId,
    word: u32,
    ty: Type,
) -> ValueId {
    let ptr_ty = func.ctx().with_ty_store_mut(|store| store.make_ptr(ty));
    // A field without words reads nothing; any address in the enum will do.
    if words(func.ctx(), ty) == 0 {
        return bitcast_before(func, before, base, ptr_ty);
    }
    let path = layout.path(func.ctx(), word, ty);
    let node_ty = path.last().unwrap().1;
    let mut indices: SmallVec<[ValueId; 8]> = smallvec![base, func.dfg.make_imm_value(0i64)];
    indices.extend(
        path.iter()
            .map(|&(index, _)| func.dfg.make_imm_value(i64::from(index))),
    );
    let node_ptr_ty = func
        .ctx()
        .with_ty_store_mut(|store| store.make_ptr(node_ty));
    let is = func.inst_set();
    let ptr = insert_before(
        func,
        before,
        data::Gep::new_unchecked(is, indices),
        node_ptr_ty,
    );
    if node_ty == ty {
        ptr
    } else {
        bitcast_before(func, before, ptr, ptr_ty)
    }
}

fn part_ptr(func: &mut Function, before: InstId, base: ValueId, part: u32, ty: Type) -> ValueId {
    let zero = func.dfg.make_imm_value(0i64);
    let index = func.dfg.make_imm_value(i64::from(part));
    let ptr_ty = func.ctx().with_ty_store_mut(|store| store.make_ptr(ty));
    let is = func.inst_set();
    insert_before(
        func,
        before,
        data::Gep::new_unchecked(is, smallvec![base, zero, index]),
        ptr_ty,
    )
}

fn store_tag(
    func: &mut Function,
    before: InstId,
    layout: &LoweredEnum,
    base: ValueId,
    variant: EnumVariantRef,
) {
    let tag_ptr = part_ptr(func, before, base, 0, layout.tag_ty);
    let tag = func.dfg.make_imm_value(tag_imm(func.ctx(), variant));
    let is = func.inst_set();
    insert_before_no_result(
        func,
        before,
        data::Mstore::new_unchecked(is, tag_ptr, tag, layout.tag_ty),
    );
}

/// Converts single-word `value` to word type `to`.
fn cast_word(func: &mut Function, before: InstId, value: ValueId, to: Type) -> ValueId {
    let from = func.dfg.value_ty(value);
    if from == to {
        return value;
    }
    let is = func.inst_set();
    let is_ptr = |ty| func.ctx().with_ty_store(|store| store.is_ptr(ty));
    match (is_ptr(from), is_ptr(to)) {
        (true, true) => bitcast_before(func, before, value, to),
        (true, false) => insert_before(
            func,
            before,
            cast::PtrToInt::new_unchecked(is, value, to),
            to,
        ),
        (false, true) => insert_before(
            func,
            before,
            cast::IntToPtr::new_unchecked(is, value, to),
            to,
        ),
        (false, false) if from < to => {
            insert_before(func, before, cast::Zext::new_unchecked(is, value, to), to)
        }
        (false, false) => {
            insert_before(func, before, cast::Trunc::new_unchecked(is, value, to), to)
        }
    }
}

fn bitcast_before(func: &mut Function, before: InstId, value: ValueId, to: Type) -> ValueId {
    let is = func.inst_set();
    insert_before(
        func,
        before,
        cast::Bitcast::new_unchecked(is, value, to),
        to,
    )
}

fn insert_value(
    func: &mut Function,
    before: InstId,
    dest: ValueId,
    index: u32,
    value: ValueId,
) -> ValueId {
    let ty = func.dfg.value_ty(dest);
    let index = func.dfg.make_imm_value(i64::from(index));
    let is = func.inst_set();
    insert_before(
        func,
        before,
        data::InsertValue::new_unchecked(is, dest, index, value),
        ty,
    )
}

fn extract_value(
    func: &mut Function,
    before: InstId,
    src: ValueId,
    index: u32,
    ty: Type,
) -> ValueId {
    let index = func.dfg.make_imm_value(i64::from(index));
    let is = func.inst_set();
    insert_before(
        func,
        before,
        data::ExtractValue::new_unchecked(is, src, index),
        ty,
    )
}

fn insert_before(func: &mut Function, before: InstId, data: impl Inst, ty: Type) -> ValueId {
    let inst = insert_before_no_result(func, before, data);
    let result = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    func.dfg.attach_result(inst, result);
    result
}

fn insert_before_no_result(func: &mut Function, before: InstId, data: impl Inst) -> InstId {
    let inst = func.dfg.make_inst(data);
    func.propagate_inst_attribution(inst, before);
    func.layout.insert_inst_before(inst, before);
    inst
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Type, types::CompoundType};

    use super::super::ObjectLowerToMemory;
    use crate::test_support::{lookup_func, parse_test_module};

    #[test]
    fn variants_share_payload_parts_down_to_conflicting_words() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"
type @Point = {i256, i256};
type @Option = enum { #None, #Some(@Point) };
type @Mixed = enum { #None, #Pt(@Point), #Narrow(i8, i256), #Flag(i1) };
type @Arr = enum { #Arr([i64; 3]), #Pair(i256, i1) };
type @RefOrNum = enum { #Ref(objref<i256>), #Num(i64) };
type @Zero = enum { #Z([i64; 0], i64), #W(i256) };
type @Inner = enum { #Small(i8), #Wide(i256, i64) };
type @Outer = enum { #Off, #On(@Inner, i64), #Raw(i256, i256, i256) };
type @Code = enum { #A, #B, #C };
type @Result = enum { #Err(@Code), #Ok(@Point) };
type @Narrow = {i8, i256};
type @Split = enum { #A(@Narrow), #B(i256, i256) };
func public %f(v0.@Option, v1.@Mixed, v2.@Arr, v3.@RefOrNum, v4.@Zero, v5.@Outer, v6.@Result, v7.@Split) {
block0:
    return;
}
"#,
        );
        let ctx = &module.ctx;
        let f = lookup_func(&module, "f");
        let sizes: Vec<_> = ctx
            .func_sig(f, |sig| sig.args().to_vec())
            .into_iter()
            .map(|ty| ctx.size_of(ty).unwrap())
            .collect();
        ObjectLowerToMemory.run(&module);

        let point =
            ctx.with_ty_store(|store| Type::Compound(store.lookup_struct("Point").unwrap()));
        let ptr = ctx.with_ty_store_mut(|store| store.make_ptr(Type::I256));
        let (i1, i8, i64, i256) = (Type::I1, Type::I8, Type::I64, Type::I256);
        let expected = [
            // One variant with a payload keeps its fields.
            vec![i1, point],
            // `Pt`'s point holds `Narrow`'s and `Flag`'s fields.
            vec![i8, point],
            vec![i1, i256, i64, i64],
            // A word holding a pointer or an integer stays a pointer.
            vec![i1, ptr],
            // `Z`'s empty array takes no word.
            vec![i1, i256],
            // `On`'s inner enum splits: `Raw` needs a wider first word.
            vec![i8, i256, i256, i256, i64],
            // `Ok`'s point holds `Err`'s tag.
            vec![i1, point],
            // `A`'s struct splits: its first word is narrower than `B`'s.
            vec![i1, i256, i256],
        ];
        let args = ctx.func_sig(f, |sig| sig.args().to_vec());
        for ((arg, fields), size) in args.into_iter().zip(expected).zip(sizes) {
            let Some(CompoundType::Struct(lowered)) = arg.resolve_compound(ctx) else {
                panic!("{arg:?} should lower to a struct");
            };
            assert_eq!(lowered.fields, fields, "{}", lowered.name);
            assert_eq!(ctx.size_of(arg).unwrap(), size, "{}", lowered.name);
        }
    }
}
