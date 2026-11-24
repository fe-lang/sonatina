//! Small aggregates held in registers. Native code holds a struct, array or
//! enum of a few integer and pointer fields as one value per scalar field, an
//! enum's tag first, rather than as the address of its storage, and private
//! functions pass and return it so. The Cranelift backend translates such
//! values; tail-call analysis passes them as it passes scalars. This module
//! also says which casts native code lowers to nothing, for the inliner.

use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Type,
    inst::{CastInstKind, InstClassKind},
    module::ModuleCtx,
    types::CompoundType,
};
use sonatina_triple::Architecture;

/// Values held in registers have at most this many parts. Cranelift's
/// `tail` convention passes six integer arguments in registers on both
/// x86_64 (rdi to r9) and aarch64 (x2 to x7), so a value of this many parts
/// passes in registers beside one other argument, such as a receiver.
pub const MAX_PARTS: usize = 5;

/// A scalar field, element or enum tag of a value held in registers, at its
/// offset in the value's storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Part {
    pub offset: u32,
    pub ty: Type,
}

pub type Parts = SmallVec<[Part; MAX_PARTS]>;

/// The parts of `ty` if native code holds its values in registers: a struct,
/// array or enum whose scalar fields are at most `MAX_PARTS` integers and
/// pointers of at most a word, of which only one enum variant has any: the
/// others' fields, if they have any, are zero-sized.
pub fn register_parts(ctx: &ModuleCtx, ty: Type) -> Option<Parts> {
    let mut parts = Parts::new();
    (is_aggregate(ctx, ty) && collect_parts(ctx, ty, 0, &mut parts) && !parts.is_empty())
        .then_some(parts)
}

/// Whether `ty` is a struct, array or enum.
pub fn is_aggregate(ctx: &ModuleCtx, ty: Type) -> bool {
    matches!(
        ty.resolve_compound(ctx),
        Some(CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_))
    )
}

/// Whether native code represents `ty` values by the addresses of their
/// storage: an aggregate not held in registers.
pub fn uses_indirect_value_representation(ctx: &ModuleCtx, ty: Type) -> bool {
    is_aggregate(ctx, ty) && register_parts(ctx, ty).is_none()
}

/// Whether native code for the module's target lowers the cast `inst` to no
/// instruction. On the Cranelift targets, with 64-bit registers, those casts
/// are the truncations, the integer-pointer casts that do not widen and the
/// bitcasts between scalars in the same registers, whose result is the
/// operand's registers or the low ones of them; `zext i1 -> i8`, both a
/// byte; and `zext i64 -> i128`, whose zero high word the carry chains and
/// products it feeds fold away. Every other extension emits an instruction,
/// and one to i256 fills limbs; a bitcast to or from an aggregate, or
/// between i256 and another type, goes through memory; and a cast to i1 is
/// masked to its low bit.
///
/// wasm32 holds a pointer or an integer of at most 32 bits in an `i32`, its
/// bits above the width clear, an i64 in an `i64` and a wider integer in
/// `i64` limbs. A truncation to i32 is an `i32.wrap_i64` and one to fewer
/// bits a mask, so only truncations to 64 bits or more are free; a zero
/// extension is free within an `i32`, and from i64 to i128 as above; an
/// `int_to_ptr` from more than 32 bits checks that the address fits; and a
/// `ptr_to_int` is free only to i32.
pub fn is_free_cast(func: &Function, inst: InstId) -> bool {
    let data = func.dfg.inst(inst);
    let InstClassKind::Cast(kind) = data.kind() else {
        return false;
    };
    let values = data.collect_values();
    let ([from], Some(result)) = (values.as_slice(), func.dfg.inst_result(inst)) else {
        return false;
    };
    let ctx = func.ctx();
    let (from, to) = (func.dfg.value_ty(*from), func.dfg.value_ty(result));
    let pointer = ctx.type_layout.pointer_repl();
    let wasm = ctx.triple.architecture == Architecture::Wasm32;
    to != Type::I1
        && match kind {
            CastInstKind::Trunc | CastInstKind::TruncNuw => !wasm || to >= Type::I64,
            CastInstKind::Zext => {
                (from, to) == (Type::I64, Type::I128)
                    || if wasm {
                        to <= Type::I32
                    } else {
                        (from, to) == (Type::I1, Type::I8)
                    }
            }
            CastInstKind::Sext => false,
            CastInstKind::IntToPtr if wasm => from <= pointer,
            CastInstKind::IntToPtr => from >= pointer,
            CastInstKind::PtrToInt if wasm => to == pointer,
            CastInstKind::PtrToInt => to <= pointer,
            CastInstKind::Bitcast => {
                !is_aggregate(ctx, from)
                    && !is_aggregate(ctx, to)
                    && (from == Type::I256) == (to == Type::I256)
            }
        }
}

fn collect_parts(ctx: &ModuleCtx, ty: Type, base: u32, parts: &mut Parts) -> bool {
    match ty.resolve_compound(ctx) {
        Some(CompoundType::Struct(data)) => {
            !data.packed
                && (0..data.fields.len()).all(|idx| {
                    ctx.aggregate_elem_offset(ty, idx)
                        .is_some_and(|(offset, field)| {
                            collect_parts(ctx, field, base + offset as u32, parts)
                        })
                })
        }
        Some(CompoundType::Array { elem, len }) => {
            len <= MAX_PARTS
                && ctx.size_of(elem).is_ok_and(|stride| {
                    (0..len).all(|index| {
                        collect_parts(ctx, elem, base + (index * stride) as u32, parts)
                    })
                })
        }
        Some(CompoundType::Enum(data)) => {
            // The tag, then the parts of the one variant that has any. A
            // variant whose fields are all zero-sized, such as a unit
            // payload, has none.
            push_part(parts, base, data.tag_ty()) && {
                let payload = parts.len();
                data.variants
                    .iter()
                    .enumerate()
                    .all(|(variant, variant_data)| {
                        let start = parts.len();
                        (0..variant_data.fields.len()).all(|field| {
                            ctx.enum_variant_field_offset(ty, variant, field)
                                .is_some_and(|(offset, field_ty)| {
                                    collect_parts(ctx, field_ty, base + offset as u32, parts)
                                })
                        }) && (start == payload || parts.len() == start)
                    })
            }
        }
        Some(CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_)) => {
            push_part(parts, base, ty)
        }
        Some(CompoundType::Func { .. }) => false,
        None => push_part(parts, base, ty),
    }
}

fn push_part(parts: &mut Parts, offset: u32, ty: Type) -> bool {
    let scalar = matches!(
        ty,
        Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Compound(_)
    );
    scalar && parts.len() < MAX_PARTS && {
        parts.push(Part { offset, ty });
        true
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Type;
    use sonatina_parser::parse_module;

    use super::{is_free_cast, register_parts};

    #[test]
    fn values_of_five_scalars_are_held_in_registers() {
        let module = parse_module(
            r#"target = "x86_64-unknown-native"
type @Five = {*i8, i64, i64, *i8, i64};
type @Six = {*i8, i64, i64, *i8, i64, i8};
func private %f(v0.@Five, v1.@Six) {
    block0:
        return;
}
"#,
        )
        .expect("parse should succeed")
        .module;
        let func = module.funcs()[0];
        let [five, six] = module
            .ctx
            .func_sig(func, |sig| [sig.args()[0], sig.args()[1]]);
        let parts = register_parts(&module.ctx, five).expect("five scalars have parts");
        let offsets: Vec<_> = parts.iter().map(|part| part.offset).collect();
        assert_eq!(offsets, [0, 8, 16, 24, 32]);
        assert_eq!(parts[1].ty, Type::I64);
        assert!(register_parts(&module.ctx, six).is_none());
    }

    #[test]
    fn enums_hold_the_tag_and_the_parts_of_their_one_variant_with_parts() {
        let module = parse_module(
            r#"target = "x86_64-unknown-native"
type @Empty = {};
type @Aligned = {[i64; 0]};
type @Fieldless = enum { #Overflow, #OutOfRange };
type @UnitOk = enum { #Ok(@Empty), #Err(@Fieldless) };
type @WordErr = enum { #Ok(@Empty), #Err(i64) };
type @Three = enum { #A(@Empty), #B(i64, i32), #C(@Empty, [i8; 0]) };
type @AllEmpty = enum { #A(@Empty), #B([i8; 0]) };
type @PayloadFirst = enum { #Ok(i64), #Err(@Empty) };
type @AlignedFirst = enum { #A(@Aligned), #B(i8) };
type @Four = enum { #A(@Empty), #B(i64, i64, i64, i64), #C(@Empty) };
type @InStruct = {i32, @UnitOk, i64};
type @Inner = enum { #X(@Empty), #Y(i32) };
type @InEnum = enum { #A(@Empty), #B(@Inner) };
type @TwoPayloads = enum { #Ok(i64), #Err(@Fieldless) };
type @EmptyThenTwo = enum { #A(@Empty), #B(i64), #C(i32) };
type @Five = enum { #A(@Empty), #B(i64, i64, i64, i64, i64) };
type @FourAndOne = enum { #A(@Empty), #B(i64, i64, i64, i64), #C(i8) };
type @Wide = enum { #A(@Empty), #B(i256) };
func private %f(v0.@UnitOk, v1.@WordErr, v2.@Three, v3.@AllEmpty, v4.@PayloadFirst, v5.@AlignedFirst, v6.@Four, v7.@InStruct, v8.@InEnum, v9.@TwoPayloads, v10.@EmptyThenTwo, v11.@Five, v12.@FourAndOne, v13.@Wide) {
    block0:
        return;
}
"#,
        )
        .expect("parse should succeed")
        .module;
        let func = module.funcs()[0];
        let args = module.ctx.func_sig(func, |sig| sig.args().to_vec());
        let parts = |ty| {
            register_parts(&module.ctx, ty)
                .map(|parts| parts.iter().map(|part| (part.offset, part.ty)).collect())
        };
        // Zero-sized fields have no parts, wherever their variant is. Two
        // variants with parts, more than five parts or an `i256` keep an enum
        // in memory.
        let expected: [Option<Vec<_>>; 14] = [
            Some(vec![(0, Type::I1), (1, Type::I1)]),
            Some(vec![(0, Type::I1), (8, Type::I64)]),
            Some(vec![(0, Type::I8), (8, Type::I64), (16, Type::I32)]),
            Some(vec![(0, Type::I1)]),
            Some(vec![(0, Type::I1), (8, Type::I64)]),
            Some(vec![(0, Type::I1), (8, Type::I8)]),
            Some(vec![
                (0, Type::I8),
                (8, Type::I64),
                (16, Type::I64),
                (24, Type::I64),
                (32, Type::I64),
            ]),
            Some(vec![
                (0, Type::I32),
                (4, Type::I1),
                (5, Type::I1),
                (8, Type::I64),
            ]),
            Some(vec![(0, Type::I1), (4, Type::I1), (8, Type::I32)]),
            None,
            None,
            None,
            None,
            None,
        ];
        assert_eq!(args.into_iter().map(parts).collect::<Vec<_>>(), expected);
    }

    #[test]
    fn casts_that_lower_to_nothing_are_free() {
        // Free on a 64-bit Cranelift target and on wasm32; `word` is an
        // integer of pointer width.
        let casts = [
            ("v10.i64 = trunc v1 i64", [true, true]),
            ("v11.i128 = trunc v2 i128", [true, true]),
            ("v12.i8 = trunc_nuw v0 i8", [true, false]),
            ("v13.i1 = trunc v0 i1", [false, false]),
            ("v14.i128 = zext v0 i128", [true, true]),
            ("v15.i8 = zext v4 i8", [true, true]),
            ("v16.i64 = zext v5 i64", [false, false]),
            ("v17.i128 = zext v5 i128", [false, false]),
            ("v18.i256 = zext v0 i256", [false, false]),
            ("v19.i64 = sext v5 i64", [false, false]),
            ("v20.i8 = sext v4 i8", [false, false]),
            ("v21.i128 = sext v0 i128", [false, false]),
            ("v22.*i64 = bitcast v3 *i64", [true, true]),
            ("v23.word = bitcast v3 word", [true, true]),
            ("v24.[i8; 32] = bitcast v2 [i8; 32]", [false, false]),
            ("v25.i256 = bitcast v7 i256", [false, false]),
            ("v26.@Word = bitcast v0 @Word", [false, false]),
            ("v27.i64 = bitcast v6 i64", [false, false]),
            ("v28.*i8 = int_to_ptr v0 *i8", [true, false]),
            ("v29.*i8 = int_to_ptr v2 *i8", [true, false]),
            ("v30.*i8 = int_to_ptr v5 *i8", [false, true]),
            ("v31.i64 = ptr_to_int v3 i64", [true, false]),
            ("v32.i32 = ptr_to_int v3 i32", [true, true]),
            ("v33.i256 = ptr_to_int v3 i256", [false, false]),
            ("v34.i8 = ptr_to_int v3 i8", [true, false]),
            ("v35.i32 = trunc v0 i32", [true, false]),
            ("v36.i32 = zext v4 i32", [false, true]),
            // Not a cast, and of two results.
            ("(v37.i64, v38.i1) = call %pair", [false, false]),
        ];
        for (column, (triple, word)) in [
            ("x86_64-unknown-native", "i64"),
            ("wasm32-unknown-native", "i32"),
        ]
        .into_iter()
        .enumerate()
        {
            let body: String = casts
                .iter()
                .map(|(inst, _)| format!("        {};\n", inst.replace("word", word)))
                .collect();
            let module = parse_module(&format!(
                r#"target = "{triple}"
type @Word = {{i64}};
declare external %pair() -> (i64, i1);
func private %f(v0.i64, v1.i128, v2.i256, v3.*i8, v4.i1, v5.i32, v6.@Word, v7.[i8; 32]) {{
    block0:
{body}        return;
}}
"#
            ))
            .expect("parse should succeed")
            .module;
            let f = module
                .funcs()
                .into_iter()
                .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "f"))
                .unwrap();
            module.func_store.view(f, |func| {
                let insts: Vec<_> = func.layout.iter_all_insts().collect();
                assert_eq!(insts.len(), casts.len() + 1);
                for ((inst, free), &id) in casts.iter().zip(&insts) {
                    assert_eq!(is_free_cast(func, id), free[column], "{triple}: {inst}");
                }
            });
        }
    }
}
