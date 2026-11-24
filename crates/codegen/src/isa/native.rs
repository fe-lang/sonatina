//! Small aggregates held in registers. Native code holds a struct, array or
//! enum of a few integer and pointer fields as one value per scalar field, an
//! enum's tag first, rather than as the address of its storage, and private
//! functions pass and return it so. The Cranelift backend translates such
//! values; tail-call analysis passes them as it passes scalars.

use smallvec::SmallVec;
use sonatina_ir::{Type, module::ModuleCtx, types::CompoundType};

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

    use super::register_parts;

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
}
