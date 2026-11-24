//! Folding of private functions with the same machine code.
//!
//! A module may hold several functions that compile alike: instances of one
//! source function for different kinds of the same argument, or for type
//! arguments its code does not depend on. The object receives a function as
//! its code bytes, alignment and relocations only, so two functions with the
//! same ones are the same function wherever their relocations name the same
//! targets. Calls between such functions compare by the function called:
//! two calls are alike if their callees are, which holds of recursive
//! functions too.

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    mem,
};

use cranelift_codegen::{
    Context, FinalizedRelocTarget,
    binemit::{Addend, CodeOffset, Reloc},
    ir::{self as clif, ExternalName, TrapCode, UserExternalName},
};
use sonatina_ir::module::FuncRef;

use super::FUNC_NAMESPACE;

/// The functions of `functions` with the machine code of an earlier one,
/// each with the first such function.
pub(super) fn duplicates<'a>(
    functions: impl IntoIterator<Item = (FuncRef, &'a Context)>,
) -> HashMap<FuncRef, FuncRef> {
    let (funcs, shapes): (Vec<_>, Vec<_>) = functions
        .into_iter()
        .map(|(func_ref, ctx)| (func_ref, Shape::new(ctx)))
        .unzip();
    let positions: HashMap<_, _> = funcs
        .iter()
        .enumerate()
        .map(|(index, &func_ref)| (func_ref, index))
        .collect();
    let mut callers = vec![Vec::new(); funcs.len()];
    for (caller, shape) in shapes.iter().enumerate() {
        for (slot, callee) in shape.callees.iter().enumerate() {
            if let Some(&callee) = positions.get(callee) {
                callers[callee].push((caller, slot));
            }
        }
    }

    // Functions start in one class per shape and callees outside `functions`,
    // which are only themselves, and split while the classes of their other
    // callees differ, so recursive functions alike throughout stay together.
    // Each round compares only the callers of the functions that changed
    // class in the previous one, all of them at first, by those callees' new
    // classes: the members of a class agreed before those changes, so callers
    // alike in them stay together, and apart from the members not compared,
    // which call older classes there. The largest part of a class keeps it,
    // so a function changes class at most 1 + log2 n times, and the
    // refinement takes O((n + m) log² n) for n functions and m calls between
    // them.
    let mut ids = HashMap::new();
    let mut classes: Vec<usize> = shapes
        .iter()
        .map(|shape| {
            let outside: Vec<_> = shape
                .callees
                .iter()
                .map(|callee| (!positions.contains_key(callee)).then_some(*callee))
                .collect();
            let id = ids.len();
            *ids.entry((&shape.code, outside)).or_insert(id)
        })
        .collect();
    let mut members = vec![Vec::new(); ids.len()];
    let mut places: Vec<usize> = classes
        .iter()
        .enumerate()
        .map(|(index, &class)| {
            members[class].push(index);
            members[class].len() - 1
        })
        .collect();
    let mut changes = vec![Vec::new(); funcs.len()];
    let mut moved: Vec<usize> = (0..funcs.len()).collect();
    loop {
        let mut compared = Vec::new();
        for callee in moved.drain(..) {
            for &(caller, slot) in &callers[callee] {
                if changes[caller].is_empty() {
                    compared.push(caller);
                }
                changes[caller].push((slot, classes[callee]));
            }
        }
        if compared.is_empty() {
            break;
        }
        let mut keys: Vec<_> = compared
            .into_iter()
            .map(|index| {
                let mut slots = mem::take(&mut changes[index]);
                slots.sort_unstable();
                (classes[index], slots, index)
            })
            .collect();
        keys.sort_unstable();
        for split in keys.chunk_by(|a, b| a.0 == b.0) {
            // Each group of alike callers leaves for a part of its own.
            let class = split[0].0;
            let mut parts = Vec::new();
            for group in split.chunk_by(|a, b| a.1 == b.1) {
                let part = members.len();
                members.push(Vec::new());
                for &(_, _, index) in group {
                    let place = places[index];
                    members[class].swap_remove(place);
                    if let Some(&other) = members[class].get(place) {
                        places[other] = place;
                    }
                    places[index] = members[part].len();
                    members[part].push(index);
                    classes[index] = part;
                }
                parts.push(part);
            }
            if let Some(&largest) = parts.iter().max_by_key(|&&part| members[part].len())
                && members[largest].len() > members[class].len()
            {
                members.swap(class, largest);
                for &index in &members[class] {
                    classes[index] = class;
                }
                for &index in &members[largest] {
                    classes[index] = largest;
                }
            }
            moved.extend(parts.iter().flat_map(|&part| &members[part]));
        }
    }

    let mut first = HashMap::new();
    funcs
        .iter()
        .zip(&classes)
        .filter_map(|(&func_ref, &class)| {
            let first = *first.entry(class).or_insert(func_ref);
            (first != func_ref).then_some((func_ref, first))
        })
        .collect()
}

/// What the object receives of a compiled function, with the module's
/// functions it names in `callees`, in relocation order.
struct Shape<'a> {
    code: Code<'a>,
    callees: Vec<FuncRef>,
}

impl<'a> Shape<'a> {
    fn new(ctx: &'a Context) -> Self {
        let compiled = ctx
            .compiled_code()
            .expect("folding runs on compiled functions");
        let names = ctx.func.params.user_named_funcs();
        let mut callees = Vec::new();
        let relocs = compiled
            .buffer
            .relocs()
            .iter()
            .map(|reloc| {
                let target = match &reloc.target {
                    FinalizedRelocTarget::ExternalName(ExternalName::User(name))
                        if names[*name].namespace == FUNC_NAMESPACE =>
                    {
                        callees.push(FuncRef::from_u32(names[*name].index));
                        Target::Callee
                    }
                    FinalizedRelocTarget::ExternalName(ExternalName::User(name)) => {
                        Target::Symbol(names[*name].clone())
                    }
                    target => Target::Other(target.clone()),
                };
                (reloc.offset, reloc.kind, reloc.addend, target)
            })
            .collect();
        Self {
            code: Code {
                signature: &ctx.func.signature,
                alignment: compiled.buffer.alignment,
                bytes: compiled.code_buffer(),
                relocs,
                traps: compiled
                    .buffer
                    .traps()
                    .iter()
                    .map(|trap| (trap.offset, trap.code))
                    .collect(),
            },
            callees,
        }
    }
}

/// A compiled function's code and relocations, without the functions of the
/// module it calls. Its trap records are not in the object, but are compared
/// all the same.
#[derive(PartialEq, Eq)]
struct Code<'a> {
    signature: &'a clif::Signature,
    alignment: u32,
    bytes: &'a [u8],
    relocs: Vec<(CodeOffset, Reloc, Addend, Target)>,
    traps: Vec<(CodeOffset, TrapCode)>,
}

/// `Reloc` has no `Hash`, so a relocation's kind hashes as its variant.
impl Hash for Code<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.signature.hash(state);
        self.alignment.hash(state);
        self.bytes.hash(state);
        self.relocs.len().hash(state);
        for (offset, kind, addend, target) in &self.relocs {
            (offset, mem::discriminant(kind), addend, target).hash(state);
        }
        self.traps.hash(state);
    }
}

/// What a relocation refers to: a function of the module, which `Shape`
/// names in its `callees`, another symbol, or a place in its own function.
#[derive(PartialEq, Eq, Hash)]
enum Target {
    Callee,
    Symbol(UserExternalName),
    Other(FinalizedRelocTarget),
}

#[cfg(test)]
mod tests {
    use cranelift_codegen::{
        control::ControlPlane,
        ir::{AbiParam, GlobalValueData, InstBuilder, immediates::Imm64, types},
        settings,
    };
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

    use super::*;

    fn compile(
        returns: clif::Type,
        body: impl FnOnce(&mut FunctionBuilder) -> clif::Value,
    ) -> Context {
        let isa = cranelift_native::builder()
            .unwrap()
            .finish(settings::Flags::new(settings::builder()))
            .unwrap();
        let mut ctx = Context::new();
        ctx.func.signature.returns.push(AbiParam::new(returns));
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);
        let value = body(&mut builder);
        builder.ins().return_(&[value]);
        builder.finalize(isa.frontend_config());
        ctx.compile(&*isa, &mut ControlPlane::default()).unwrap();
        ctx
    }

    /// The address `offset` bytes into a data symbol: a relocation's addend.
    fn symbol_address(offset: i64) -> Context {
        compile(types::I64, |builder| {
            let name = builder
                .func
                .declare_imported_user_function(UserExternalName::new(1, 0));
            let symbol = builder.create_global_value(GlobalValueData::Symbol {
                name: ExternalName::user(name),
                offset: Imm64::new(offset),
                colocated: false,
                tls: false,
            });
            builder.ins().symbol_value(types::I64, symbol)
        })
    }

    /// What the function of index `callee` returns, plus `addend`.
    fn call(callee: u32, addend: i64) -> Context {
        compile(types::I64, |builder| {
            let signature = builder.func.signature.clone();
            let signature = builder.import_signature(signature);
            let name = builder
                .func
                .declare_imported_user_function(UserExternalName::new(FUNC_NAMESPACE, callee));
            let callee = builder.import_function(clif::ExtFuncData {
                name: ExternalName::user(name),
                signature,
                colocated: true,
                patchable: false,
            });
            let call = builder.ins().call(callee, &[]);
            let value = builder.inst_results(call)[0];
            builder.ins().iadd_imm_s(value, addend)
        })
    }

    /// The duplicates of `functions`, each the function of its index, by
    /// index.
    fn duplicate_indices(functions: &[Context]) -> Vec<(u32, u32)> {
        let mut duplicates: Vec<_> = duplicates(
            functions
                .iter()
                .zip(0..)
                .map(|(ctx, index)| (FuncRef::from_u32(index), ctx)),
        )
        .into_iter()
        .map(|(duplicate, first)| (duplicate.as_u32(), first.as_u32()))
        .collect();
        duplicates.sort_unstable();
        duplicates
    }

    #[test]
    fn chains_of_calls_fold_where_their_ends_do() {
        // Three chains of calls alike but for the callee: the last two end
        // in the same constant and fold link by link, the first ends in
        // another and stays apart all the way up. The last function has the
        // links' code and calls itself, so it is like none of them.
        const LINKS: u32 = 8;
        let chain = LINKS + 1;
        let mut functions: Vec<_> = [1, 2, 2]
            .into_iter()
            .zip((0..).step_by(chain as usize))
            .flat_map(|(end, start)| {
                (start + 1..=start + LINKS)
                    .map(|callee| call(callee, 1))
                    .chain([compile(types::I64, |builder| {
                        builder.ins().iconst(types::I64, end)
                    })])
            })
            .collect();
        functions.push(call(3 * chain, 1));
        assert_eq!(
            duplicate_indices(&functions),
            (2 * chain..3 * chain)
                .map(|index| (index, index - chain))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn recursive_functions_alike_throughout_fold() {
        // A cycle of three calls alike throughout is one function, as are a
        // pair and a function calling into the cycle. In a cycle of three
        // with one member adding another number the members differ, and its
        // twin folds into it member by member.
        let functions = [
            call(1, 1),
            call(2, 1),
            call(0, 1),
            call(4, 1),
            call(3, 1),
            call(6, 1),
            call(7, 1),
            call(5, 2),
            call(9, 1),
            call(10, 1),
            call(8, 2),
            call(0, 1),
        ];
        assert_eq!(
            duplicate_indices(&functions),
            [
                (1, 0),
                (2, 0),
                (3, 0),
                (4, 0),
                (8, 5),
                (9, 6),
                (10, 7),
                (11, 0)
            ]
        );
    }

    #[test]
    fn functions_differing_in_an_addend_or_a_constant_stay_apart() {
        let functions = [
            symbol_address(0),
            symbol_address(8),
            symbol_address(0),
            compile(types::F64, |builder| builder.ins().f64const(0.1)),
            compile(types::F64, |builder| builder.ins().f64const(0.2)),
        ];
        let duplicates = duplicates(
            functions
                .iter()
                .enumerate()
                .map(|(index, ctx)| (FuncRef::from_u32(index as u32), ctx)),
        );
        assert_eq!(
            duplicates,
            HashMap::from([(FuncRef::from_u32(2), FuncRef::from_u32(0))])
        );
    }
}
