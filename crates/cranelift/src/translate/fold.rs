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

    // Each function's class is its first member. Functions start in one class
    // per shape and split while their callees' classes differ, so recursive
    // functions alike throughout stay together.
    let mut first = HashMap::new();
    let mut classes: Vec<usize> = shapes
        .iter()
        .enumerate()
        .map(|(index, shape)| *first.entry(&shape.code).or_insert(index))
        .collect();
    loop {
        let mut first = HashMap::new();
        let next: Vec<usize> = shapes
            .iter()
            .enumerate()
            .map(|(index, shape)| {
                // A callee outside `functions` is only itself.
                let callees: Vec<_> = shape
                    .callees
                    .iter()
                    .map(|callee| {
                        positions
                            .get(callee)
                            .map(|&callee| classes[callee])
                            .ok_or(*callee)
                    })
                    .collect();
                *first.entry((classes[index], callees)).or_insert(index)
            })
            .collect();
        if next == classes {
            break;
        }
        classes = next;
    }

    classes
        .iter()
        .enumerate()
        .filter(|&(index, &class)| index != class)
        .map(|(index, &class)| (funcs[index], funcs[class]))
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
