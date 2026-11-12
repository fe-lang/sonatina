//! Translation of a wasm32 Sonatina module to a WAFFLE module.
//!
//! WAFFLE takes SSA with block parameters, so Sonatina phi nodes become block
//! parameters, and recovers structured control flow when the module is
//! encoded. The integer lowerings live in [`super::arith`], the 256-bit ones in
//! [`super::wide`] and the layout of linear memory in [`super::memory`]. The
//! aggregate and memory instructions are in the `aggregate` submodule.
//!
//! Every instruction of the native instruction set is matched explicitly. An
//! instruction that is not translated returns an error naming it; no
//! instruction is skipped.
//!
//! # Values
//!
//! An integer of at most 64 bits is one WebAssembly value. A pointer, an
//! `objref`, a `constref` and a value of struct or array type are one `i32`:
//! the address of the value in linear memory (aggregates live in memory, as
//! on the native target). A 256-bit integer is four `i64` values and a 128-bit
//! integer two.
//!
//! # Frames
//!
//! When a module needs linear-memory storage, every function takes the address
//! of the first free byte of the stack as a hidden first parameter, places its
//! frame there, and passes the end of its frame to the functions it calls. No
//! mutable stack pointer exists, so a trap leaves nothing to repair. An exported
//! function is a thin wrapper that starts the stack at the `stack_top` global.

use std::collections::hash_map::Entry;

use rustc_hash::{FxHashMap, FxHashSet};
use waffle::{
    BlockTarget, ExportKind, Func, FuncDecl, FunctionBody, MemoryArg, Module as WaffleModule,
    Operator, Signature, SignatureData, Terminator, Type as WType, ValueDef, entity::EntityRef,
};

use sonatina_codegen::{
    OptLevel,
    analysis::tail_position::{tail_callers, tail_position_calls},
};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Immediate, Inst, InstId, Linkage, Module, Type, Value,
    ValueId,
    inst::{
        control_flow::Call, data::SymbolRef, inst_set::InstSetExt, native::inst_set::NativeInstKind,
    },
    isa::native::inst_set as native_inst_set,
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};

use super::{
    HOST_ALLOCATOR_EXPORTS, WasmError,
    arith::{Arith, Cmp, DivRem, Emit, Int, Shift},
    heap::{self, Mode},
    memory::{
        self, ALIGN, MemoryPlan, RuntimeGlobals, align_up, build_arena_mark,
        declare_runtime_globals,
    },
    sha256,
    tail::TailCallSites,
    wide::{self, LIMBS, Limbs, Wide},
};
mod aggregate;
mod wide_ops;

use wide_ops::{WideHelpers, WideOp, constant_shift};

type V = waffle::Value;

pub(super) struct Translated {
    pub(super) module: WaffleModule<'static>,
    /// Exported function names, in module order.
    pub(super) exports: Vec<String>,
    /// The functions that make tail calls, with the callees of those calls.
    pub(super) tail_calls: TailCallSites,
}

fn unsupported(message: String) -> WasmError {
    WasmError::Unsupported(message)
}

fn invalid(message: String) -> WasmError {
    WasmError::Invalid(message)
}

/// How a Sonatina type is held by WebAssembly values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Repr {
    /// An integer of at most 64 bits: one value.
    Int(Int),
    /// A 128- or 256-bit integer: two or four `i64` values.
    Wide(Wide),
    /// A pointer, `objref` or `constref`: an `i32` address.
    Pointer,
    /// A struct or array: an `i32` address of the value in memory.
    Aggregate,
}

fn repr(ctx: &ModuleCtx, ty: Type) -> Option<Repr> {
    if let Some(int) = Int::from_type(ty) {
        return Some(Repr::Int(int));
    }
    if let Some(wide) = Wide::from_type(ty) {
        return Some(Repr::Wide(wide));
    }
    match ty.resolve_compound(ctx)? {
        CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => {
            Some(Repr::Pointer)
        }
        CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_) => {
            Some(Repr::Aggregate)
        }
        CompoundType::Func { .. } => None,
    }
}

impl Repr {
    fn push_carriers(self, out: &mut Vec<WType>) {
        match self {
            Self::Int(int) => out.push(int.carrier()),
            Self::Wide(wide) => out.extend(std::iter::repeat_n(WType::I64, wide.limbs())),
            Self::Pointer | Self::Aggregate => out.push(WType::I32),
        }
    }
}

/// The type of storage that a function returns through its hidden buffer, if
/// it does: a single struct, array or enum result. A `constref` result is the
/// address of its constant, which no call overwrites.
fn indirect_return_storage(ctx: &ModuleCtx, rets: &[Type]) -> Option<Type> {
    let [ty] = rets else {
        return None;
    };
    match ty.resolve_compound(ctx)? {
        CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_) => Some(*ty),
        _ => None,
    }
}

fn type_name(ctx: &ModuleCtx, ty: Type) -> String {
    match ty {
        Type::Unit => "unit".to_string(),
        Type::I1 => "i1".to_string(),
        Type::I8 => "i8".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I64 => "i64".to_string(),
        Type::I128 => "i128".to_string(),
        Type::I256 => "i256".to_string(),
        Type::EnumTag(_) => "an enum tag".to_string(),
        Type::Compound(_) => match ty.resolve_compound(ctx) {
            Some(CompoundType::Ptr(_)) => "a pointer",
            Some(CompoundType::ObjRef(_)) => "an object reference",
            Some(CompoundType::ConstRef(_)) => "a constant reference",
            Some(CompoundType::Array { .. }) => "an array",
            Some(CompoundType::Struct(_)) => "a struct",
            Some(CompoundType::Enum(_)) => "an enum",
            Some(CompoundType::Func { .. }) => "a function type",
            None => "an unresolved compound type",
        }
        .to_string(),
    }
}

/// The value a `br_table` compares with its cases.
#[derive(Clone, Copy)]
enum Scrutinee {
    Int(Int, V),
    Wide(Limbs),
}

/// What a call goes to.
#[derive(Clone, Copy)]
enum CallTarget {
    Func(Func),
    /// The C routine `memmove` or `memcpy`, which is `memory.copy` in the
    /// module and not an import.
    MemoryCopy,
    /// The C routine `malloc` with a 32-bit size, which is the allocator of the
    /// module and not an import.
    HeapMalloc,
    /// The C routine `free`, which is the allocator of the module and not an
    /// import.
    HeapFree,
}

/// A function the module can call: its WAFFLE index and its Sonatina signature.
struct Callee {
    target: CallTarget,
    params: Vec<Type>,
    rets: Vec<Type>,
    /// Results of an import come from the host and are not known to be
    /// canonical.
    is_import: bool,
    /// The function takes the stack top as a hidden first parameter.
    stack_param: bool,
    /// The function returns its single aggregate result through a hidden
    /// buffer whose address is its next parameter. The type is the storage.
    sret: Option<Type>,
}

/// What a scan of the module found that decides the shape of the output.
struct Scan {
    runtime: bool,
    arena: bool,
    /// The module declares the external C routine `free`, so it needs a `free`
    /// function.
    free: bool,
    /// Which 256-bit helper functions are used: multiplication, division, left
    /// and right shifts.
    helpers: (bool, bool, bool, bool, bool, bool),
    /// The module uses `sha256_compress`.
    sha256: bool,
}

fn kind_needs_runtime(kind: &NativeInstKind<'_>) -> bool {
    matches!(
        kind,
        NativeInstKind::Alloca(_)
            | NativeInstKind::ObjAlloc(_)
            | NativeInstKind::ConstRef(_)
            | NativeInstKind::ConstProj(_)
            | NativeInstKind::ConstIndex(_)
            | NativeInstKind::ConstLoad(_)
            | NativeInstKind::ObjProj(_)
            | NativeInstKind::ObjIndex(_)
            | NativeInstKind::ObjLoad(_)
            | NativeInstKind::ObjStore(_)
            | NativeInstKind::ObjMaterializeStack(_)
            | NativeInstKind::InsertValue(_)
            | NativeInstKind::ExtractValue(_)
            | NativeInstKind::EnumMake(_)
            | NativeInstKind::MemAllocDynamic(_)
            | NativeInstKind::Sha256Compress(_)
    )
}

/// The operation of an instruction that calls a 256-bit helper when its
/// operands are 128- or 256-bit, and its two operands.
fn wide_op_of(kind: &NativeInstKind<'_>) -> Option<(WideOp, ValueId, ValueId)> {
    Some(match kind {
        NativeInstKind::Mul(i) => (WideOp::Mul, *i.lhs(), *i.rhs()),
        NativeInstKind::Umulo(i) => (WideOp::Umulo, *i.lhs(), *i.rhs()),
        NativeInstKind::Smulo(i) => (WideOp::Smulo, *i.lhs(), *i.rhs()),
        NativeInstKind::Umulsat(i) => (WideOp::Umulsat, *i.lhs(), *i.rhs()),
        NativeInstKind::Smulsat(i) => (WideOp::Smulsat, *i.lhs(), *i.rhs()),
        NativeInstKind::Udiv(i) => (WideOp::Udiv, *i.lhs(), *i.rhs()),
        NativeInstKind::Umod(i) => (WideOp::Umod, *i.lhs(), *i.rhs()),
        NativeInstKind::Sdiv(i) => (WideOp::Sdiv, *i.lhs(), *i.rhs()),
        NativeInstKind::Smod(i) => (WideOp::Smod, *i.lhs(), *i.rhs()),
        NativeInstKind::Shl(i) => (WideOp::Shl, *i.value(), *i.bits()),
        NativeInstKind::Shr(i) => (WideOp::Shr, *i.value(), *i.bits()),
        NativeInstKind::Sar(i) => (WideOp::Sar, *i.value(), *i.bits()),
        _ => return None,
    })
}

fn scan_module(module: &Module) -> Scan {
    let mut runtime = module.ctx.with_gv_store(|store| !store.is_empty());
    let mut arena = false;
    let mut free = false;
    let mut helpers = (false, false, false, false, false, false);
    let mut sha256 = false;
    let mut called = FxHashSet::default();
    let inst_set = native_inst_set();
    for func_ref in module.funcs() {
        let is_aggregate = |ty: Type| {
            matches!(
                repr(&module.ctx, ty),
                Some(Repr::Aggregate) | None if ty != Type::Unit && !ty.is_enum_tag()
            ) || matches!(
                ty.resolve_compound(&module.ctx),
                Some(CompoundType::ObjRef(_) | CompoundType::ConstRef(_))
            )
        };
        module.ctx.func_sig(func_ref, |sig| {
            if sig
                .args()
                .iter()
                .chain(sig.ret_tys())
                .any(|ty| is_aggregate(*ty))
            {
                runtime = true;
            }
        });
        module.func_store.try_view(func_ref, |function| {
            for block in function.layout.iter_block() {
                for inst_id in function.layout.iter_inst(block) {
                    let inst = function.dfg.inst(inst_id);
                    if !inst_set.contains_inst(inst) {
                        continue;
                    }
                    let kind = inst_set.resolve_inst(inst);
                    if kind_needs_runtime(&kind) {
                        runtime = true;
                    }
                    if let NativeInstKind::Call(call) = &kind {
                        called.insert(*call.callee());
                    }
                    if matches!(kind, NativeInstKind::MemAllocDynamic(_)) {
                        arena = true;
                    }
                    if matches!(kind, NativeInstKind::Sha256Compress(_)) {
                        sha256 = true;
                    }
                    // A shift by a constant and a 128-bit product are built
                    // in place.
                    if let Some((op, lhs, rhs)) = wide_op_of(&kind)
                        && let Some(wide) = Wide::from_type(function.dfg.value_ty(lhs))
                        && !(matches!(op, WideOp::Shl | WideOp::Shr | WideOp::Sar)
                            && constant_shift(function, rhs).is_some())
                        && !(op == WideOp::Mul && wide == Wide::I128)
                    {
                        let (mulo, divrem, shl, shr) = op.needs();
                        helpers.0 |= mulo;
                        helpers.1 |= divrem;
                        helpers.2 |= shl;
                        helpers.3 |= shr;
                    }
                    // Modular arithmetic of every width runs at 256 bits.
                    match &kind {
                        NativeInstKind::EvmAddMod(_) => {
                            helpers.1 = true;
                            helpers.4 = true;
                        }
                        NativeInstKind::EvmMulMod(_) => helpers.5 = true,
                        _ => {}
                    }
                }
            }
            for (value, _) in function.dfg.values_iter() {
                if is_aggregate(function.dfg.value_ty(value)) {
                    runtime = true;
                }
            }
        });
    }
    // The C routines `malloc` and `free` are the allocator of the module, which
    // only a call to one of them needs.
    for func_ref in called {
        if module.ctx.func_linkage(func_ref) == Linkage::External {
            let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
            if matches!(name.as_str(), "malloc" | "free") {
                runtime = true;
                arena = true;
                free |= name == "free";
            }
        }
    }
    Scan {
        runtime,
        arena,
        free,
        helpers,
        sha256,
    }
}

pub(super) fn translate_module(
    module: &Module,
    import_module: &str,
    stack_bytes: u32,
    host_allocator: bool,
    heap_poison: bool,
    opt_level: OptLevel,
) -> Result<Translated, WasmError> {
    let mut scan = scan_module(module);
    if host_allocator {
        scan.runtime = true;
        scan.arena = true;
    }
    let plan = memory::plan_memory(module, scan.runtime, scan.arena, scan.sha256, stack_bytes)?;

    let mut wmod = WaffleModule::empty();
    // Linear memory is always present and exported, so scalar loads and stores
    // and host access share one contract. It may grow.
    let memory = wmod.memories.push(waffle::MemoryData {
        initial_pages: plan.initial_pages,
        maximum_pages: None,
        segments: plan.segments.clone(),
    });
    wmod.exports.push(waffle::Export {
        name: "memory".to_string(),
        kind: ExportKind::Memory(memory),
    });
    let globals = plan
        .runtime
        .then(|| declare_runtime_globals(&mut wmod, &plan));

    let funcs = module.funcs();
    let mut callees: FxHashMap<FuncRef, Callee> = FxHashMap::default();
    let mut exports = Vec::new();
    let mut export_names: FxHashSet<String> = FxHashSet::default();
    export_names.insert("memory".to_string());
    if host_allocator {
        export_names.extend(HOST_ALLOCATOR_EXPORTS.map(String::from));
    }

    // WAFFLE requires imported functions to take the lowest function indexes,
    // so declare every import before any defined function.
    let mut definitions = Vec::new();
    for &func_ref in &funcs {
        let name = module.ctx.func_sig(func_ref, |sig| sig.name().to_string());
        let linkage = module.ctx.func_linkage(func_ref);
        let has_body = module
            .func_store
            .try_view(func_ref, |function| function.layout.entry_block().is_some())
            .unwrap_or(false);

        match (linkage, has_body) {
            (Linkage::External, false) if matches!(name.as_str(), "malloc" | "free") => {
                let target = heap_call_target(module, func_ref, &name)?;
                let (params, rets) = module.ctx.func_sig(func_ref, |sig| {
                    (sig.args().to_vec(), sig.ret_tys().to_vec())
                });
                callees.insert(
                    func_ref,
                    Callee {
                        target,
                        params,
                        rets,
                        is_import: false,
                        stack_param: false,
                        sret: None,
                    },
                );
            }
            (Linkage::External, false) if is_memory_copy_declaration(module, func_ref, &name) => {
                let (params, rets) = module.ctx.func_sig(func_ref, |sig| {
                    (sig.args().to_vec(), sig.ret_tys().to_vec())
                });
                callees.insert(
                    func_ref,
                    Callee {
                        target: CallTarget::MemoryCopy,
                        params,
                        rets,
                        is_import: false,
                        stack_param: false,
                        sret: None,
                    },
                );
            }
            (Linkage::External, false) => {
                let signature = declared_signature(module, func_ref, &name, &plan, true)?;
                let wsig = memory::signature(&mut wmod, signature.wasm);
                let func = wmod.funcs.push(FuncDecl::Import(wsig, name.clone()));
                wmod.imports.push(waffle::Import {
                    module: import_module.to_string(),
                    name,
                    kind: waffle::ImportKind::Func(func),
                });
                callees.insert(
                    func_ref,
                    Callee {
                        target: CallTarget::Func(func),
                        params: signature.params,
                        rets: signature.rets,
                        is_import: true,
                        stack_param: false,
                        sret: None,
                    },
                );
            }
            (Linkage::External, true) => {
                return Err(invalid(format!(
                    "function `{name}` is external but has a body"
                )));
            }
            (Linkage::Public | Linkage::Private, false) => {
                return Err(invalid(format!(
                    "function `{name}` is defined in this module but has no body"
                )));
            }
            (Linkage::Public | Linkage::Private, true) => {
                definitions.push((func_ref, name, linkage))
            }
        }
    }

    // Declare every defined function before translating bodies so calls
    // resolve regardless of definition order.
    let mut pending = Vec::new();
    let mut wrappers = Vec::new();
    for (func_ref, name, linkage) in definitions {
        let public = linkage == Linkage::Public;
        if public && host_allocator && HOST_ALLOCATOR_EXPORTS.contains(&name.as_str()) {
            return Err(invalid(format!(
                "export name `{name}` is reserved for the host allocator"
            )));
        }
        if public && !export_names.insert(name.clone()) {
            return Err(invalid(format!(
                "export name `{name}` is used by more than one function or by the memory"
            )));
        }
        if public {
            exports.push(name.clone());
        }
        // The function that other functions call. With a runtime it takes the
        // stack top, so an export is a wrapper around it.
        let inner = declared_signature(module, func_ref, &name, &plan, false)?;
        if public {
            check_exportable(module, func_ref, &name)?;
        }
        let stack_param = plan.runtime;
        let sret = inner.sret;
        let wsig = memory::signature(&mut wmod, inner.wasm);
        let placeholder = FunctionBody::new(&wmod, wsig);
        let inner_name = if public && plan.runtime {
            format!("{name}$body")
        } else {
            name.clone()
        };
        let func = wmod
            .funcs
            .push(FuncDecl::Body(wsig, inner_name.clone(), placeholder));
        if public && plan.runtime {
            let exported = declared_signature(module, func_ref, &name, &plan, true)?;
            let export_sig = memory::signature(&mut wmod, exported.wasm);
            let placeholder = FunctionBody::new(&wmod, export_sig);
            let wrapper = wmod
                .funcs
                .push(FuncDecl::Body(export_sig, name.clone(), placeholder));
            wmod.exports.push(waffle::Export {
                name: name.clone(),
                kind: ExportKind::Func(wrapper),
            });
            wrappers.push((
                wrapper,
                export_sig,
                func,
                inner.params.clone(),
                inner.rets.clone(),
            ));
        } else if public {
            wmod.exports.push(waffle::Export {
                name: name.clone(),
                kind: ExportKind::Func(func),
            });
        }
        callees.insert(
            func_ref,
            Callee {
                target: CallTarget::Func(func),
                params: inner.params,
                rets: inner.rets,
                is_import: false,
                stack_param,
                sret,
            },
        );
        pending.push((func_ref, func, wsig, inner_name, public && !plan.runtime));
    }

    // The allocator of the module: `malloc` serves `mem.alloc_dynamic` and the
    // external C routine of that name, and `free` the external C routine.
    let arena_func = if plan.arena {
        let sig = heap::alloc_signature(&mut wmod);
        let placeholder = FunctionBody::new(&wmod, sig);
        Some((
            wmod.funcs
                .push(FuncDecl::Body(sig, "heap_malloc".to_string(), placeholder)),
            sig,
        ))
    } else {
        None
    };
    let free_func = if scan.free {
        let sig = heap::consume_signature(&mut wmod);
        let placeholder = FunctionBody::new(&wmod, sig);
        Some((
            wmod.funcs
                .push(FuncDecl::Body(sig, "heap_free".to_string(), placeholder)),
            sig,
        ))
    } else {
        None
    };

    // The SHA-256 compression that `sha256_compress` calls.
    let sha256_func = scan.sha256.then(|| {
        let sig = sha256::signature(&mut wmod);
        let placeholder = FunctionBody::new(&wmod, sig);
        let func = wmod
            .funcs
            .push(FuncDecl::Body(sig, sha256::NAME.to_string(), placeholder));
        (func, sig)
    });

    // The 256-bit helpers that the bodies call.
    let mut helpers = WideHelpers::default();
    let mut helper_bodies = Vec::new();
    let wide_results = |count: usize| vec![WType::I64; count];
    let mut declare = |wmod: &mut WaffleModule<'static>,
                       name: &str,
                       operands: usize,
                       results: Vec<WType>,
                       kind: HelperKind| {
        let sig = wide::helper_signature(wmod, operands * LIMBS, &results);
        let placeholder = FunctionBody::new(wmod, sig);
        let func = wmod
            .funcs
            .push(FuncDecl::Body(sig, name.to_string(), placeholder));
        helper_bodies.push((func, sig, name.to_string(), kind));
        func
    };
    let (needs_mulo, needs_divrem, needs_shl, needs_shr, needs_addmod, needs_mulmod) = scan.helpers;
    if needs_mulo {
        let mut results = wide_results(LIMBS);
        results.push(WType::I32);
        helpers.mulo = Some(declare(
            &mut wmod,
            "i256.mulo",
            2,
            results,
            HelperKind::Mulo,
        ));
    }
    if needs_divrem {
        helpers.udivrem = Some(declare(
            &mut wmod,
            "i256.udivrem",
            2,
            wide_results(2 * LIMBS),
            HelperKind::DivRem,
        ));
    }
    if needs_shl {
        helpers.shl = Some(declare(
            &mut wmod,
            "i256.shl",
            2,
            wide_results(LIMBS),
            HelperKind::Shift { left: true },
        ));
    }
    if needs_shr {
        helpers.shr = Some(declare(
            &mut wmod,
            "i256.shr",
            2,
            wide_results(LIMBS),
            HelperKind::Shift { left: false },
        ));
    }
    if needs_addmod {
        helpers.addmod = Some(declare(
            &mut wmod,
            "i256.addmod",
            3,
            wide_results(LIMBS),
            HelperKind::Modular { product: false },
        ));
    }
    if needs_mulmod {
        helpers.mulmod = Some(declare(
            &mut wmod,
            "i256.mulmod",
            3,
            wide_results(LIMBS),
            HelperKind::Modular { product: true },
        ));
    }

    let tail_callers: FxHashSet<FuncRef> = tail_callers(module).into_iter().collect();
    let mut tail_calls = TailCallSites::default();
    for (func_ref, func, wsig, name, canonicalize_params) in pending {
        let body = module
            .func_store
            .try_view(func_ref, |function| {
                let sites = if tail_callers.contains(&func_ref) {
                    tail_call_sites(module, func_ref, function, &callees)
                } else {
                    FxHashMap::default()
                };
                if !sites.is_empty() {
                    tail_calls.insert(func.index() as u32, sites.values().copied().collect());
                }
                FunctionTranslator::new(
                    module,
                    function,
                    func_ref,
                    &name,
                    &wmod,
                    wsig,
                    memory,
                    &callees,
                    &plan,
                    globals,
                    arena_func.map(|(func, _)| func),
                    free_func.map(|(func, _)| func),
                    sha256_func.map(|(func, _)| func),
                    helpers,
                    sites.into_keys().collect(),
                    opt_level,
                )
                .translate(canonicalize_params)
            })
            .ok_or_else(|| invalid(format!("function `{name}` has no body")))??;
        wmod.funcs[func] = FuncDecl::Body(wsig, name, body);
    }

    for (wrapper, export_sig, inner, params, rets) in wrappers {
        let globals = globals.expect("a wrapper exists only with a runtime");
        let body = build_wrapper(&wmod, export_sig, inner, &params, &rets, globals)?;
        let name = match &wmod.funcs[wrapper] {
            FuncDecl::Body(_, name, _) => name.clone(),
            _ => unreachable!("a wrapper is a defined function"),
        };
        wmod.funcs[wrapper] = FuncDecl::Body(export_sig, name, body);
    }

    for (func, sig, name, kind) in helper_bodies {
        let body = match kind {
            HelperKind::Mulo => wide::build_mulo(&wmod, sig),
            HelperKind::DivRem => wide::build_udivrem(&wmod, sig),
            HelperKind::Shift { left } => wide::build_shift(&wmod, sig, left),
            HelperKind::Modular { product: true } => wide::build_mulmod(&wmod, sig),
            HelperKind::Modular { product: false } => {
                let udivrem = helpers
                    .udivrem
                    .expect("modular addition is declared with the division helper");
                wide::build_addmod(&wmod, sig, udivrem)
            }
        };
        wmod.funcs[func] = FuncDecl::Body(sig, name, body);
    }

    if let Some((func, sig)) = sha256_func {
        let body = sha256::build_compress(&wmod, sig, memory, plan.sha256);
        wmod.funcs[func] = FuncDecl::Body(sig, sha256::NAME.to_string(), body);
    }

    if let Some((func, sig)) = arena_func {
        // A heap exists only with a runtime, which has the globals.
        let globals = globals.expect("a heap exists only with a runtime");
        let arena_top = globals
            .arena_top
            .expect("the heap global exists with a heap");
        let arena_last = globals
            .arena_last
            .expect("the heap global exists with a heap");
        let lists = plan.lists;
        let body = heap::build_malloc(
            &wmod,
            sig,
            memory,
            arena_top,
            arena_last,
            lists,
            Mode::Module,
        );
        wmod.funcs[func] = FuncDecl::Body(sig, "heap_malloc".to_string(), body);
        if let Some((free, free_sig)) = free_func {
            let body = heap::build_free(
                &wmod,
                free_sig,
                memory,
                arena_top,
                lists,
                plan.stack_limit,
                heap_poison,
            );
            wmod.funcs[free] = FuncDecl::Body(free_sig, "heap_free".to_string(), body);
        }
        if host_allocator {
            let [alloc, mark, release] = HOST_ALLOCATOR_EXPORTS;
            // The host allocator cuts zeroed blocks from the top and traps on
            // failure; the allocator of the module reuses freed blocks.
            let host_sig = heap::alloc_signature(&mut wmod);
            let host_body = heap::build_malloc(
                &wmod,
                host_sig,
                memory,
                arena_top,
                arena_last,
                lists,
                Mode::Host,
            );
            let host_func = wmod
                .funcs
                .push(FuncDecl::Body(host_sig, alloc.to_string(), host_body));
            let mark_sig = memory::signature(
                &mut wmod,
                SignatureData {
                    params: vec![],
                    returns: vec![WType::I32],
                },
            );
            let mark_func = wmod.funcs.push(FuncDecl::Body(
                mark_sig,
                mark.to_string(),
                build_arena_mark(&wmod, mark_sig, arena_top),
            ));
            let release_sig = memory::signature(
                &mut wmod,
                SignatureData {
                    params: vec![WType::I32],
                    returns: vec![],
                },
            );
            let release_func = wmod.funcs.push(FuncDecl::Body(
                release_sig,
                release.to_string(),
                heap::build_release(
                    &wmod,
                    release_sig,
                    memory,
                    arena_top,
                    arena_last,
                    lists,
                    plan.stack_limit,
                ),
            ));
            for (name, func) in [
                (alloc, host_func),
                (mark, mark_func),
                (release, release_func),
            ] {
                wmod.exports.push(waffle::Export {
                    name: name.to_string(),
                    kind: ExportKind::Func(func),
                });
                exports.push(name.to_string());
            }
        }
    }

    Ok(Translated {
        module: wmod,
        exports,
        tail_calls,
    })
}

/// The tail calls of `function`, one of the functions in a recursive cycle,
/// with the WebAssembly index of each callee. The callee takes the caller's
/// stack top, so its frame replaces the caller's: an aggregate argument must
/// be one the caller received, whose storage is below both frames, and the
/// result must not come back through a buffer in the caller's frame.
fn tail_call_sites(
    module: &Module,
    func_ref: FuncRef,
    function: &Function,
    callees: &FxHashMap<FuncRef, Callee>,
) -> FxHashMap<InstId, u32> {
    tail_position_calls(func_ref, function)
        .into_iter()
        .filter_map(|(inst, callee)| {
            let callee = callees.get(&callee)?;
            let CallTarget::Func(func) = callee.target else {
                return None;
            };
            let call = function.dfg.downcast::<&Call>(inst)?;
            let passes = |&arg: &ValueId| {
                repr(&module.ctx, function.dfg.value_ty(arg)) != Some(Repr::Aggregate)
                    || function.arg_values.contains(&arg)
            };
            (callee.sret.is_none() && call.args().iter().all(passes))
                .then_some((inst, func.index() as u32))
        })
        .collect()
}

/// Which 256-bit helper function a declaration is for.
#[derive(Clone, Copy)]
enum HelperKind {
    Mulo,
    DivRem,
    Shift { left: bool },
    Modular { product: bool },
}

/// Whether an external function is the C routine that copies memory:
/// `memmove` or `memcpy` taking two pointers and a length of 32 or 64 bits, and
/// returning a pointer.
fn is_memory_copy_declaration(module: &Module, func_ref: FuncRef, name: &str) -> bool {
    if !matches!(name, "memmove" | "memcpy") {
        return false;
    }
    let ctx = &module.ctx;
    let is_pointer = |ty: Type| ty.is_pointer(ctx);
    module.ctx.func_sig(func_ref, |sig| {
        matches!(sig.args(), [dst, src, len]
            if is_pointer(*dst) && is_pointer(*src) && matches!(len, Type::I32 | Type::I64))
            && matches!(sig.ret_tys(), [ret] if is_pointer(*ret))
    })
}

/// The call target of an external `malloc` or `free`: the allocator of the module.
///
/// `malloc` must take a 32-bit size and return a pointer, and `free` must take a
/// pointer and return nothing. Any other signature is an error that names the
/// signature expected, because importing it from the host would give the module
/// two allocators.
fn heap_call_target(
    module: &Module,
    func_ref: FuncRef,
    name: &str,
) -> Result<CallTarget, WasmError> {
    let ctx = &module.ctx;
    let is_pointer = |ty: Type| ty.is_pointer(ctx);
    let matches = module.ctx.func_sig(func_ref, |sig| match name {
        "malloc" => {
            matches!(sig.args(), [size] if *size == Type::I32)
                && matches!(sig.ret_tys(), [ret] if is_pointer(*ret))
        }
        _ => {
            matches!(sig.args(), [address] if is_pointer(*address))
                && matches!(sig.ret_tys(), [] | [Type::Unit])
        }
    });
    if !matches {
        let expected = if name == "malloc" {
            "one `i32` size parameter and a pointer result"
        } else {
            "one pointer parameter and no result"
        };
        return Err(WasmError::Unsupported(format!(
            "`{name}` is the allocator of the WebAssembly module and must have {expected}; \
             this declaration has another signature"
        )));
    }
    Ok(if name == "malloc" {
        CallTarget::HeapMalloc
    } else {
        CallTarget::HeapFree
    })
}

struct DeclaredSignature {
    wasm: SignatureData,
    params: Vec<Type>,
    rets: Vec<Type>,
    sret: Option<Type>,
}

/// The WebAssembly signature of a function. With `external` the signature is
/// the one the host sees: no hidden parameters, and scalars only. Otherwise it
/// is the signature that the module's own calls use.
fn declared_signature(
    module: &Module,
    func_ref: FuncRef,
    name: &str,
    plan: &MemoryPlan,
    external: bool,
) -> Result<DeclaredSignature, WasmError> {
    module.ctx.func_sig(func_ref, |sig| {
        let sret = indirect_return_storage(&module.ctx, sig.ret_tys());
        if sig.ret_tys().len() > 1
            && sig
                .ret_tys()
                .iter()
                .any(|ty| matches!(repr(&module.ctx, *ty), Some(Repr::Aggregate) | None))
        {
            return Err(unsupported(format!(
                "function `{name}`: results that mix several values with a struct or an array \
                 are not supported"
            )));
        }
        let carrier = |ty: Type, role: String| {
            let Some(representation) = repr(&module.ctx, ty) else {
                return Err(unsupported(format!(
                    "function `{name}`: {role} has type {}, which the wasm32 backend does not support",
                    type_name(&module.ctx, ty)
                )));
            };
            if external && matches!(representation, Repr::Wide(_) | Repr::Aggregate)
                || external && is_reference(&module.ctx, ty)
            {
                return Err(unsupported(format!(
                    "function `{name}`: {role} has type {}, which cannot cross the module \
                     boundary; only integers of at most 64 bits and pointers can",
                    type_name(&module.ctx, ty)
                )));
            }
            Ok(representation)
        };
        let mut params = Vec::new();
        let mut returns = Vec::new();
        let hidden_stack = plan.runtime && !external;
        if hidden_stack {
            params.push(WType::I32);
        }
        if sret.is_some() && !external {
            params.push(WType::I32);
        }
        for (index, ty) in sig.args().iter().enumerate() {
            carrier(*ty, format!("parameter {index}"))?.push_carriers(&mut params);
        }
        for (index, ty) in sig.ret_tys().iter().enumerate() {
            let representation = carrier(*ty, format!("result {index}"))?;
            if sret.is_none() || external {
                representation.push_carriers(&mut returns);
            }
        }
        Ok(DeclaredSignature {
            wasm: SignatureData { params, returns },
            params: sig.args().to_vec(),
            rets: sig.ret_tys().to_vec(),
            sret,
        })
    })
}

fn is_reference(ctx: &ModuleCtx, ty: Type) -> bool {
    matches!(
        ty.resolve_compound(ctx),
        Some(CompoundType::ObjRef(_) | CompoundType::ConstRef(_))
    )
}

/// An export crosses the module boundary, so its signature must too.
fn check_exportable(module: &Module, func_ref: FuncRef, name: &str) -> Result<(), WasmError> {
    // Building the host-facing signature reports the offending type by name.
    let plan = MemoryPlan::bare();
    declared_signature(module, func_ref, name, &plan, true).map(|_| ())
}

/// The calling function of an export: it starts the stack at the `stack_top`
/// global, calls the function, and puts the global back as it found it.
fn build_wrapper(
    wmod: &WaffleModule<'static>,
    wsig: Signature,
    inner: Func,
    params: &[Type],
    rets: &[Type],
    globals: RuntimeGlobals,
) -> Result<FunctionBody, WasmError> {
    let mut body = FunctionBody::new(wmod, wsig);
    let entry = body.entry;
    let incoming: Vec<V> = body.blocks[entry]
        .params
        .iter()
        .map(|param| param.1)
        .collect();
    let mut args = Vec::with_capacity(incoming.len() + 1);
    let top = body.add_op(
        entry,
        Operator::GlobalGet {
            global_index: globals.stack_top,
        },
        &[],
        &[WType::I32],
    );
    args.push(top);
    for (ty, value) in params.iter().zip(incoming) {
        let value = match Int::from_type(*ty) {
            // The host may pass any bits above the width of a narrow parameter.
            Some(int) => Emit {
                body: &mut body,
                block: entry,
            }
            .canonicalize(int, value),
            None => value,
        };
        args.push(value);
    }
    let carriers: Vec<WType> = rets
        .iter()
        .map(|ty| match Int::from_type(*ty) {
            Some(int) => Ok(int.carrier()),
            None => Ok(WType::I32),
        })
        .collect::<Result<_, WasmError>>()?;
    let results = emit_call(&mut body, entry, inner, &args, &carriers);
    body.add_op(
        entry,
        Operator::GlobalSet {
            global_index: globals.stack_top,
        },
        &[top],
        &[],
    );
    body.set_terminator(entry, Terminator::Return { values: results });
    Ok(body)
}

/// Emit a call and return its results in order.
pub(super) fn emit_call(
    body: &mut FunctionBody,
    block: waffle::Block,
    func: Func,
    args: &[V],
    carriers: &[WType],
) -> Vec<V> {
    let call = Operator::Call {
        function_index: func,
    };
    if carriers.is_empty() {
        body.add_op(block, call, args, &[]);
        return Vec::new();
    }
    let call_value = body.add_op(block, call, args, carriers);
    let count = carriers.len();
    carriers
        .iter()
        .enumerate()
        .map(|(index, carrier)| {
            if count == 1 {
                call_value
            } else {
                let picked =
                    body.add_value(ValueDef::PickOutput(call_value, index as u32, *carrier));
                body.append_to_block(block, picked);
                picked
            }
        })
        .collect()
}

/// How a scalar moves between linear memory and a value.
#[derive(Clone, Copy)]
enum Access {
    Byte,
    Half,
    Word,
    Double,
}

impl Access {
    fn align(self) -> u32 {
        match self {
            Self::Byte => 0,
            Self::Half => 1,
            Self::Word => 2,
            Self::Double => 3,
        }
    }
}

struct FunctionTranslator<'a> {
    module: &'a Module,
    function: &'a Function,
    name: &'a str,
    body: FunctionBody,
    memory: waffle::Memory,
    callees: &'a FxHashMap<FuncRef, Callee>,
    plan: &'a MemoryPlan,
    globals: Option<RuntimeGlobals>,
    arena: Option<Func>,
    free: Option<Func>,
    sha256: Option<Func>,
    wide_helpers: WideHelpers,
    return_tys: Vec<Type>,
    /// Sonatina values defined so far, in canonical WAFFLE form. Not 128- or
    /// 256-bit values, which are in `wide`, zero-extended to four limbs.
    values: FxHashMap<ValueId, V>,
    wide: FxHashMap<ValueId, Limbs>,
    blocks: FxHashMap<BlockId, waffle::Block>,
    /// The stack top received from the caller, which is the base of the frame.
    sp: Option<V>,
    /// The end of the frame, which callees receive as their stack top.
    top: Option<V>,
    /// The placeholder constant that holds the frame size once it is known.
    frame_size: Option<V>,
    /// The bytes of the frame handed out so far.
    frame: u32,
    /// The hidden buffer for an aggregate result.
    sret: Option<(V, Type)>,
    trap: Option<waffle::Block>,
    /// Block parameters that carry the contents of aggregate phis, by result.
    phi_params: FxHashMap<ValueId, V>,
    /// Frame offsets of the storage of aggregate phis, by result.
    phi_slots: FxHashMap<ValueId, u32>,
    /// Frame offsets of snapshots of the inputs of aggregate phis, by edge.
    edge_slots: FxHashMap<(BlockId, BlockId, InstId), u32>,
    /// Frame offsets of the zero-filled storage of aggregate `undef` operands.
    undef_slots: FxHashMap<ValueId, u32>,
    /// The calls that end their block as tail calls.
    tail_calls: FxHashSet<InstId>,
    /// The size of the largest copy made with loads and stores.
    inline_copy_bytes: u32,
}

impl<'a> FunctionTranslator<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        module: &'a Module,
        function: &'a Function,
        func_ref: FuncRef,
        name: &'a str,
        wmod: &WaffleModule,
        wsig: Signature,
        memory: waffle::Memory,
        callees: &'a FxHashMap<FuncRef, Callee>,
        plan: &'a MemoryPlan,
        globals: Option<RuntimeGlobals>,
        arena: Option<Func>,
        free: Option<Func>,
        sha256: Option<Func>,
        wide_helpers: WideHelpers,
        tail_calls: FxHashSet<InstId>,
        opt_level: OptLevel,
    ) -> Self {
        Self {
            module,
            function,
            name,
            body: FunctionBody::new(wmod, wsig),
            memory,
            callees,
            plan,
            globals,
            arena,
            free,
            sha256,
            wide_helpers,
            return_tys: callees[&func_ref].rets.clone(),
            values: FxHashMap::default(),
            wide: FxHashMap::default(),
            blocks: FxHashMap::default(),
            sp: None,
            top: None,
            frame_size: None,
            frame: 0,
            sret: None,
            trap: None,
            phi_params: FxHashMap::default(),
            phi_slots: FxHashMap::default(),
            edge_slots: FxHashMap::default(),
            undef_slots: FxHashMap::default(),
            tail_calls,
            inline_copy_bytes: aggregate::inline_copy_bytes(opt_level),
        }
    }

    fn translate(mut self, canonicalize_params: bool) -> Result<FunctionBody, WasmError> {
        let function = self.function;
        let entry = function
            .layout
            .entry_block()
            .ok_or_else(|| invalid(format!("function `{}` has no entry block", self.name)))?;

        // Blocks unreachable from the entry never run and are not translated.
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(function);
        let mut order: Vec<BlockId> = cfg.post_order().collect();
        order.reverse();

        // A Sonatina entry block may be a loop header, but WebAssembly cannot
        // branch to the start of a function body. Enter such a block through
        // a separate prologue. The frame check also lives there.
        let runtime = self.plan.runtime;
        let needs_prologue = runtime || cfg.preds_of(entry).next().is_some();
        for &block in &order {
            let wb = if block == entry && !needs_prologue {
                self.body.entry
            } else {
                self.body.add_block()
            };
            self.blocks.insert(block, wb);
        }

        let params: Vec<V> = self.body.blocks[self.body.entry]
            .params
            .iter()
            .map(|param| param.1)
            .collect();
        let mut next = 0;
        let prologue = self.body.entry;
        if runtime {
            let sp = params[next];
            next += 1;
            self.sp = Some(sp);
            let size = self.emit(prologue).c32(0);
            self.frame_size = Some(size);
            let top = self
                .emit(prologue)
                .op(Operator::I32Add, &[sp, size], WType::I32);
            self.top = Some(top);
        }
        let callee_sret = self
            .callees
            .values()
            .next()
            .map(|_| ())
            .and(indirect_return_storage(&self.module.ctx, &self.return_tys));
        if let Some(storage) = callee_sret {
            self.sret = Some((params[next], storage));
            next += 1;
        }
        for &arg in &function.arg_values {
            let ty = function.dfg.value_ty(arg);
            let representation = repr(&self.module.ctx, ty).ok_or_else(|| {
                unsupported(format!(
                    "function `{}`: parameter of type {}, which the wasm32 backend does not support",
                    self.name,
                    type_name(&self.module.ctx, ty)
                ))
            })?;
            match representation {
                Repr::Wide(wide) => {
                    let carried = &params[next..next + wide.limbs()];
                    next += wide.limbs();
                    let limbs = self.emit(prologue).wide_from_carried(wide, carried);
                    self.wide.insert(arg, limbs);
                }
                Repr::Int(int) => {
                    let mut value = params[next];
                    next += 1;
                    if canonicalize_params {
                        // The host may pass any bits above the width of a narrow
                        // parameter.
                        value = self.emit(prologue).canonicalize(int, value);
                    }
                    self.values.insert(arg, value);
                }
                Repr::Pointer | Repr::Aggregate => {
                    self.values.insert(arg, params[next]);
                    next += 1;
                }
            }
        }
        if needs_prologue {
            // The terminator of the prologue is set once the frame is known.
        }

        for &block in &order {
            for inst_id in function.layout.iter_inst(block) {
                let inst = function.dfg.inst(inst_id);
                let NativeInstKind::Phi(_) = self.resolve(inst)? else {
                    break;
                };
                if block == entry {
                    return Err(invalid(format!(
                        "function `{}`: the entry block contains a phi",
                        self.name
                    )));
                }
                let result = function.dfg.inst_result(inst_id).ok_or_else(|| {
                    invalid(format!("function `{}`: a phi has no result", self.name))
                })?;
                let ty = function.dfg.value_ty(result);
                let representation = repr(&self.module.ctx, ty).ok_or_else(|| {
                    unsupported(format!(
                        "function `{}`: `phi` of type {}, which the wasm32 backend does not support",
                        self.name,
                        type_name(&self.module.ctx, ty)
                    ))
                })?;
                let wb = self.blocks[&block];
                match representation {
                    Repr::Wide(wide) => {
                        let carried: Vec<V> = (0..wide.limbs())
                            .map(|_| self.body.add_blockparam(wb, WType::I64))
                            .collect();
                        let limbs = self.emit(wb).wide_from_carried(wide, &carried);
                        self.wide.insert(result, limbs);
                    }
                    Repr::Int(int) => {
                        let param = self.body.add_blockparam(wb, int.carrier());
                        self.values.insert(result, param);
                    }
                    Repr::Pointer => {
                        let param = self.body.add_blockparam(wb, WType::I32);
                        self.values.insert(result, param);
                    }
                    Repr::Aggregate => {
                        // The block parameter is the address of the incoming
                        // contents. The block copies them into storage of its own
                        // before anything else runs.
                        let param = self.body.add_blockparam(wb, WType::I32);
                        self.phi_params.insert(result, param);
                        let (size, align) = self.layout_of(ty)?;
                        let slot = self.slot(size, align)?;
                        self.phi_slots.insert(result, slot);
                    }
                }
            }
        }

        let first = self.blocks[&entry];
        for &block in &order {
            self.translate_block(block)?;
        }

        if needs_prologue {
            let target = BlockTarget {
                block: first,
                args: vec![],
            };
            let terminator = self.finish_frame(target)?;
            self.body.set_terminator(prologue, terminator);
        }

        Ok(self.body)
    }

    /// Fix the frame size in the prologue and return its terminator: a branch to
    /// `target`, preceded by a check that the stack has room for the frame.
    fn finish_frame(&mut self, target: BlockTarget) -> Result<Terminator, WasmError> {
        let (Some(size_value), Some(sp)) = (self.frame_size, self.sp) else {
            return Ok(Terminator::Br { target });
        };
        let size = align_up(self.frame, ALIGN).ok_or_else(|| {
            unsupported(format!("function `{}`: the frame is too large", self.name))
        })?;
        let ValueDef::Operator(_, args, tys) = self.body.values[size_value].clone() else {
            return Err(invalid("the frame size is not a constant".to_string()));
        };
        self.body.values[size_value] =
            ValueDef::Operator(Operator::I32Const { value: size }, args, tys);
        if size == 0 {
            return Ok(Terminator::Br { target });
        }
        let prologue = self.body.entry;
        let stack_limit = self.plan.stack_limit;
        let limit = self.emit(prologue).c32(stack_limit);
        let room = self
            .emit(prologue)
            .op(Operator::I32Sub, &[limit, sp], WType::I32);
        let need = self.emit(prologue).c32(size);
        let short = self
            .emit(prologue)
            .op(Operator::I32LtU, &[room, need], WType::I32);
        let trap = self.trap_block();
        Ok(Terminator::CondBr {
            cond: short,
            if_true: BlockTarget {
                block: trap,
                args: vec![],
            },
            if_false: target,
        })
    }

    fn emit(&mut self, block: waffle::Block) -> Emit<'_> {
        Emit {
            body: &mut self.body,
            block,
        }
    }

    fn resolve(&self, inst: &'a dyn Inst) -> Result<NativeInstKind<'a>, WasmError> {
        let inst_set = native_inst_set();
        if !inst_set.contains_inst(inst) {
            return Err(unsupported(format!(
                "function `{}`: instruction `{}` is not in the wasm32 instruction set",
                self.name,
                inst.as_text()
            )));
        }
        Ok(inst_set.resolve_inst(inst))
    }

    fn unsupported_inst(&self, op: &str) -> WasmError {
        unsupported(format!(
            "function `{}`: instruction `{op}` is not supported by the wasm32 backend",
            self.name
        ))
    }

    /// The integer type of an operand, or an error naming the type and the
    /// instruction that needs it.
    fn int_ty(&self, op: &str, ty: Type) -> Result<Int, WasmError> {
        Int::from_type(ty).ok_or_else(|| {
            if Wide::from_type(ty).is_some() {
                return unsupported(format!(
                    "function `{}`: `{op}` on {} is not supported by the wasm32 backend",
                    self.name,
                    type_name(&self.module.ctx, ty)
                ));
            }
            unsupported(format!(
                "function `{}`: `{op}` on {}, which the wasm32 backend does not support \
                 (integers of 1, 8, 16, 32 and 64 bits are supported)",
                self.name,
                type_name(&self.module.ctx, ty)
            ))
        })
    }

    fn is_pointer(&self, ty: Type) -> bool {
        matches!(
            ty.resolve_compound(&self.module.ctx),
            Some(CompoundType::Ptr(_))
        )
    }

    /// The width of a 128- or 256-bit operand.
    fn wide_ty(&self, id: ValueId) -> Option<Wide> {
        Wide::from_type(self.function.dfg.value_ty(id))
    }

    fn operand(&mut self, wb: waffle::Block, id: ValueId) -> Result<V, WasmError> {
        if let Some(&value) = self.values.get(&id) {
            return Ok(value);
        }
        let function = self.function;
        match function.dfg.value(id) {
            Value::Immediate { imm, .. } => {
                let mut emit = self.emit(wb);
                match *imm {
                    Immediate::I1(value) => Ok(emit.c32(u32::from(value))),
                    Immediate::I8(value) => Ok(emit.c32(u32::from(value as u8))),
                    Immediate::I16(value) => Ok(emit.c32(u32::from(value as u16))),
                    Immediate::I32(value) => Ok(emit.c32(value as u32)),
                    Immediate::I64(value) => Ok(emit.c64(value as u64)),
                    other => Err(self.unsupported_type("an immediate", other.ty())),
                }
            }
            Value::Undef { ty } => {
                // An undefined value is materialized as zero, as the native
                // backend does.
                match repr(&self.module.ctx, *ty) {
                    Some(Repr::Int(int)) => Ok(self.emit(wb).zero(int)),
                    Some(Repr::Pointer) => Ok(self.emit(wb).c32(0)),
                    Some(Repr::Aggregate) => self.undef_aggregate(wb, id, *ty),
                    _ => Err(self.unsupported_type("an undefined value", *ty)),
                }
            }
            Value::Global { gv, .. } => {
                let address = self.plan.globals.get(gv).ok_or_else(|| {
                    invalid(format!(
                        "function `{}`: global variable operand has no storage",
                        self.name
                    ))
                })?;
                Ok(self.emit(wb).c32(*address))
            }
            Value::Arg { .. } | Value::Inst { .. } => Err(invalid(format!(
                "function `{}`: value v{} is used before it is defined",
                self.name, id.0
            ))),
        }
    }

    /// The limbs of a 128- or 256-bit operand, zero-extended to 256 bits.
    fn wide_operand(&mut self, wb: waffle::Block, id: ValueId) -> Result<Limbs, WasmError> {
        if let Some(&limbs) = self.wide.get(&id) {
            return Ok(limbs);
        }
        let function = self.function;
        match function.dfg.value(id) {
            // An `i128` is zero-extended.
            Value::Immediate { imm, .. } if Wide::from_type(imm.ty()).is_some() => {
                Ok(self.emit(wb).wide_const(imm.zext(Type::I256).as_i256()))
            }
            Value::Undef { ty } if Wide::from_type(*ty).is_some() => Ok(self.emit(wb).wide_zero()),
            Value::Immediate { imm, .. } => Err(self.unsupported_type("an immediate", imm.ty())),
            _ => Err(invalid(format!(
                "function `{}`: value v{} is used before it is defined",
                self.name, id.0
            ))),
        }
    }

    fn unsupported_type(&self, what: &str, ty: Type) -> WasmError {
        unsupported(format!(
            "function `{}`: {what} of type {}, which the wasm32 backend does not support",
            self.name,
            type_name(&self.module.ctx, ty)
        ))
    }

    /// Record result `index` of an instruction. `expected` is the type the
    /// lowering produced, which must be the declared type of the result.
    fn define(
        &mut self,
        inst_id: InstId,
        index: usize,
        value: V,
        expected: Type,
    ) -> Result<(), WasmError> {
        let result = self.result_of(inst_id, index, expected)?;
        self.values.insert(result, value);
        Ok(())
    }

    /// Record the result of an instruction as a copy of `arg`.
    fn copy_value(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        arg: ValueId,
    ) -> Result<(), WasmError> {
        if let Some(wide) = self.wide_ty(arg) {
            let limbs = self.wide_operand(wb, arg)?;
            self.define_wide(wb, inst_id, 0, wide, limbs)
        } else {
            let ty = self.function.dfg.value_ty(arg);
            let value = self.operand(wb, arg)?;
            self.define(inst_id, 0, value, ty)
        }
    }

    /// Record result `index` of an instruction of type `wide`. A 128-bit
    /// result is the low 128 bits of `limbs`.
    fn define_wide(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        index: usize,
        wide: Wide,
        limbs: Limbs,
    ) -> Result<(), WasmError> {
        let result = self.result_of(inst_id, index, wide.ty())?;
        let limbs = self.emit(wb).wide_wrap(wide, limbs);
        self.wide.insert(result, limbs);
        Ok(())
    }

    fn result_of(
        &self,
        inst_id: InstId,
        index: usize,
        expected: Type,
    ) -> Result<ValueId, WasmError> {
        let function = self.function;
        let result = function
            .dfg
            .inst_results(inst_id)
            .get(index)
            .copied()
            .ok_or_else(|| {
                invalid(format!(
                    "function `{}`: `{}` has no result {index}",
                    self.name,
                    function.dfg.inst(inst_id).as_text()
                ))
            })?;
        let actual = function.dfg.value_ty(result);
        if actual != expected {
            return Err(invalid(format!(
                "function `{}`: `{}` produces {} but its result is declared as {}",
                self.name,
                function.dfg.inst(inst_id).as_text(),
                type_name(&self.module.ctx, expected),
                type_name(&self.module.ctx, actual)
            )));
        }
        Ok(result)
    }

    /// The type of the result of an instruction, as declared.
    fn result_ty(&self, inst_id: InstId) -> Result<Type, WasmError> {
        let function = self.function;
        function
            .dfg
            .inst_result(inst_id)
            .map(|result| function.dfg.value_ty(result))
            .ok_or_else(|| {
                invalid(format!(
                    "function `{}`: `{}` has no result",
                    self.name,
                    function.dfg.inst(inst_id).as_text()
                ))
            })
    }

    /// Operands of a two-operand integer instruction, which must share a type.
    fn binary_operands(
        &mut self,
        wb: waffle::Block,
        op: &str,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(Int, Type, V, V), WasmError> {
        let ty = self.function.dfg.value_ty(lhs);
        let int = self.int_ty(op, ty)?;
        if self.function.dfg.value_ty(rhs) != ty {
            return Err(invalid(format!(
                "function `{}`: `{op}` operands have different types",
                self.name
            )));
        }
        let lhs = self.operand(wb, lhs)?;
        let rhs = self.operand(wb, rhs)?;
        Ok((int, ty, lhs, rhs))
    }

    fn unary_operand(
        &mut self,
        wb: waffle::Block,
        op: &str,
        arg: ValueId,
    ) -> Result<(Int, Type, V), WasmError> {
        let ty = self.function.dfg.value_ty(arg);
        let int = self.int_ty(op, ty)?;
        let arg = self.operand(wb, arg)?;
        Ok((int, ty, arg))
    }

    /// Operands of a two-operand instruction of `wide`, extended to 256 bits,
    /// with the sign when `signed`.
    fn wide_operands(
        &mut self,
        wb: waffle::Block,
        op: &str,
        wide: Wide,
        signed: bool,
        (lhs, rhs): (ValueId, ValueId),
    ) -> Result<(Limbs, Limbs), WasmError> {
        if self.function.dfg.value_ty(rhs) != wide.ty() {
            return Err(invalid(format!(
                "function `{}`: `{op}` operands have different types",
                self.name
            )));
        }
        let mut operands = [self.wide_operand(wb, lhs)?, self.wide_operand(wb, rhs)?];
        if signed {
            operands = operands.map(|limbs| self.emit(wb).wide_sign_extend(wide, limbs));
        }
        Ok((operands[0], operands[1]))
    }

    /// An integer instruction with one result of the operand type.
    fn binary(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (lhs, rhs): (ValueId, ValueId),
        lower: impl FnOnce(&mut Emit<'_>, Int, V, V) -> V,
    ) -> Result<(), WasmError> {
        let op = self.function.dfg.inst(inst_id).as_text();
        let (int, ty, lhs, rhs) = self.binary_operands(wb, op, lhs, rhs)?;
        let value = lower(&mut self.emit(wb), int, lhs, rhs);
        self.define(inst_id, 0, value, ty)
    }

    /// An instruction of 128 or 256 bits with one result of the operand type,
    /// computed from the zero-extended operands, when the operands are held as
    /// limbs; otherwise the integer lowering.
    fn binary_any(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (lhs, rhs): (ValueId, ValueId),
        wide_lower: impl FnOnce(&mut Emit<'_>, Limbs, Limbs) -> Limbs,
        lower: impl FnOnce(&mut Emit<'_>, Int, V, V) -> V,
    ) -> Result<(), WasmError> {
        if let Some(wide) = self.wide_ty(lhs) {
            let op = self.function.dfg.inst(inst_id).as_text();
            let (lhs, rhs) = self.wide_operands(wb, op, wide, false, (lhs, rhs))?;
            let limbs = wide_lower(&mut self.emit(wb), lhs, rhs);
            self.define_wide(wb, inst_id, 0, wide, limbs)
        } else {
            self.binary(wb, inst_id, (lhs, rhs), lower)
        }
    }

    fn unary(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        arg: ValueId,
        lower: impl FnOnce(&mut Emit<'_>, Int, V) -> V,
    ) -> Result<(), WasmError> {
        let op = self.function.dfg.inst(inst_id).as_text();
        let (int, ty, arg) = self.unary_operand(wb, op, arg)?;
        let value = lower(&mut self.emit(wb), int, arg);
        self.define(inst_id, 0, value, ty)
    }

    /// The one-operand form of [`Self::binary_any`].
    fn unary_any(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        arg: ValueId,
        wide_lower: impl FnOnce(&mut Emit<'_>, Wide, Limbs) -> Limbs,
        lower: impl FnOnce(&mut Emit<'_>, Int, V) -> V,
    ) -> Result<(), WasmError> {
        if let Some(wide) = self.wide_ty(arg) {
            let limbs = self.wide_operand(wb, arg)?;
            let limbs = wide_lower(&mut self.emit(wb), wide, limbs);
            self.define_wide(wb, inst_id, 0, wide, limbs)
        } else {
            self.unary(wb, inst_id, arg, lower)
        }
    }

    fn compare(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (lhs, rhs): (ValueId, ValueId),
        cmp: Cmp,
        signed: bool,
    ) -> Result<(), WasmError> {
        let op = self.function.dfg.inst(inst_id).as_text();
        if let Some(wide) = self.wide_ty(lhs) {
            let (lhs, rhs) = self.wide_operands(wb, op, wide, signed, (lhs, rhs))?;
            let value = self.emit(wb).wide_compare(cmp, signed, lhs, rhs);
            return self.define(inst_id, 0, value, Type::I1);
        }
        let (int, _, lhs, rhs) = self.binary_operands(wb, op, lhs, rhs)?;
        let value = self.emit(wb).compare(int, cmp, signed, lhs, rhs);
        self.define(inst_id, 0, value, Type::I1)
    }

    /// An integer instruction with a result and an overflow flag.
    fn overflow(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (lhs, rhs): (ValueId, ValueId),
        arith: Arith,
        signed: bool,
    ) -> Result<(), WasmError> {
        let op = self.function.dfg.inst(inst_id).as_text();
        if let Some(wide) = self.wide_ty(lhs) {
            let (lhs, rhs) = self.wide_operands(wb, op, wide, signed, (lhs, rhs))?;
            let (result, flag) = self.wide_overflowing(wb, wide, arith, signed, lhs, rhs)?;
            self.define_wide(wb, inst_id, 0, wide, result)?;
            return self.define(inst_id, 1, flag, Type::I1);
        }
        let (int, ty, lhs, rhs) = self.binary_operands(wb, op, lhs, rhs)?;
        let (value, overflow) = self.emit(wb).overflow(int, arith, signed, lhs, rhs);
        self.define(inst_id, 0, value, ty)?;
        self.define(inst_id, 1, overflow, Type::I1)
    }

    /// A saturating instruction: the result, or the bound in the direction of
    /// the overflow.
    fn saturating(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (lhs, rhs): (ValueId, ValueId),
        arith: Arith,
        signed: bool,
    ) -> Result<(), WasmError> {
        if let Some(wide) = self.wide_ty(lhs) {
            let op = self.function.dfg.inst(inst_id).as_text();
            let (lhs, rhs) = self.wide_operands(wb, op, wide, signed, (lhs, rhs))?;
            let limbs = self.wide_saturating(wb, wide, arith, signed, lhs, rhs)?;
            return self.define_wide(wb, inst_id, 0, wide, limbs);
        }
        self.binary(wb, inst_id, (lhs, rhs), |e, int, l, r| {
            e.saturating(int, arith, signed, l, r)
        })
    }

    fn shift(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (value, bits): (ValueId, ValueId),
        kind: Shift,
    ) -> Result<(), WasmError> {
        // The count has the type of the value.
        let known = self.function.dfg.value_imm(bits);
        let known = known.and_then(Immediate::to_nonnegative_usize);
        self.binary(wb, inst_id, (value, bits), |emit, int, value, bits| {
            emit.shift(int, kind, value, bits, known.map(|count| count as u64))
        })
    }

    fn trap_block(&mut self) -> waffle::Block {
        if let Some(block) = self.trap {
            return block;
        }
        let block = self.body.add_block();
        self.body.set_terminator(block, Terminator::Unreachable);
        self.trap = Some(block);
        block
    }

    /// The lowest case of a `br_table` and each case's distance above it, if
    /// a table over that range is no larger than the chain of comparisons: a
    /// comparison takes about eight bytes and an entry one. Distances are
    /// modulo the width, from the lowest signed or unsigned case, whichever
    /// range is shorter, so cases on both sides of zero are close.
    fn dense_cases(
        &self,
        int: Int,
        scrutinee_ty: Type,
        table: &[(ValueId, BlockId)],
    ) -> Option<(u64, Vec<(u64, BlockId)>)> {
        let mask = u64::MAX >> (64 - int.bits());
        let keys: Vec<u64> = table
            .iter()
            .map(|&(case, _)| {
                let imm = self.function.dfg.value_imm(case)?;
                (imm.ty() == scrutinee_ty).then(|| imm.as_i256().to_u256().low_u64() & mask)
            })
            .collect::<Option<_>>()?;
        let sign = 1 << (int.bits() - 1);
        let span = |base: u64| keys.iter().map(|key| key.wrapping_sub(base) & mask).max();
        let unsigned = *keys.iter().min()?;
        let signed = *keys.iter().min_by_key(|&&key| key ^ sign)?;
        let base = if span(signed) < span(unsigned) {
            signed
        } else {
            unsigned
        };
        (keys.len() >= 3 && span(base)? < 8 * keys.len() as u64).then(|| {
            let distances = keys.iter().map(|key| key.wrapping_sub(base) & mask);
            (
                base,
                distances.zip(table.iter().map(|&(_, dest)| dest)).collect(),
            )
        })
    }

    /// End `wb` with a WebAssembly `br_table` over `cases`, which are
    /// distances above `base`, indexed by the scrutinee's distance. One past
    /// the table takes the default, as does a gap between cases.
    fn jump_table(
        &mut self,
        block: BlockId,
        wb: waffle::Block,
        (int, scrutinee): (Int, V),
        (base, cases): (u64, &[(u64, BlockId)]),
        default: Option<BlockId>,
    ) -> Result<(), WasmError> {
        let entries = cases
            .iter()
            .map(|&(distance, _)| distance)
            .max()
            .unwrap_or_default()
            + 1;
        let mut emit = self.emit(wb);
        let index = if int.carrier() == WType::I64 {
            let base = emit.c64(base);
            let distance = emit.op(Operator::I64Sub, &[scrutinee, base], WType::I64);
            let limit = emit.c64(entries);
            let inside = emit.op(Operator::I64LtU, &[distance, limit], WType::I32);
            let narrow = emit.op(Operator::I32WrapI64, &[distance], WType::I32);
            let past = emit.c32(entries as u32);
            emit.op(Operator::Select, &[narrow, past, inside], WType::I32)
        } else if base == 0 {
            scrutinee
        } else {
            let base = emit.c32(base as u32);
            let distance = emit.op(Operator::I32Sub, &[scrutinee, base], WType::I32);
            emit.canonicalize(int, distance)
        };
        let default = match default {
            Some(default) => self.edge(block, default, wb)?,
            None => BlockTarget {
                block: self.trap_block(),
                args: vec![],
            },
        };
        // The first case with a constant is the one a chain would take.
        let mut edges: FxHashMap<BlockId, BlockTarget> = FxHashMap::default();
        let mut targets = vec![None; entries as usize];
        for &(distance, dest) in cases {
            let target = &mut targets[distance as usize];
            if target.is_none() {
                *target = Some(match edges.entry(dest) {
                    Entry::Occupied(edge) => edge.get().clone(),
                    Entry::Vacant(edge) => edge.insert(self.edge(block, dest, wb)?).clone(),
                });
            }
        }
        let targets = targets
            .into_iter()
            .map(|target| target.unwrap_or_else(|| default.clone()))
            .collect();
        self.body.set_terminator(
            wb,
            Terminator::Select {
                value: index,
                targets,
                default,
            },
        );
        Ok(())
    }

    /// Trap if `cond` (an `i32`) is non-zero; the rest of the block continues
    /// in a new WAFFLE block, which becomes `wb`.
    fn trap_if(&mut self, wb: &mut waffle::Block, cond: V) {
        let trap = self.trap_block();
        let next = self.body.add_block();
        self.body.set_terminator(
            *wb,
            Terminator::CondBr {
                cond,
                if_true: BlockTarget {
                    block: trap,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: next,
                    args: vec![],
                },
            },
        );
        *wb = next;
    }

    fn memarg(&self, access: Access, offset: u32) -> MemoryArg {
        MemoryArg {
            align: access.align(),
            offset,
            memory: self.memory,
        }
    }

    /// The branch target of the edge `from` to `to`, with the phi inputs that
    /// `from` supplies. Inputs are materialized in the WAFFLE block `wb`.
    fn edge(
        &mut self,
        from: BlockId,
        to: BlockId,
        wb: waffle::Block,
    ) -> Result<BlockTarget, WasmError> {
        let function = self.function;
        let block = *self.blocks.get(&to).ok_or_else(|| {
            invalid(format!(
                "function `{}`: branch to block{} which is not reachable from the entry",
                self.name,
                to.as_u32()
            ))
        })?;
        // Copying the inputs of several aggregate phis one after another in
        // the target could overwrite an input that another phi still reads, so
        // with more than one they are first copied to storage of their own.
        let aggregate_phis = function
            .layout
            .iter_inst(to)
            .take_while(|&inst_id| function.dfg.is_phi(inst_id))
            .filter(|&inst_id| {
                function.dfg.inst_result(inst_id).is_some_and(|result| {
                    repr(&self.module.ctx, function.dfg.value_ty(result)) == Some(Repr::Aggregate)
                })
            })
            .count();
        let mut args = Vec::new();
        for inst_id in function.layout.iter_inst(to) {
            let NativeInstKind::Phi(phi) = self.resolve(function.dfg.inst(inst_id))? else {
                break;
            };
            let input = phi
                .args()
                .iter()
                .find(|(_, pred)| *pred == from)
                .map(|(value, _)| *value)
                .ok_or_else(|| {
                    invalid(format!(
                        "function `{}`: a phi in block{} has no input for block{}",
                        self.name,
                        to.as_u32(),
                        from.as_u32()
                    ))
                })?;
            let result = function
                .dfg
                .inst_result(inst_id)
                .ok_or_else(|| invalid(format!("function `{}`: a phi has no result", self.name)))?;
            let ty = function.dfg.value_ty(result);
            if function.dfg.value_ty(input) != ty {
                return Err(invalid(format!(
                    "function `{}`: a phi input from block{} has the wrong type",
                    self.name,
                    from.as_u32()
                )));
            }
            match repr(&self.module.ctx, ty) {
                Some(Repr::Wide(wide)) => {
                    args.extend_from_slice(&self.wide_operand(wb, input)?[..wide.limbs()])
                }
                Some(Repr::Aggregate) => {
                    let mut address = self.operand(wb, input)?;
                    if aggregate_phis > 1 {
                        let (size, align) = self.layout_of(ty)?;
                        let slot = match self.edge_slots.get(&(from, to, inst_id)) {
                            Some(&slot) => slot,
                            None => {
                                let slot = self.slot(size, align)?;
                                self.edge_slots.insert((from, to, inst_id), slot);
                                slot
                            }
                        };
                        let copy = self.slot_address(wb, slot)?;
                        self.copy_bytes(wb, copy, address, size);
                        address = copy;
                    }
                    args.push(address);
                }
                _ => args.push(self.operand(wb, input)?),
            }
        }
        Ok(BlockTarget { block, args })
    }

    fn translate_block(&mut self, block: BlockId) -> Result<(), WasmError> {
        let mut wb = self.blocks[&block];
        let function = self.function;
        // Aggregate phis receive the address of their input; keep a copy in
        // the storage of the phi, which no later definition overwrites.
        for inst_id in function.layout.iter_inst(block) {
            if !function.dfg.is_phi(inst_id) {
                break;
            }
            let result = function
                .dfg
                .inst_result(inst_id)
                .ok_or_else(|| invalid(format!("function `{}`: a phi has no result", self.name)))?;
            if let Some(&param) = self.phi_params.get(&result) {
                let slot = self.phi_slots[&result];
                let address = self.slot_address(wb, slot)?;
                let (size, _) = self.layout_of(function.dfg.value_ty(result))?;
                self.copy_bytes(wb, address, param, size);
                self.values.insert(result, address);
            }
        }
        for inst_id in function.layout.iter_inst(block) {
            let inst = function.dfg.inst(inst_id);
            self.translate_inst(block, &mut wb, inst_id, inst)?;
            // A tail call returns its results itself.
            if inst.is_terminator() || self.tail_calls.contains(&inst_id) {
                return Ok(());
            }
        }
        Err(invalid(format!(
            "function `{}`: block{} does not end in a terminator",
            self.name,
            block.as_u32()
        )))
    }

    fn translate_inst(
        &mut self,
        block: BlockId,
        wb_ref: &mut waffle::Block,
        inst_id: InstId,
        inst: &'a dyn Inst,
    ) -> Result<(), WasmError> {
        let op = inst.as_text();
        let mut wb = *wb_ref;
        let result = self.translate_kind(block, &mut wb, inst_id, op, inst);
        *wb_ref = wb;
        result
    }

    fn translate_kind(
        &mut self,
        block: BlockId,
        wb: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        inst: &'a dyn Inst,
    ) -> Result<(), WasmError> {
        let function = self.function;
        let kind = self.resolve(inst)?;
        if let Some((wide_op, lhs, rhs)) = wide_op_of(&kind)
            && let Some(wide) = self.wide_ty(lhs)
        {
            return self.wide_arith(*wb, inst_id, wide, wide_op, (lhs, rhs));
        }
        match kind {
            // Phi inputs are passed as block arguments by the predecessors.
            NativeInstKind::Phi(_) => {}

            NativeInstKind::EvmAddMod(i) => {
                self.wide_modular(*wb, inst_id, false, [*i.lhs(), *i.rhs(), *i.modulus()])?
            }
            NativeInstKind::EvmMulMod(i) => {
                self.wide_modular(*wb, inst_id, true, [*i.lhs(), *i.rhs(), *i.modulus()])?
            }

            NativeInstKind::Add(i) => self.binary_any(
                *wb,
                inst_id,
                (*i.lhs(), *i.rhs()),
                |e, l, r| e.wide_add(l, r).0,
                |e, int, l, r| e.add_sub_mul(int, Arith::Add, l, r),
            )?,
            NativeInstKind::Sub(i) => self.binary_any(
                *wb,
                inst_id,
                (*i.lhs(), *i.rhs()),
                |e, l, r| e.wide_sub(l, r).0,
                |e, int, l, r| e.add_sub_mul(int, Arith::Sub, l, r),
            )?,
            NativeInstKind::Mul(i) => {
                self.binary(*wb, inst_id, (*i.lhs(), *i.rhs()), |e, int, l, r| {
                    e.add_sub_mul(int, Arith::Mul, l, r)
                })?
            }
            NativeInstKind::Neg(i) => self.unary_any(
                *wb,
                inst_id,
                *i.arg(),
                |e, _, v| e.wide_neg(v),
                |e, int, v| e.neg(int, v),
            )?,
            NativeInstKind::Not(i) => self.unary_any(
                *wb,
                inst_id,
                *i.arg(),
                |e, _, v| e.wide_not(v),
                |e, int, v| e.not(int, v),
            )?,
            NativeInstKind::Clz(i) => self.unary_any(
                *wb,
                inst_id,
                *i.arg(),
                |e, wide, v| e.wide_clz(wide, v),
                |e, int, v| e.clz(int, v),
            )?,
            NativeInstKind::Ctz(i) => self.unary_any(
                *wb,
                inst_id,
                *i.arg(),
                |e, wide, v| e.wide_ctz(wide, v),
                |e, int, v| e.ctz(int, v),
            )?,
            NativeInstKind::Bswap(i) => {
                if function.dfg.value_ty(*i.arg()) == Type::I1 {
                    return Err(self.unsupported_type("`bswap`", Type::I1));
                }
                self.unary_any(
                    *wb,
                    inst_id,
                    *i.arg(),
                    |e, wide, v| e.wide_bswap(wide, v),
                    |e, int, v| e.bswap(int, v),
                )?
            }
            NativeInstKind::And(i) => self.binary_any(
                *wb,
                inst_id,
                (*i.lhs(), *i.rhs()),
                |e, l, r| e.wide_bitwise(Operator::I64And, l, r),
                |e, int, l, r| e.bitwise(int, Operator::I32And, Operator::I64And, l, r),
            )?,
            NativeInstKind::Or(i) => self.binary_any(
                *wb,
                inst_id,
                (*i.lhs(), *i.rhs()),
                |e, l, r| e.wide_bitwise(Operator::I64Or, l, r),
                |e, int, l, r| e.bitwise(int, Operator::I32Or, Operator::I64Or, l, r),
            )?,
            // A wasm32 pointer is an `i32`.
            NativeInstKind::Select(i)
                if self.is_pointer(self.function.dfg.value_ty(*i.then_value())) =>
            {
                let cond = self.operand(*wb, *i.cond())?;
                let then = self.operand(*wb, *i.then_value())?;
                let otherwise = self.operand(*wb, *i.else_value())?;
                let value =
                    self.emit(*wb)
                        .op(Operator::Select, &[then, otherwise, cond], WType::I32);
                let ty = self.function.dfg.value_ty(*i.then_value());
                self.define(inst_id, 0, value, ty)?
            }
            NativeInstKind::Select(i) => {
                let cond = self.operand(*wb, *i.cond())?;
                self.binary_any(
                    *wb,
                    inst_id,
                    (*i.then_value(), *i.else_value()),
                    |e, then, otherwise| {
                        let mut chosen = then;
                        for (limb, (then, otherwise)) in
                            chosen.iter_mut().zip(then.into_iter().zip(otherwise))
                        {
                            *limb = e.select64(then, otherwise, cond);
                        }
                        chosen
                    },
                    |e, int, then, otherwise| e.select(int, then, otherwise, cond),
                )?
            }

            NativeInstKind::Xor(i) => self.binary_any(
                *wb,
                inst_id,
                (*i.lhs(), *i.rhs()),
                |e, l, r| e.wide_bitwise(Operator::I64Xor, l, r),
                |e, int, l, r| e.bitwise(int, Operator::I32Xor, Operator::I64Xor, l, r),
            )?,

            NativeInstKind::Udiv(i) => {
                self.binary(*wb, inst_id, (*i.lhs(), *i.rhs()), |e, int, l, r| {
                    e.div_rem(int, DivRem::Udiv, l, r)
                })?
            }
            NativeInstKind::Sdiv(i) => {
                self.binary(*wb, inst_id, (*i.lhs(), *i.rhs()), |e, int, l, r| {
                    e.div_rem(int, DivRem::Sdiv, l, r)
                })?
            }
            NativeInstKind::Umod(i) => {
                self.binary(*wb, inst_id, (*i.lhs(), *i.rhs()), |e, int, l, r| {
                    e.div_rem(int, DivRem::Umod, l, r)
                })?
            }
            NativeInstKind::Smod(i) => {
                self.binary(*wb, inst_id, (*i.lhs(), *i.rhs()), |e, int, l, r| {
                    e.div_rem(int, DivRem::Smod, l, r)
                })?
            }

            NativeInstKind::Shl(i) => {
                self.shift(*wb, inst_id, (*i.value(), *i.bits()), Shift::Shl)?
            }
            NativeInstKind::Shr(i) => {
                self.shift(*wb, inst_id, (*i.value(), *i.bits()), Shift::Shr)?
            }
            NativeInstKind::Sar(i) => {
                self.shift(*wb, inst_id, (*i.value(), *i.bits()), Shift::Sar)?
            }

            NativeInstKind::Uaddo(i) => {
                self.overflow(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Add, false)?
            }
            NativeInstKind::Usubo(i) => {
                self.overflow(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Sub, false)?
            }
            NativeInstKind::Umulo(i) => {
                self.overflow(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Mul, false)?
            }
            NativeInstKind::Saddo(i) => {
                self.overflow(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Add, true)?
            }
            NativeInstKind::Ssubo(i) => {
                self.overflow(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Sub, true)?
            }
            NativeInstKind::Smulo(i) => {
                self.overflow(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Mul, true)?
            }
            NativeInstKind::Snego(i) => {
                if let Some(wide) = self.wide_ty(*i.arg()) {
                    // `0 - arg` overflows only for the minimum.
                    let arg = self.wide_operand(*wb, *i.arg())?;
                    let arg = self.emit(*wb).wide_sign_extend(wide, arg);
                    let zero = self.emit(*wb).wide_zero();
                    let (value, overflow) =
                        self.wide_overflowing(*wb, wide, Arith::Sub, true, zero, arg)?;
                    self.define_wide(*wb, inst_id, 0, wide, value)?;
                    self.define(inst_id, 1, overflow, Type::I1)?;
                } else {
                    let (int, ty, arg) = self.unary_operand(*wb, op, *i.arg())?;
                    let (value, overflow) = self.emit(*wb).signed_neg_overflow(int, arg);
                    self.define(inst_id, 0, value, ty)?;
                    self.define(inst_id, 1, overflow, Type::I1)?;
                }
            }
            NativeInstKind::Uaddsat(i) => {
                self.saturating(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Add, false)?
            }
            NativeInstKind::Usubsat(i) => {
                self.saturating(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Sub, false)?
            }
            NativeInstKind::Umulsat(i) => {
                self.saturating(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Mul, false)?
            }
            NativeInstKind::Saddsat(i) => {
                self.saturating(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Add, true)?
            }
            NativeInstKind::Ssubsat(i) => {
                self.saturating(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Sub, true)?
            }
            NativeInstKind::Smulsat(i) => {
                self.saturating(*wb, inst_id, (*i.lhs(), *i.rhs()), Arith::Mul, true)?
            }

            NativeInstKind::Eq(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Eq, false)?
            }
            NativeInstKind::Ne(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Ne, false)?
            }
            NativeInstKind::Lt(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Lt, false)?
            }
            NativeInstKind::Gt(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Gt, false)?
            }
            NativeInstKind::Le(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Le, false)?
            }
            NativeInstKind::Ge(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Ge, false)?
            }
            NativeInstKind::Slt(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Lt, true)?
            }
            NativeInstKind::Sgt(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Gt, true)?
            }
            NativeInstKind::Sle(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Le, true)?
            }
            NativeInstKind::Sge(i) => {
                self.compare(*wb, inst_id, (*i.lhs(), *i.rhs()), Cmp::Ge, true)?
            }
            NativeInstKind::IsZero(i) => {
                if self.wide_ty(*i.lhs()).is_some() {
                    let arg = self.wide_operand(*wb, *i.lhs())?;
                    let value = self.emit(*wb).wide_is_zero(arg);
                    self.define(inst_id, 0, value, Type::I1)?;
                } else if self.is_pointer(function.dfg.value_ty(*i.lhs())) {
                    let arg = self.operand(*wb, *i.lhs())?;
                    let value = self.emit(*wb).is_zero(Int::I32, arg);
                    self.define(inst_id, 0, value, Type::I1)?;
                } else {
                    let (int, _, arg) = self.unary_operand(*wb, op, *i.lhs())?;
                    let value = self.emit(*wb).is_zero(int, arg);
                    self.define(inst_id, 0, value, Type::I1)?;
                }
            }

            NativeInstKind::Zext(i) => self.convert(*wb, inst_id, op, *i.from(), *i.ty(), false)?,
            NativeInstKind::Sext(i) => self.convert(*wb, inst_id, op, *i.from(), *i.ty(), true)?,
            NativeInstKind::Trunc(i) => {
                self.convert(*wb, inst_id, op, *i.from(), *i.ty(), false)?
            }
            NativeInstKind::Bitcast(i) => self.bitcast(wb, inst_id, op, *i.from(), *i.ty())?,
            NativeInstKind::IntToPtr(i) => {
                let to_ty = *i.ty();
                if !self.is_pointer(to_ty) {
                    return Err(self.unsupported_type("`int_to_ptr` result", to_ty));
                }
                // An address that does not fit in 32 bits is not an address of
                // this module.
                let value = self.index32(wb, op, *i.from(), false)?;
                self.define(inst_id, 0, value, to_ty)?;
            }
            NativeInstKind::PtrToInt(i) => {
                let from_ty = function.dfg.value_ty(*i.from());
                if !self.is_pointer(from_ty) {
                    return Err(self.unsupported_type("`ptr_to_int` operand", from_ty));
                }
                let to_ty = *i.ty();
                let arg = self.operand(*wb, *i.from())?;
                if let Some(wide) = Wide::from_type(to_ty) {
                    let limbs = self.emit(*wb).wide_extend(Int::I32, false, arg);
                    self.define_wide(*wb, inst_id, 0, wide, limbs)?;
                } else {
                    let to = self.int_ty(op, to_ty)?;
                    let value = self.emit(*wb).resize(Int::I32, to, false, arg);
                    self.define(inst_id, 0, value, to_ty)?;
                }
            }

            NativeInstKind::Mload(i) => self.mload(wb, inst_id, op, *i.addr(), *i.ty())?,
            NativeInstKind::Mstore(i) => self.mstore(wb, op, *i.addr(), *i.value(), *i.ty())?,
            NativeInstKind::Memzero(i) => self.memzero(wb, op, *i.dest(), *i.len())?,
            NativeInstKind::Memcopy(i) => self.memcopy(wb, op, *i.dest(), *i.src(), *i.len())?,
            // Every use of a value sees one value, and an undefined one reads as
            // zero in WebAssembly, so freezing changes nothing.
            NativeInstKind::Freeze(i) => self.copy_value(*wb, inst_id, *i.arg())?,
            // Sonatina's passes keep it in place. WebAssembly has no way to hide
            // a value from the engine, so the module passes it on unchanged.
            NativeInstKind::BlackBox(i) => self.copy_value(*wb, inst_id, *i.arg())?,
            NativeInstKind::Sha256Compress(i) => {
                self.sha256_compress(*wb, inst_id, *i.state(), *i.block())?
            }
            NativeInstKind::Gep(i) => self.gep(wb, inst_id, op, i.values())?,
            NativeInstKind::Alloca(i) => self.alloca(*wb, inst_id, *i.ty())?,
            NativeInstKind::MemAllocDynamic(i) => {
                self.mem_alloc_dynamic(wb, inst_id, op, *i.size())?
            }
            NativeInstKind::ObjAlloc(i) => self.obj_alloc(*wb, inst_id, *i.ty())?,
            NativeInstKind::ObjProj(i) => self.projection(*wb, inst_id, op, i.values())?,
            NativeInstKind::ConstProj(i) => self.projection(*wb, inst_id, op, i.values())?,
            NativeInstKind::ObjIndex(i) => {
                self.element_address(wb, inst_id, op, *i.object(), *i.index())?
            }
            NativeInstKind::ConstIndex(i) => {
                self.element_address(wb, inst_id, op, *i.object(), *i.index())?
            }
            NativeInstKind::ObjLoad(i) => self.obj_load(*wb, inst_id, *i.object(), true)?,
            NativeInstKind::ConstLoad(i) => self.obj_load(*wb, inst_id, *i.object(), false)?,
            NativeInstKind::ObjStore(i) => self.obj_store(*wb, *i.object(), *i.value())?,
            NativeInstKind::ObjMaterializeStack(i) => self.alias(*wb, inst_id, *i.object())?,
            NativeInstKind::ObjFromPtr(i) => self.alias(*wb, inst_id, *i.ptr())?,
            NativeInstKind::ConstRef(i) => {
                self.global_address(*wb, inst_id, op, i.global().gv())?
            }
            NativeInstKind::SymAddr(i) if let SymbolRef::Global(gv) = i.sym() => {
                self.global_address(*wb, inst_id, op, *gv)?
            }
            NativeInstKind::InsertValue(i) => {
                self.insert_value(block, *wb, inst_id, *i.dest(), *i.idx(), *i.value())?
            }
            NativeInstKind::ExtractValue(i) => {
                self.extract_value(*wb, inst_id, *i.dest(), *i.idx())?
            }

            NativeInstKind::Call(call) => {
                self.call(wb, inst_id, op, *call.callee(), call.args())?
            }

            NativeInstKind::Jump(jump) => {
                let target = self.edge(block, *jump.dest(), *wb)?;
                self.body.set_terminator(*wb, Terminator::Br { target });
            }
            NativeInstKind::Br(br) => {
                let cond_ty = function.dfg.value_ty(*br.cond());
                let int = self.int_ty(op, cond_ty)?;
                let cond = self.operand(*wb, *br.cond())?;
                let nonzero = self.edge(block, *br.nz_dest(), *wb)?;
                let zero = self.edge(block, *br.z_dest(), *wb)?;
                let terminator = if int.is_wide() {
                    // `br_if` takes an i32, so branch on the i64 being zero.
                    let is_zero = self.emit(*wb).is_zero(int, cond);
                    Terminator::CondBr {
                        cond: is_zero,
                        if_true: zero,
                        if_false: nonzero,
                    }
                } else {
                    Terminator::CondBr {
                        cond,
                        if_true: nonzero,
                        if_false: zero,
                    }
                };
                self.body.set_terminator(*wb, terminator);
            }
            NativeInstKind::BrTable(table) => {
                let scrutinee_ty = function.dfg.value_ty(*table.scrutinee());
                let scrutinee = if Wide::from_type(scrutinee_ty).is_some() {
                    Scrutinee::Wide(self.wide_operand(*wb, *table.scrutinee())?)
                } else {
                    let int = self.int_ty(op, scrutinee_ty)?;
                    Scrutinee::Int(int, self.operand(*wb, *table.scrutinee())?)
                };
                let default = *table.default();
                if let Scrutinee::Int(int, value) = scrutinee
                    && let Some((base, cases)) = self.dense_cases(int, scrutinee_ty, table.table())
                {
                    return self.jump_table(block, *wb, (int, value), (base, &cases), default);
                }

                // Each case is tested in turn; the edge arguments are
                // materialized in the block that takes the edge.
                let mut current = *wb;
                for (index, &(case, dest)) in table.table().iter().enumerate() {
                    if function.dfg.value_ty(case) != scrutinee_ty {
                        return Err(invalid(format!(
                            "function `{}`: a `br_table` case has the wrong type",
                            self.name
                        )));
                    }
                    let matched = match scrutinee {
                        Scrutinee::Int(int, scrutinee) => {
                            let case = self.operand(current, case)?;
                            self.emit(current)
                                .compare(int, Cmp::Eq, false, scrutinee, case)
                        }
                        Scrutinee::Wide(scrutinee) => {
                            let case = self.wide_operand(current, case)?;
                            self.emit(current)
                                .wide_compare(Cmp::Eq, false, scrutinee, case)
                        }
                    };
                    let if_true = self.edge(block, dest, current)?;
                    let if_false = if index + 1 < table.table().len() {
                        let next = self.body.add_block();
                        BlockTarget {
                            block: next,
                            args: vec![],
                        }
                    } else if let Some(default) = default {
                        self.edge(block, default, current)?
                    } else {
                        BlockTarget {
                            block: self.trap_block(),
                            args: vec![],
                        }
                    };
                    let next = if_false.block;
                    self.body.set_terminator(
                        current,
                        Terminator::CondBr {
                            cond: matched,
                            if_true,
                            if_false,
                        },
                    );
                    current = next;
                }
                if table.table().is_empty() {
                    let default = default.ok_or_else(|| {
                        invalid(format!(
                            "function `{}`: an empty `br_table` has no default",
                            self.name
                        ))
                    })?;
                    let target = self.edge(block, default, *wb)?;
                    self.body.set_terminator(*wb, Terminator::Br { target });
                }
            }
            NativeInstKind::Return(ret) => self.ret(*wb, ret.args().as_slice())?,
            NativeInstKind::Unreachable(_) => {
                self.body.set_terminator(*wb, Terminator::Unreachable);
            }

            // Not translated: function pointers, and symbols other than globals.
            NativeInstKind::GetFunctionPtr(_)
            | NativeInstKind::SymAddr(_)
            | NativeInstKind::SymSize(_) => return Err(self.unsupported_inst(op)),

            // Enums take the layout of the target: the tag at offset zero and
            // every variant's fields from one shared payload offset.
            NativeInstKind::EnumMake(i) => {
                self.enum_make(*wb, inst_id, *i.variant(), i.values())?
            }
            NativeInstKind::EnumWriteVariant(i) => {
                self.enum_write_variant(*wb, *i.object(), *i.variant(), i.values())?
            }
            NativeInstKind::EnumSetTag(i) => self.enum_set_tag(*wb, *i.object(), *i.variant())?,
            NativeInstKind::EnumTag(i) => self.enum_tag(*wb, inst_id, op, *i.value())?,
            NativeInstKind::EnumGetTag(i) => self.enum_tag(*wb, inst_id, op, *i.object())?,
            NativeInstKind::EnumIsVariant(i) => {
                self.enum_is_variant(*wb, inst_id, *i.value(), *i.variant())?
            }
            NativeInstKind::EnumAssertVariant(_) => {}
            NativeInstKind::EnumAssertVariantRef(i) => self.alias(*wb, inst_id, *i.object())?,
            NativeInstKind::EnumExtract(i) => {
                self.enum_extract(*wb, inst_id, *i.value(), *i.variant(), *i.field())?
            }
            NativeInstKind::EnumProj(i) => {
                self.enum_proj(*wb, inst_id, *i.object(), *i.variant(), *i.field())?
            }
        }
        Ok(())
    }

    /// `zext`, `sext` and `trunc`: change the width of an integer.
    fn convert(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        op: &str,
        from: ValueId,
        to_ty: Type,
        signed: bool,
    ) -> Result<(), WasmError> {
        let from_ty = self.function.dfg.value_ty(from);
        match (Wide::from_type(from_ty), Wide::from_type(to_ty)) {
            (None, Some(to)) => {
                let from_int = self.int_ty(op, from_ty)?;
                let value = self.operand(wb, from)?;
                let limbs = self.emit(wb).wide_extend(from_int, signed, value);
                self.define_wide(wb, inst_id, 0, to, limbs)
            }
            (Some(_), None) => {
                let to_int = self.int_ty(op, to_ty)?;
                let limbs = self.wide_operand(wb, from)?;
                let value = self.emit(wb).wide_trunc(to_int, limbs);
                self.define(inst_id, 0, value, to_ty)
            }
            // `zext` keeps the zero-extended limbs, and `trunc` drops the
            // limbs above the result.
            (Some(from_wide), Some(to)) => {
                let mut limbs = self.wide_operand(wb, from)?;
                if signed {
                    limbs = self.emit(wb).wide_sign_extend(from_wide, limbs);
                }
                self.define_wide(wb, inst_id, 0, to, limbs)
            }
            (None, None) => {
                let (from_int, _, value) = self.unary_operand(wb, op, from)?;
                let to_int = self.int_ty(op, to_ty)?;
                let value = self.emit(wb).resize(from_int, to_int, signed, value);
                self.define(inst_id, 0, value, to_ty)
            }
        }
    }

    fn call(
        &mut self,
        wb_ref: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        callee: FuncRef,
        call_args: &[ValueId],
    ) -> Result<(), WasmError> {
        let function = self.function;
        let callees = self.callees;
        let callee = callees.get(&callee).ok_or_else(|| {
            invalid(format!(
                "function `{}`: `{op}` of a function that is not declared in the module",
                self.name
            ))
        })?;
        if call_args.len() != callee.params.len() {
            return Err(invalid(format!(
                "function `{}`: `{op}` passes {} arguments but the callee takes {}",
                self.name,
                call_args.len(),
                callee.params.len()
            )));
        }
        if let Some(index) = call_args
            .iter()
            .zip(&callee.params)
            .position(|(&arg, &param)| function.dfg.value_ty(arg) != param)
        {
            return Err(invalid(format!(
                "function `{}`: `{op}` argument {index} does not have the parameter type",
                self.name
            )));
        }
        let results = function.dfg.inst_results(inst_id);
        if results.len() != callee.rets.len() {
            return Err(invalid(format!(
                "function `{}`: `{op}` has {} results but the callee returns {}",
                self.name,
                results.len(),
                callee.rets.len()
            )));
        }
        let func = match callee.target {
            CallTarget::Func(func) => func,
            CallTarget::MemoryCopy => {
                let [dst, src, len] = call_args else {
                    return Err(invalid(format!(
                        "function `{}`: `{op}` of a memory copy needs three arguments",
                        self.name
                    )));
                };
                let dst_value = self.operand(*wb_ref, *dst)?;
                let src_value = self.operand(*wb_ref, *src)?;
                let len_value = self.index32(wb_ref, op, *len, false)?;
                self.body.add_op(
                    *wb_ref,
                    Operator::MemoryCopy {
                        dst_mem: self.memory,
                        src_mem: self.memory,
                    },
                    &[dst_value, src_value, len_value],
                    &[],
                );
                // Like the C routine, the call returns its destination.
                return match function.dfg.inst_results(inst_id) {
                    [] => Ok(()),
                    _ => self.define(inst_id, 0, dst_value, callee.rets[0]),
                };
            }
            CallTarget::HeapMalloc | CallTarget::HeapFree => {
                let [argument] = call_args else {
                    return Err(invalid(format!(
                        "function `{}`: `{op}` of the allocator needs one argument",
                        self.name
                    )));
                };
                let value = self.operand(*wb_ref, *argument)?;
                let missing = || {
                    invalid(format!(
                        "function `{}`: `{op}` calls the allocator but the module has none",
                        self.name
                    ))
                };
                let (func, carriers): (Func, &[WType]) = match callee.target {
                    CallTarget::HeapMalloc => (self.arena.ok_or_else(missing)?, &[WType::I32]),
                    _ => (self.free.ok_or_else(missing)?, &[]),
                };
                let results = emit_call(&mut self.body, *wb_ref, func, &[value], carriers);
                return match function.dfg.inst_results(inst_id) {
                    [] => Ok(()),
                    _ => self.define(inst_id, 0, results[0], callee.rets[0]),
                };
            }
        };
        let wb = *wb_ref;
        let mut args = Vec::with_capacity(call_args.len() + 2);
        // The value of `stack_top` that the call to an import must put back.
        let mut stack_top_before = None;
        let tail = self.tail_calls.contains(&inst_id);
        if callee.stack_param {
            // The frame of a tail call's callee replaces this one.
            args.push(match (tail, self.sp) {
                (true, Some(sp)) => sp,
                _ => self.frame_top()?,
            });
        } else if callee.is_import
            && let (Some(globals), Some(top)) = (self.globals, self.top)
        {
            // A host function may call back into an export. Tell the export
            // where the stack of this call ends, and put the global back when
            // the host function returns, so that a trap later in this call
            // does not leave it pointing into a frame that is gone.
            stack_top_before = Some(self.body.add_op(
                wb,
                Operator::GlobalGet {
                    global_index: globals.stack_top,
                },
                &[],
                &[WType::I32],
            ));
            self.body.add_op(
                wb,
                Operator::GlobalSet {
                    global_index: globals.stack_top,
                },
                &[top],
                &[],
            );
        }
        let sret_address = match callee.sret {
            Some(storage) => {
                let (size, align) = self.layout_of(storage)?;
                let slot = self.slot(size, align)?;
                let address = self.slot_address(wb, slot)?;
                args.push(address);
                Some(address)
            }
            None => None,
        };
        for &arg in call_args {
            if let Some(wide) = self.wide_ty(arg) {
                args.extend_from_slice(&self.wide_operand(wb, arg)?[..wide.limbs()]);
            } else {
                args.push(self.operand(wb, arg)?);
            }
        }

        let mut carriers = Vec::new();
        if sret_address.is_none() {
            for ty in &callee.rets {
                repr(&self.module.ctx, *ty)
                    .expect("signature types were checked")
                    .push_carriers(&mut carriers);
            }
        }
        let values = emit_call(&mut self.body, wb, func, &args, &carriers);
        if tail {
            // `tail::rewrite` makes the call and this return a `return_call`.
            self.body.set_terminator(wb, Terminator::Return { values });
            return Ok(());
        }
        if let (Some(before), Some(globals)) = (stack_top_before, self.globals) {
            self.body.add_op(
                wb,
                Operator::GlobalSet {
                    global_index: globals.stack_top,
                },
                &[before],
                &[],
            );
        }
        if let Some(address) = sret_address {
            return self.define(inst_id, 0, address, callee.rets[0]);
        }
        let mut next = 0;
        for (index, ty) in callee.rets.iter().enumerate() {
            match repr(&self.module.ctx, *ty).expect("signature types were checked") {
                Repr::Wide(wide) => {
                    let carried = &values[next..next + wide.limbs()];
                    next += wide.limbs();
                    let limbs = self.emit(wb).wide_from_carried(wide, carried);
                    self.define_wide(wb, inst_id, index, wide, limbs)?;
                }
                Repr::Int(int) => {
                    let mut value = values[next];
                    next += 1;
                    if callee.is_import {
                        // The host may return any bits above the width of a
                        // narrow result.
                        value = self.emit(wb).canonicalize(int, value);
                    }
                    self.define(inst_id, index, value, *ty)?;
                }
                Repr::Pointer | Repr::Aggregate => {
                    self.define(inst_id, index, values[next], *ty)?;
                    next += 1;
                }
            }
        }
        Ok(())
    }

    fn ret(&mut self, wb: waffle::Block, args: &[ValueId]) -> Result<(), WasmError> {
        if args.len() != self.return_tys.len() {
            return Err(invalid(format!(
                "function `{}`: `return` has {} values but the signature has {}",
                self.name,
                args.len(),
                self.return_tys.len()
            )));
        }
        for (index, &arg) in args.iter().enumerate() {
            if self.function.dfg.value_ty(arg) != self.return_tys[index] {
                return Err(invalid(format!(
                    "function `{}`: `return` value {index} does not have the result type",
                    self.name
                )));
            }
        }
        if let Some((buffer, storage)) = self.sret {
            let source = self.operand(wb, args[0])?;
            let (size, _) = self.layout_of(storage)?;
            self.copy_bytes(wb, buffer, source, size);
            self.body
                .set_terminator(wb, Terminator::Return { values: vec![] });
            return Ok(());
        }
        let mut values = Vec::with_capacity(args.len());
        for &arg in args {
            if let Some(wide) = self.wide_ty(arg) {
                values.extend_from_slice(&self.wide_operand(wb, arg)?[..wide.limbs()]);
            } else {
                values.push(self.operand(wb, arg)?);
            }
        }
        self.body.set_terminator(wb, Terminator::Return { values });
        Ok(())
    }
}
