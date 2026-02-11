use std::{
    collections::{BTreeSet, VecDeque},
    panic::{AssertUnwindSafe, catch_unwind},
};

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, GlobalVariableRef, Immediate, Inst, InstDowncast, InstId, Module, Signature,
    Type, Value, ValueId,
    global_variable::GvInitializer,
    inst::{
        arith, cast, cmp,
        control_flow::{self, BranchInfo},
        data::{self, SymbolRef},
        evm, logic,
    },
    isa::TypeLayoutError,
    module::{FuncRef, ModuleCtx},
    object::{Directive, SectionRef},
    types::{CompoundType, CompoundTypeRef},
    visitor::Visitor,
};

use crate::{
    VerifierConfig,
    diagnostic::{Diagnostic, DiagnosticCode, Location},
    report::VerificationReport,
};

pub fn verify_module(module: &Module, cfg: &VerifierConfig) -> VerificationReport {
    let mut report = VerificationReport::default();

    verify_module_invariants(module, cfg, &mut report);

    let mut func_reports: Vec<_> = module
        .func_store
        .funcs()
        .into_par_iter()
        .map(|func_ref| {
            let Some(func_report) = module.func_store.try_view(func_ref, |func| {
                verify_function_with_symbols(&module.ctx, func_ref, func, cfg)
            }) else {
                let mut report = VerificationReport::default();
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidFuncRef,
                        "function reference is not present in function store",
                        Location::Function(func_ref),
                    ),
                    cfg.max_diagnostics,
                );
                return (func_ref, report);
            };

            (func_ref, func_report)
        })
        .collect();

    func_reports.sort_by_key(|(func_ref, _)| func_ref.as_u32());
    for (_, func_report) in func_reports {
        report.extend_with_limit(func_report.diagnostics, cfg.max_diagnostics);
        if cfg.max_diagnostics != 0 && report.diagnostics.len() >= cfg.max_diagnostics {
            break;
        }
    }

    report
}

pub fn verify_function(
    ctx: &ModuleCtx,
    func_ref: FuncRef,
    func: &Function,
    cfg: &VerifierConfig,
) -> VerificationReport {
    verify_function_with_symbols(ctx, func_ref, func, cfg)
}

pub fn verify_module_or_panic(module: &Module, cfg: &VerifierConfig) {
    let report = verify_module(module, cfg);
    if report.has_errors() {
        eprintln!("SONATINA_IR_VERIFY_FAILURE: module");
        eprintln!("{report}");
        panic!("SONATINA_IR_VERIFY_FAILURE");
    }
}

pub fn verify_function_or_panic(
    ctx: &ModuleCtx,
    func_ref: FuncRef,
    func: &Function,
    cfg: &VerifierConfig,
) {
    let report = verify_function(ctx, func_ref, func, cfg);
    if report.has_errors() {
        eprintln!("SONATINA_IR_VERIFY_FAILURE: function {}", func_ref.as_u32());
        eprintln!("{report}");
        panic!("SONATINA_IR_VERIFY_FAILURE");
    }
}

fn verify_module_invariants(
    module: &Module,
    cfg: &VerifierConfig,
    report: &mut VerificationReport,
) {
    let mut declared_refs: Vec<_> = module
        .ctx
        .declared_funcs
        .iter()
        .map(|entry| *entry.key())
        .collect();
    declared_refs.sort_by_key(|func_ref| func_ref.as_u32());

    for func_ref in &declared_refs {
        if !module.func_store.contains(*func_ref) {
            report.push(
                Diagnostic::error(
                    DiagnosticCode::InvalidFuncRef,
                    "declared function is missing from function store",
                    Location::Function(*func_ref),
                ),
                cfg.max_diagnostics,
            );
        }

        let Some(sig) = module.ctx.get_sig(*func_ref) else {
            continue;
        };

        for (index, arg_ty) in sig.args().iter().enumerate() {
            verify_signature_type(
                &module.ctx,
                *func_ref,
                *arg_ty,
                format!("signature arg {index}"),
                cfg,
                report,
            );
        }

        verify_signature_type(
            &module.ctx,
            *func_ref,
            sig.ret_ty(),
            "signature return".to_string(),
            cfg,
            report,
        );
    }

    let mut store_refs = module.func_store.funcs();
    store_refs.sort_by_key(|func_ref| func_ref.as_u32());
    for func_ref in store_refs {
        if module.ctx.get_sig(func_ref).is_none() {
            report.push(
                Diagnostic::error(
                    DiagnosticCode::InvalidSignature,
                    "function has no declared signature",
                    Location::Function(func_ref),
                ),
                cfg.max_diagnostics,
            );
        }
    }

    module.ctx.with_ty_store(|type_store| {
        for (cmpd_ref, cmpd) in type_store.all_compounds() {
            let ty = Type::Compound(cmpd_ref);
            let location = Location::Type { func: None, ty };
            if matches!(cmpd, CompoundType::Struct(s) if s.packed)
                && matches!(
                    module.ctx.triple.architecture,
                    sonatina_triple::Architecture::Evm
                )
            {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "packed struct is unsupported by the active target layout",
                        location.clone(),
                    ),
                    cfg.max_diagnostics,
                );
            }

            for nested in iter_nested_types(cmpd) {
                if let Type::Compound(nested_ref) = nested
                    && type_store.get_compound(nested_ref).is_none()
                {
                    report.push(
                        Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "compound type references a missing nested type",
                            location.clone(),
                        )
                        .with_note(format!("missing type ref: {}", nested_ref.as_u32())),
                        cfg.max_diagnostics,
                    );
                }
            }

            if !is_type_valid(&module.ctx, ty) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "type is not representable (contains a by-value recursive cycle)",
                        location.clone(),
                    ),
                    cfg.max_diagnostics,
                );
                continue;
            }

            let size_res = catch_unwind(AssertUnwindSafe(|| module.ctx.size_of(ty)));
            if !matches!(
                size_res,
                Ok(Ok(_)) | Ok(Err(TypeLayoutError::UnrepresentableType(_)))
            ) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "type layout computation failed",
                        location.clone(),
                    ),
                    cfg.max_diagnostics,
                );
            }

            let align_res = catch_unwind(AssertUnwindSafe(|| module.ctx.align_of(ty)));
            if !matches!(
                align_res,
                Ok(Ok(_)) | Ok(Err(TypeLayoutError::UnrepresentableType(_)))
            ) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "type alignment computation failed",
                        location,
                    ),
                    cfg.max_diagnostics,
                );
            }
        }
    });

    module.ctx.with_gv_store(|gv_store| {
        for gv_ref in gv_store.all_gv_refs() {
            let Some(gv_data) = gv_store.get(gv_ref) else {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidGlobalRef,
                        "global reference points to missing global data",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
                continue;
            };

            if let Type::Compound(cmpd_ref) = gv_data.ty
                && module
                    .ctx
                    .with_ty_store(|store| store.get_compound(cmpd_ref).is_none())
            {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidTypeRef,
                        "global type references a missing compound type",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
            }

            if gv_data.linkage.is_external() && gv_data.initializer.is_some() {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "external global must not define an initializer",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
            }

            if let Some(initializer) = &gv_data.initializer {
                verify_gv_initializer(module, gv_ref, initializer, gv_data.ty, cfg, report);
            }
        }
    });

    let mut object_names: Vec<_> = module.objects.keys().cloned().collect();
    object_names.sort();

    for object_name in object_names {
        let Some(object) = module.objects.get(&object_name) else {
            continue;
        };

        let mut section_names = FxHashSet::default();
        for section in &object.sections {
            let section_name = section.name.0.to_string();
            if !section_names.insert(section_name.clone()) {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "object contains duplicate section name",
                        Location::Object {
                            name: object_name.clone(),
                            section: Some(section_name.clone()),
                        },
                    ),
                    cfg.max_diagnostics,
                );
            }

            let mut entry_count = 0usize;
            let mut entry = None;
            let mut include_funcs = Vec::new();
            let mut include_set = FxHashSet::default();
            let mut local_embed_symbols = FxHashSet::default();
            for directive in &section.directives {
                match directive {
                    Directive::Entry(func) => {
                        entry_count += 1;
                        if module.ctx.get_sig(*func).is_none() {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::InvalidFuncRef,
                                    "object entry directive references unknown function",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("missing function ref: {}", func.as_u32())),
                                cfg.max_diagnostics,
                            );
                        } else if entry.is_none() {
                            entry = Some(*func);
                        }
                    }
                    Directive::Include(func) => {
                        if module.ctx.get_sig(*func).is_none() {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::InvalidFuncRef,
                                    "object include directive references unknown function",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("missing function ref: {}", func.as_u32())),
                                cfg.max_diagnostics,
                            );
                        } else if include_set.insert(*func) {
                            include_funcs.push(*func);
                        }
                    }
                    Directive::Data(gv) => {
                        let Some(gv_data) =
                            module.ctx.with_gv_store(|store| store.get(*gv).cloned())
                        else {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::InvalidGlobalRef,
                                    "object data directive references unknown global",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("missing global ref: {}", gv.as_u32())),
                                cfg.max_diagnostics,
                            );
                            continue;
                        };

                        if let Err(reason) = validate_global_for_object_data(
                            &module.ctx,
                            gv_data.ty,
                            gv_data.is_const,
                            gv_data.initializer.as_ref(),
                        ) {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::StructuralInvariantViolation,
                                    "object data directive references non-encodable global data",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("global ref: {}", gv.as_u32()))
                                .with_note(reason),
                                cfg.max_diagnostics,
                            );
                        }
                    }
                    Directive::Embed(embed) => {
                        let symbol = embed.as_symbol.0.to_string();
                        if !local_embed_symbols.insert(symbol.clone()) {
                            report.push(
                                Diagnostic::error(
                                    DiagnosticCode::StructuralInvariantViolation,
                                    "duplicate embed symbol in section",
                                    Location::Object {
                                        name: object_name.clone(),
                                        section: Some(section_name.clone()),
                                    },
                                )
                                .with_note(format!("duplicate embed symbol: &{symbol}")),
                                cfg.max_diagnostics,
                            );
                        }

                        match &embed.source {
                            SectionRef::Local(local) => {
                                let exists = object
                                    .sections
                                    .iter()
                                    .any(|candidate| candidate.name.0 == local.0);
                                if !exists {
                                    report.push(
                                        Diagnostic::error(
                                            DiagnosticCode::InvalidBlockRef,
                                            "embed source section does not exist in object",
                                            Location::Object {
                                                name: object_name.clone(),
                                                section: Some(section_name.clone()),
                                            },
                                        )
                                        .with_note(
                                            format!("missing local section: {}", local.0.as_str()),
                                        ),
                                        cfg.max_diagnostics,
                                    );
                                }
                            }
                            SectionRef::External {
                                object: ext_obj,
                                section: ext_section,
                            } => {
                                let exists = module.objects.get(ext_obj.0.as_str()).is_some_and(
                                    |target_obj| {
                                        target_obj
                                            .sections
                                            .iter()
                                            .any(|candidate| candidate.name.0 == ext_section.0)
                                    },
                                );
                                if !exists {
                                    report.push(
                                        Diagnostic::error(
                                            DiagnosticCode::InvalidBlockRef,
                                            "embed source external section does not exist",
                                            Location::Object {
                                                name: object_name.clone(),
                                                section: Some(section_name.clone()),
                                            },
                                        )
                                        .with_note(
                                            format!(
                                                "missing external section: @{}.{}",
                                                ext_obj.0.as_str(),
                                                ext_section.0.as_str()
                                            ),
                                        ),
                                        cfg.max_diagnostics,
                                    );
                                }
                            }
                        }
                    }
                }
            }

            if entry_count == 0 {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "section is missing an entry directive",
                        Location::Object {
                            name: object_name.clone(),
                            section: Some(section_name.clone()),
                        },
                    ),
                    cfg.max_diagnostics,
                );
            }
            if entry_count > 1 {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::StructuralInvariantViolation,
                        "section has multiple entry directives",
                        Location::Object {
                            name: object_name.clone(),
                            section: Some(section_name.clone()),
                        },
                    ),
                    cfg.max_diagnostics,
                );
            }

            if let Some(entry_func) = entry {
                let used_embed_symbols =
                    collect_section_used_embed_symbols(module, entry_func, &include_funcs);
                let mut missing_symbols: Vec<_> = used_embed_symbols
                    .into_iter()
                    .filter(|symbol| !local_embed_symbols.contains(symbol))
                    .collect();
                missing_symbols.sort();

                for symbol in missing_symbols {
                    report.push(
                        Diagnostic::error(
                            DiagnosticCode::StructuralInvariantViolation,
                            "section uses an embed symbol that is not declared in that section",
                            Location::Object {
                                name: object_name.clone(),
                                section: Some(section_name.clone()),
                            },
                        )
                        .with_note(format!("missing embed symbol: &{symbol}")),
                        cfg.max_diagnostics,
                    );
                }
            }
        }
    }
}

fn verify_signature_type(
    ctx: &ModuleCtx,
    func_ref: FuncRef,
    ty: Type,
    usage: String,
    cfg: &VerifierConfig,
    report: &mut VerificationReport,
) {
    let location = Location::Type {
        func: Some(func_ref),
        ty,
    };

    if !is_type_valid(ctx, ty) {
        report.push(
            Diagnostic::error(
                DiagnosticCode::InvalidTypeRef,
                "function signature contains an invalid type",
                location,
            )
            .with_note(usage),
            cfg.max_diagnostics,
        );
        return;
    }

    if has_by_value_function_type_in_signature(ctx, ty) {
        report.push(
            Diagnostic::error(
                DiagnosticCode::InvalidSignature,
                "function signature contains a by-value function type",
                location,
            )
            .with_note(usage),
            cfg.max_diagnostics,
        );
    }
}

fn has_by_value_function_type_in_signature(ctx: &ModuleCtx, ty: Type) -> bool {
    let mut visited = FxHashSet::default();
    let mut stack = vec![(ty, false)];

    while let Some((current_ty, behind_pointer)) = stack.pop() {
        let Type::Compound(cmpd_ref) = current_ty else {
            continue;
        };
        if !visited.insert((cmpd_ref, behind_pointer)) {
            continue;
        }

        let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
            continue;
        };

        match cmpd {
            CompoundType::Array { elem, .. } => {
                stack.push((elem, behind_pointer));
            }
            CompoundType::Ptr(elem) => {
                stack.push((elem, true));
            }
            CompoundType::Struct(s) => {
                for field in s.fields {
                    stack.push((field, behind_pointer));
                }
            }
            CompoundType::Func { args, ret_ty } => {
                if !behind_pointer {
                    return true;
                }
                for arg in args {
                    stack.push((arg, false));
                }
                stack.push((ret_ty, false));
            }
        }
    }

    false
}

fn validate_global_for_object_data(
    ctx: &ModuleCtx,
    ty: Type,
    is_const: bool,
    initializer: Option<&GvInitializer>,
) -> Result<(), String> {
    if !is_const {
        return Err("global must be declared const for object data emission".to_string());
    }
    let Some(initializer) = initializer else {
        return Err("global must define an initializer for object data emission".to_string());
    };

    validate_data_initializer_shape(ctx, ty, initializer)
}

fn validate_data_initializer_shape(
    ctx: &ModuleCtx,
    ty: Type,
    initializer: &GvInitializer,
) -> Result<(), String> {
    if ty.is_pointer(ctx) {
        return Err(format!(
            "type {ty:?} is unsupported for object data (pointer type)"
        ));
    }

    if ty.is_integral() {
        return match initializer {
            GvInitializer::Immediate(imm) if imm.ty() == ty => Ok(()),
            GvInitializer::Immediate(imm) => Err(format!(
                "integral initializer type mismatch: expected {ty:?}, found {:?}",
                imm.ty()
            )),
            _ => Err(format!(
                "integral type {ty:?} requires an immediate initializer"
            )),
        };
    }

    let Type::Compound(cmpd_ref) = ty else {
        return Err(format!("type {ty:?} is unsupported for object data"));
    };
    let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
        return Err(format!("type ref {} does not exist", cmpd_ref.as_u32()));
    };

    match cmpd {
        CompoundType::Array { elem, len } => {
            let GvInitializer::Array(items) = initializer else {
                return Err("array type requires array initializer".to_string());
            };
            if items.len() != len {
                return Err(format!(
                    "array initializer length mismatch: expected {len}, found {}",
                    items.len()
                ));
            }

            for item in items {
                validate_data_initializer_shape(ctx, elem, item)?;
            }
            Ok(())
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return Err(format!(
                    "type {ty:?} is unsupported for object data (packed struct)"
                ));
            }

            let GvInitializer::Struct(fields) = initializer else {
                return Err("struct type requires struct initializer".to_string());
            };
            if fields.len() != s.fields.len() {
                return Err(format!(
                    "struct initializer field count mismatch: expected {}, found {}",
                    s.fields.len(),
                    fields.len()
                ));
            }

            for (field, field_ty) in fields.iter().zip(s.fields) {
                validate_data_initializer_shape(ctx, field_ty, field)?;
            }
            Ok(())
        }
        CompoundType::Ptr(_) => Err(format!(
            "type {ty:?} is unsupported for object data (pointer type)"
        )),
        CompoundType::Func { .. } => Err(format!(
            "type {ty:?} is unsupported for object data (function type)"
        )),
    }
}

fn collect_section_used_embed_symbols(
    module: &Module,
    entry: FuncRef,
    includes: &[FuncRef],
) -> FxHashSet<String> {
    let mut seen_funcs = FxHashSet::default();
    let mut worklist = VecDeque::new();
    let mut used_embed_symbols = FxHashSet::default();

    for func in std::iter::once(entry).chain(includes.iter().copied()) {
        if seen_funcs.insert(func) {
            worklist.push_back(func);
        }
    }

    while let Some(func_ref) = worklist.pop_front() {
        let _ = module.func_store.try_view(func_ref, |func| {
            let inst_set = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        let callee = call.callee();
                        if module.ctx.get_sig(callee).is_some() && seen_funcs.insert(callee) {
                            worklist.push_back(callee);
                        }
                    }

                    let inst = func.dfg.inst(inst_id);
                    if let Some(ptr) =
                        <&data::GetFunctionPtr as InstDowncast>::downcast(inst_set, inst)
                    {
                        let callee = *ptr.func();
                        if module.ctx.get_sig(callee).is_some() && seen_funcs.insert(callee) {
                            worklist.push_back(callee);
                        }
                    }
                    if let Some(sym) = <&data::SymAddr as InstDowncast>::downcast(inst_set, inst) {
                        record_symbol_membership(
                            &module.ctx,
                            sym.sym(),
                            &mut seen_funcs,
                            &mut worklist,
                            &mut used_embed_symbols,
                        );
                    }
                    if let Some(sym) = <&data::SymSize as InstDowncast>::downcast(inst_set, inst) {
                        record_symbol_membership(
                            &module.ctx,
                            sym.sym(),
                            &mut seen_funcs,
                            &mut worklist,
                            &mut used_embed_symbols,
                        );
                    }
                }
            }
        });
    }

    used_embed_symbols
}

fn record_symbol_membership(
    ctx: &ModuleCtx,
    sym: &SymbolRef,
    seen_funcs: &mut FxHashSet<FuncRef>,
    worklist: &mut VecDeque<FuncRef>,
    used_embed_symbols: &mut FxHashSet<String>,
) {
    match sym {
        SymbolRef::Func(func) => {
            if ctx.get_sig(*func).is_some() && seen_funcs.insert(*func) {
                worklist.push_back(*func);
            }
        }
        SymbolRef::Global(_) => {}
        SymbolRef::Embed(embed) => {
            used_embed_symbols.insert(embed.0.to_string());
        }
    }
}

fn verify_gv_initializer(
    module: &Module,
    gv_ref: GlobalVariableRef,
    init: &GvInitializer,
    expected_ty: Type,
    cfg: &VerifierConfig,
    report: &mut VerificationReport,
) {
    match init {
        GvInitializer::Immediate(imm) => {
            let expected = expected_ty;
            let pointer_repl = module.ctx.type_layout.pointer_repl();
            if imm.ty() != expected
                && !(is_pointer_ty(&module.ctx, expected) && imm.ty() == pointer_repl)
            {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "global initializer immediate type does not match global type",
                        Location::Global(gv_ref),
                    )
                    .with_note(format!(
                        "expected {:?}, found {:?}",
                        expected,
                        imm.ty()
                    )),
                    cfg.max_diagnostics,
                );
            }
        }
        GvInitializer::Array(items) => {
            let Some((elem_ty, len)) = module.ctx.with_ty_store(|store| {
                let Type::Compound(cmpd_ref) = expected_ty else {
                    return None;
                };
                match store.get_compound(cmpd_ref) {
                    Some(CompoundType::Array { elem, len }) => Some((*elem, *len)),
                    _ => None,
                }
            }) else {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "array initializer used for non-array global type",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
                return;
            };

            if items.len() != len {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "array initializer length does not match declared array length",
                        Location::Global(gv_ref),
                    )
                    .with_note(format!("expected {len}, found {}", items.len())),
                    cfg.max_diagnostics,
                );
            }

            for item in items {
                verify_gv_initializer(module, gv_ref, item, elem_ty, cfg, report);
            }
        }
        GvInitializer::Struct(fields) => {
            let Some(struct_data) = module.ctx.with_ty_store(|store| {
                let Type::Compound(cmpd_ref) = expected_ty else {
                    return None;
                };
                match store.get_compound(cmpd_ref) {
                    Some(CompoundType::Struct(s)) => Some(s.clone()),
                    _ => None,
                }
            }) else {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "struct initializer used for non-struct global type",
                        Location::Global(gv_ref),
                    ),
                    cfg.max_diagnostics,
                );
                return;
            };

            if fields.len() != struct_data.fields.len() {
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "struct initializer field count does not match struct type",
                        Location::Global(gv_ref),
                    )
                    .with_note(format!(
                        "expected {}, found {}",
                        struct_data.fields.len(),
                        fields.len()
                    )),
                    cfg.max_diagnostics,
                );
            }

            for (field, ty) in fields.iter().zip(struct_data.fields) {
                verify_gv_initializer(module, gv_ref, field, ty, cfg, report);
            }
        }
    }
}

struct FuncVerifier<'a> {
    ctx: &'a ModuleCtx,
    func_ref: FuncRef,
    func: &'a Function,
    sig: Option<Signature>,
    cfg: &'a VerifierConfig,
    report: VerificationReport,

    block_order: Vec<BlockId>,
    block_to_insts: FxHashMap<BlockId, Vec<InstId>>,
    inst_to_block: FxHashMap<InstId, BlockId>,
    inst_index_in_block: FxHashMap<InstId, usize>,

    succs: FxHashMap<BlockId, Vec<BlockId>>,
    preds: FxHashMap<BlockId, Vec<BlockId>>,
    reachable: FxHashSet<BlockId>,
}

fn verify_function_with_symbols<'a>(
    ctx: &'a ModuleCtx,
    func_ref: FuncRef,
    func: &'a Function,
    cfg: &'a VerifierConfig,
) -> VerificationReport {
    let mut verifier = FuncVerifier::new(ctx, func_ref, func, cfg);
    verifier.run();
    verifier.report
}

impl<'a> FuncVerifier<'a> {
    fn new(
        ctx: &'a ModuleCtx,
        func_ref: FuncRef,
        func: &'a Function,
        cfg: &'a VerifierConfig,
    ) -> Self {
        Self {
            ctx,
            func_ref,
            func,
            sig: ctx.get_sig(func_ref),
            cfg,
            report: VerificationReport::default(),
            block_order: Vec::new(),
            block_to_insts: FxHashMap::default(),
            inst_to_block: FxHashMap::default(),
            inst_index_in_block: FxHashMap::default(),
            succs: FxHashMap::default(),
            preds: FxHashMap::default(),
            reachable: FxHashSet::default(),
        }
    }

    fn run(&mut self) {
        self.check_signature_and_values();
        self.scan_layout();
        self.check_referential_integrity();
        self.check_block_and_cfg_rules();
        self.check_phi_rules();

        if self.cfg.should_check_types() {
            self.check_type_rules();
        }
        if self.cfg.should_check_dominance() {
            self.check_dominance_rules();
        }
        if self.cfg.should_check_users() || self.cfg.should_check_value_caches() {
            self.check_metadata_consistency();
        }
    }

    fn emit(&mut self, diagnostic: Diagnostic) {
        self.report.push(diagnostic, self.cfg.max_diagnostics);
    }

    fn check_signature_and_values(&mut self) {
        let Some(sig) = self.sig.clone() else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InvalidSignature,
                "function signature is missing in module context",
                Location::Function(self.func_ref),
            ));
            return;
        };

        if self.func.arg_values.len() != sig.args().len() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InvalidSignature,
                    "argument value count does not match function signature",
                    Location::Function(self.func_ref),
                )
                .with_note(format!(
                    "expected {}, found {}",
                    sig.args().len(),
                    self.func.arg_values.len()
                )),
            );
        }

        for (index, value) in self.func.arg_values.iter().enumerate() {
            let Some(value_data) = self.func.dfg.get_value(*value) else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidValueRef,
                        "function argument references missing value",
                        Location::Function(self.func_ref),
                    )
                    .with_note(format!(
                        "arg index {index} uses missing value {}",
                        value.as_u32()
                    )),
                );
                continue;
            };

            match value_data {
                Value::Arg { ty, idx } => {
                    if !self.is_type_valid(*ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidTypeRef,
                                "argument value has an invalid type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("arg index {index}")),
                        );
                    }
                    if has_by_value_function_type_in_signature(self.ctx, *ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidSignature,
                                "argument value type contains a by-value function type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("arg index {index}")),
                        );
                    }

                    if *idx != index {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value index does not match its position",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("expected index {index}, found {idx}")),
                        );
                    }

                    if let Some(expected) = sig.args().get(index)
                        && ty != expected
                    {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value type does not match function signature",
                                Location::Value {
                                    func: self.func_ref,
                                    value: *value,
                                },
                            )
                            .with_note(format!("expected {:?}, found {:?}", expected, ty)),
                        );
                    }
                }
                _ => {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::ValueTypeMismatch,
                        "function argument table contains non-argument value",
                        Location::Value {
                            func: self.func_ref,
                            value: *value,
                        },
                    ));
                }
            }
        }

        for (value_id, value_data) in self.func.dfg.values.iter() {
            match value_data {
                Value::Immediate { imm, ty } => {
                    if imm.ty() != *ty {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "immediate value stores mismatched type metadata",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!(
                                "immediate is {:?}, value type is {:?}",
                                imm.ty(),
                                ty
                            )),
                        );
                    }
                }
                Value::Arg { ty, idx } => {
                    if !self.is_type_valid(*ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidTypeRef,
                                "argument value has an invalid type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("arg index {}", idx)),
                        );
                    }
                    if has_by_value_function_type_in_signature(self.ctx, *ty) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidSignature,
                                "argument value type contains a by-value function type",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("arg index {}", idx)),
                        );
                    }

                    let expected = sig.args().get(*idx);
                    if expected.is_none() {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value index is out of signature bounds",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("arg index {} is out of bounds", idx)),
                        );
                    } else if Some(ty) != expected {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ValueTypeMismatch,
                                "argument value type does not match signature",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("expected {:?}, found {:?}", expected, ty)),
                        );
                    }
                }
                Value::Inst { inst, ty } => {
                    if !self.func.dfg.has_inst(*inst) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidInstRef,
                                "value points to an instruction that does not exist",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("missing instruction id {}", inst.as_u32())),
                        );
                    }
                    if !self.is_type_valid(*ty) {
                        self.emit(Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "instruction value has invalid type",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        ));
                    }
                }
                Value::Global { gv, ty } => {
                    if self.ctx.with_gv_store(|store| store.get(*gv).is_none()) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::InvalidGlobalRef,
                                "value references a global that does not exist",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("missing global id {}", gv.as_u32())),
                        );
                    } else {
                        let expected_gv_ty = self.ctx.with_gv_store(|store| store.ty(*gv));
                        let matches = self
                            .pointee_ty(*ty)
                            .is_some_and(|pointee| pointee == expected_gv_ty);
                        if !matches {
                            self.emit(
                                Diagnostic::error(
                                    DiagnosticCode::ValueTypeMismatch,
                                    "global value does not have pointer-to-global type",
                                    Location::Value {
                                        func: self.func_ref,
                                        value: value_id,
                                    },
                                )
                                .with_note(format!(
                                    "global type is {:?}, value type is {:?}",
                                    expected_gv_ty, ty
                                )),
                            );
                        }
                    }
                }
                Value::Undef { ty } => {
                    if !self.is_type_valid(*ty) {
                        self.emit(Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "undef value has invalid type",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        ));
                    }
                }
            }
        }
    }

    fn scan_layout(&mut self) {
        let Some(sig) = self.sig.as_ref() else {
            return;
        };

        if sig.linkage().has_definition() && self.func.layout.entry_block().is_none() {
            self.emit(Diagnostic::error(
                DiagnosticCode::MissingEntryBlock,
                "function with definition has no entry block",
                Location::Function(self.func_ref),
            ));
            return;
        }

        if sig.linkage().is_external() && self.func.layout.entry_block().is_some() {
            self.emit(Diagnostic::error(
                DiagnosticCode::MissingEntryBlock,
                "external function declaration must not contain a layout",
                Location::Function(self.func_ref),
            ));
        }

        let mut seen_blocks = FxHashSet::default();
        let mut previous_block = None;
        let mut next_block = self.func.layout.entry_block();
        let max_block_steps = self.func.layout.block_slots_len().saturating_add(1);
        for _ in 0..max_block_steps {
            let Some(block) = next_block else {
                break;
            };

            if !self.func.layout.has_block_slot(block) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidBlockRef,
                        "layout block list points to an out-of-range block",
                        Location::Function(self.func_ref),
                    )
                    .with_note(format!("invalid block id {}", block.as_u32())),
                );
                break;
            }

            if !self.func.layout.is_block_inserted(block) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnlistedButInserted,
                    "layout linked list points at a block marked as not inserted",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
                break;
            }

            if !seen_blocks.insert(block) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::LayoutBlockCycle,
                    "layout block list contains a cycle",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
                break;
            }

            if !self.func.dfg.has_block(block) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidBlockRef,
                        "layout references a block that does not exist in DFG",
                        Location::Block {
                            func: self.func_ref,
                            block,
                        },
                    )
                    .with_note(format!("missing block id {}", block.as_u32())),
                );
            }

            if self.cfg.should_run_deep_sanity() {
                let prev = self.func.layout.try_prev_block(block);
                if prev != previous_block {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::BranchInfoMismatch,
                            "layout block backward pointer is inconsistent",
                            Location::Block {
                                func: self.func_ref,
                                block,
                            },
                        )
                        .with_note(format!(
                            "expected previous block {:?}, found {:?}",
                            previous_block.map(|b| b.as_u32()),
                            prev.map(|b| b.as_u32())
                        )),
                    );
                }
            }

            self.block_order.push(block);
            previous_block = Some(block);
            next_block = self.func.layout.try_next_block(block);
        }

        if next_block.is_some() {
            self.emit(Diagnostic::error(
                DiagnosticCode::LayoutBlockCycle,
                "layout block traversal did not terminate; cycle is likely present",
                Location::Function(self.func_ref),
            ));
        }

        let max_block_id = self
            .func
            .layout
            .block_slots_len()
            .max(self.func.dfg.num_blocks());
        for raw in 0..max_block_id {
            let block = BlockId::from_u32(raw as u32);
            let inserted = self
                .func
                .layout
                .try_is_block_inserted(block)
                .unwrap_or(false);
            let listed = seen_blocks.contains(&block);

            if inserted && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "block is marked inserted but not reachable from layout entry chain",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }
            if listed && !inserted {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnlistedButInserted,
                    "block is listed in layout chain but not marked inserted",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }
            if !self.cfg.allow_detached_entities && self.func.dfg.has_block(block) && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "DFG block is detached from layout",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }
        }

        let mut global_seen_insts = FxHashSet::default();
        let listed_blocks = self.block_order.clone();
        for block in listed_blocks {
            let mut block_insts = Vec::new();
            let mut local_seen = FxHashSet::default();
            let mut prev_inst = None;
            let mut next_inst = self.func.layout.try_first_inst_of(block).unwrap_or(None);
            let max_inst_steps = self.func.layout.inst_slots_len().saturating_add(1);

            for index in 0..max_inst_steps {
                let Some(inst) = next_inst else {
                    break;
                };

                if !self.func.layout.has_inst_slot(inst) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidInstRef,
                            "block instruction list points to an out-of-range instruction",
                            Location::Block {
                                func: self.func_ref,
                                block,
                            },
                        )
                        .with_note(format!("invalid instruction id {}", inst.as_u32())),
                    );
                    break;
                }

                if !self.func.layout.is_inst_inserted(inst) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::UnlistedButInserted,
                        "block instruction list points at instruction not marked inserted",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                    break;
                }

                if !local_seen.insert(inst) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::LayoutInstCycle,
                        "instruction list in block contains a cycle",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                    break;
                }

                if let Some(owner) = self.inst_to_block.get(&inst).copied()
                    && owner != block
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InstInMultipleBlocks,
                            "instruction appears in multiple block lists",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_note(format!(
                            "instruction already appears in block {}",
                            owner.as_u32()
                        )),
                    );
                }

                self.inst_to_block.insert(inst, block);
                self.inst_index_in_block.insert(inst, index);

                if !self.func.dfg.has_inst(inst) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::InvalidInstRef,
                        "layout references instruction that does not exist in DFG",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                }

                if let Some(claimed_block) = self.func.layout.try_inst_block(inst)
                    && claimed_block != block
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InstInMultipleBlocks,
                            "instruction block back-reference does not match list owner",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_note(format!(
                            "instruction claims block {}, list owner is {}",
                            claimed_block.as_u32(),
                            block.as_u32()
                        )),
                    );
                }

                if self.cfg.should_run_deep_sanity() {
                    let prev = self.func.layout.try_prev_inst(inst);
                    if prev != prev_inst {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::BranchInfoMismatch,
                                "instruction backward pointer is inconsistent",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!(
                                "expected previous inst {:?}, found {:?}",
                                prev_inst.map(|i| i.as_u32()),
                                prev.map(|i| i.as_u32())
                            )),
                        );
                    }
                }

                block_insts.push(inst);
                global_seen_insts.insert(inst);
                prev_inst = Some(inst);
                next_inst = self.func.layout.try_next_inst(inst);
            }

            if next_inst.is_some() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::LayoutInstCycle,
                    "instruction list traversal did not terminate; cycle is likely present",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }

            self.block_to_insts.insert(block, block_insts);
        }

        let max_inst_id = self
            .func
            .layout
            .inst_slots_len()
            .max(self.func.dfg.num_insts());
        for raw in 0..max_inst_id {
            let inst = InstId::from_u32(raw as u32);
            let inserted = self.func.layout.try_is_inst_inserted(inst).unwrap_or(false);
            let listed = global_seen_insts.contains(&inst);

            if inserted && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "instruction is marked inserted but unreachable from block instruction lists",
                    Location::Inst {
                        func: self.func_ref,
                        block: None,
                        inst,
                    },
                ));
            }
            if listed && !inserted {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnlistedButInserted,
                    "instruction appears in layout lists but is not marked inserted",
                    Location::Inst {
                        func: self.func_ref,
                        block: self.inst_to_block.get(&inst).copied(),
                        inst,
                    },
                ));
            }
            if !self.cfg.allow_detached_entities && self.func.dfg.has_inst(inst) && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "DFG instruction is detached from layout",
                    Location::Inst {
                        func: self.func_ref,
                        block: None,
                        inst,
                    },
                ));
            }
        }
    }

    fn check_referential_integrity(&mut self) {
        let mut insts_to_scan: Vec<InstId> = self
            .block_order
            .iter()
            .flat_map(|block| {
                self.block_to_insts
                    .get(block)
                    .into_iter()
                    .flatten()
                    .copied()
            })
            .collect();

        if !self.cfg.allow_detached_entities {
            for inst in self.func.dfg.insts.keys() {
                if !self.inst_to_block.contains_key(&inst) {
                    insts_to_scan.push(inst);
                }
            }
            insts_to_scan.sort_by_key(|inst| inst.as_u32());
        }

        for inst_id in insts_to_scan {
            let Some(inst) = self.func.dfg.get_inst(inst_id) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InvalidInstRef,
                    "instruction id is missing in DFG",
                    Location::Inst {
                        func: self.func_ref,
                        block: self.inst_to_block.get(&inst_id).copied(),
                        inst: inst_id,
                    },
                ));
                continue;
            };

            let refs = collect_inst_refs(inst);
            for value in refs.values {
                if !self.func.dfg.has_value(value) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidValueRef,
                            "instruction references value outside DFG value table",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("invalid value id {}", value.as_u32()))
                        .with_snippet(self.snippet_for_inst(inst_id)),
                    );
                    continue;
                }

                if !self.cfg.allow_detached_entities
                    && let Some(Value::Inst { inst, .. }) = self.func.dfg.get_value(value)
                    && !self.inst_to_block.contains_key(inst)
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InsertedButUnlisted,
                            "instruction uses detached value definition",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!(
                            "value v{} is defined by detached inst {}",
                            value.as_u32(),
                            inst.as_u32()
                        )),
                    );
                }
            }

            for block in refs.blocks {
                if !self.func.dfg.has_block(block) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidBlockRef,
                            "instruction references block outside DFG block table",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("invalid block id {}", block.as_u32())),
                    );
                }
            }

            for func_ref in refs.funcs {
                if self.ctx.get_sig(func_ref).is_none() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidFuncRef,
                            "instruction references unknown function",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("missing function id {}", func_ref.as_u32())),
                    );
                }
            }

            for gv in refs.globals {
                if self.ctx.with_gv_store(|store| store.get(gv).is_none()) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidGlobalRef,
                            "instruction references unknown global",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("missing global id {}", gv.as_u32())),
                    );
                }
            }

            for ty in refs.types {
                if !self.is_type_valid(ty) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidTypeRef,
                            "instruction references invalid type",
                            Location::Inst {
                                func: self.func_ref,
                                block: self.inst_to_block.get(&inst_id).copied(),
                                inst: inst_id,
                            },
                        )
                        .with_note(format!("invalid type {ty:?}")),
                    );
                }
            }
        }
    }

    fn check_block_and_cfg_rules(&mut self) {
        let blocks = self.block_order.clone();
        for block in blocks {
            self.succs.entry(block).or_default();
            self.preds.entry(block).or_default();
        }

        let mut seen_edges = FxHashSet::default();

        let blocks = self.block_order.clone();
        for block in blocks {
            let insts = self.block_to_insts.get(&block).cloned().unwrap_or_default();
            let mut has_non_tail_terminator = false;

            if insts.is_empty() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::EmptyBlock,
                    "block has no instructions",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
                continue;
            }

            let last_inst = *insts.last().expect("checked non-empty");
            for &inst in insts.iter().take(insts.len().saturating_sub(1)) {
                if self
                    .func
                    .dfg
                    .get_inst(inst)
                    .is_some_and(|data| data.is_terminator())
                {
                    has_non_tail_terminator = true;
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::TerminatorNotLast,
                            "terminator appears before end of block",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_snippet(self.snippet_for_inst(inst)),
                    );
                }
            }

            let Some(last_data) = self.func.dfg.get_inst(last_inst) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InvalidInstRef,
                    "block terminator instruction is missing",
                    Location::Inst {
                        func: self.func_ref,
                        block: Some(block),
                        inst: last_inst,
                    },
                ));
                continue;
            };

            if !last_data.is_terminator() {
                let code = if has_non_tail_terminator {
                    DiagnosticCode::NonTerminatorAtEnd
                } else {
                    DiagnosticCode::MissingTerminator
                };
                let message = if has_non_tail_terminator {
                    "block ends with a non-terminator after an earlier terminator"
                } else {
                    "block does not end with a terminator instruction"
                };
                self.emit(
                    Diagnostic::error(
                        code,
                        message,
                        Location::Block {
                            func: self.func_ref,
                            block,
                        },
                    )
                    .with_note(format!(
                        "last instruction is `{}` (inst {})",
                        last_data.as_text(),
                        last_inst.as_u32()
                    ))
                    .with_snippet(self.snippet_for_inst(last_inst)),
                );
                continue;
            }

            let branch = <&dyn BranchInfo as InstDowncast>::downcast(self.ctx.inst_set, last_data);
            if let Some(branch) = branch {
                let dests = branch.dests();
                if branch.num_dests() != dests.len() {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::BranchInfoMismatch,
                        "branch metadata reports inconsistent destination count",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst: last_inst,
                        },
                    ));
                }

                for dest in dests {
                    if !self.func.dfg.has_block(dest) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::BranchToMissingBlock,
                                "branch targets a block outside DFG block table",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst: last_inst,
                                },
                            )
                            .with_note(format!("invalid block id {}", dest.as_u32())),
                        );
                        continue;
                    }

                    if self.func.layout.try_is_block_inserted(dest) != Some(true) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::BranchToNonInsertedBlock,
                                "branch targets a non-inserted block",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst: last_inst,
                                },
                            )
                            .with_note(format!("target block {} is detached", dest.as_u32())),
                        );
                        continue;
                    }

                    if seen_edges.insert((block, dest)) {
                        self.succs.entry(block).or_default().push(dest);
                        self.preds.entry(dest).or_default().push(block);
                    }
                }
            }
        }

        if let Some(entry) = self.func.layout.entry_block() {
            self.reachable = compute_reachable(entry, &self.succs);
        }

        if !self.cfg.allow_unreachable_blocks {
            let blocks = self.block_order.clone();
            for block in blocks {
                if !self.reachable.contains(&block) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::UnreachableBlock,
                        "block is unreachable from function entry",
                        Location::Block {
                            func: self.func_ref,
                            block,
                        },
                    ));
                }
            }
        }
    }

    fn check_phi_rules(&mut self) {
        let entry = self.func.layout.entry_block();

        let blocks = self.block_order.clone();
        for block in blocks {
            let insts = self.block_to_insts.get(&block).cloned().unwrap_or_default();
            let preds = self.preds.get(&block).cloned().unwrap_or_default();
            let pred_set: FxHashSet<_> = preds.iter().copied().collect();

            let mut seen_non_phi = false;
            for inst in insts {
                let Some(inst_data) = self.func.dfg.get_inst(inst) else {
                    continue;
                };

                let Some(phi) =
                    <&control_flow::Phi as InstDowncast>::downcast(self.ctx.inst_set, inst_data)
                else {
                    seen_non_phi = true;
                    continue;
                };

                if seen_non_phi {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::PhiNotAtBlockTop,
                            "phi instruction must appear at the beginning of the block",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_snippet(self.snippet_for_inst(inst)),
                    );
                }

                if entry == Some(block) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::PhiInEntryBlock,
                        "entry block must not contain phi instructions",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                }

                let mut seen_incomings = FxHashSet::default();
                let result_ty = self.inst_result_ty(inst);

                for (value, pred_block) in phi.args() {
                    if !pred_set.contains(pred_block) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::PhiHasNonPredIncoming,
                                "phi incoming block is not a CFG predecessor",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!("incoming from block {}", pred_block.as_u32())),
                        );
                    }

                    if !seen_incomings.insert(*pred_block) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::PhiDuplicateIncomingBlock,
                                "phi contains duplicate incoming block",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!("duplicate predecessor {}", pred_block.as_u32())),
                        );
                    }

                    if let (Some(arg_ty), Some(res_ty)) = (self.value_ty(*value), result_ty)
                        && arg_ty != res_ty
                    {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::PhiIncomingTypeMismatch,
                                "phi incoming value type differs from phi result type",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!("expected {:?}, found {:?}", res_ty, arg_ty)),
                        );
                    }
                }

                if seen_incomings.len() != pred_set.len() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::PhiArgCountMismatchPreds,
                            "phi incoming blocks do not match predecessor set",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_note(format!(
                            "expected {} predecessor(s), found {} incoming block(s)",
                            pred_set.len(),
                            seen_incomings.len()
                        )),
                    );
                }
            }
        }
    }

    fn check_type_rules(&mut self) {
        let mut insts: Vec<_> = self
            .block_order
            .iter()
            .flat_map(|block| {
                self.block_to_insts
                    .get(block)
                    .into_iter()
                    .flatten()
                    .copied()
            })
            .collect();

        if !self.cfg.allow_detached_entities {
            let mut detached: Vec<_> = self
                .func
                .dfg
                .insts
                .keys()
                .filter(|inst| !self.inst_to_block.contains_key(inst))
                .collect();
            detached.sort_by_key(|inst| inst.as_u32());
            insts.extend(detached);
        }

        for inst_id in insts {
            let Some(inst) = self.func.dfg.get_inst(inst_id) else {
                continue;
            };

            self.verify_inst_type(inst_id, inst);
        }
    }

    fn verify_inst_type(&mut self, inst_id: InstId, inst: &dyn Inst) {
        if let Some(op) = <&arith::Neg as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_unary_integral_same(inst_id, *op.arg(), "neg");
            return;
        }
        if let Some(op) = <&logic::Not as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_unary_integral_same(inst_id, *op.arg(), "not");
            return;
        }
        if let Some(op) = <&arith::Add as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "add");
            return;
        }
        if let Some(op) = <&arith::Sub as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "sub");
            return;
        }
        if let Some(op) = <&arith::Mul as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "mul");
            return;
        }
        if let Some(op) = <&arith::Sdiv as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "sdiv");
            return;
        }
        if let Some(op) = <&arith::Udiv as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "udiv");
            return;
        }
        if let Some(op) = <&arith::Smod as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "smod");
            return;
        }
        if let Some(op) = <&arith::Umod as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "umod");
            return;
        }
        if let Some(op) = <&logic::And as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "and");
            return;
        }
        if let Some(op) = <&logic::Or as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "or");
            return;
        }
        if let Some(op) = <&logic::Xor as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_binary_integral_same(inst_id, *op.lhs(), *op.rhs(), "xor");
            return;
        }

        if let Some(op) = <&arith::Shl as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_shift(inst_id, *op.bits(), *op.value(), "shl");
            return;
        }
        if let Some(op) = <&arith::Shr as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_shift(inst_id, *op.bits(), *op.value(), "shr");
            return;
        }
        if let Some(op) = <&arith::Sar as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_shift(inst_id, *op.bits(), *op.value(), "sar");
            return;
        }

        if let Some(op) = <&cmp::Lt as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "lt");
            return;
        }
        if let Some(op) = <&cmp::Gt as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "gt");
            return;
        }
        if let Some(op) = <&cmp::Slt as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "slt");
            return;
        }
        if let Some(op) = <&cmp::Sgt as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "sgt");
            return;
        }
        if let Some(op) = <&cmp::Le as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "le");
            return;
        }
        if let Some(op) = <&cmp::Ge as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "ge");
            return;
        }
        if let Some(op) = <&cmp::Sle as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "sle");
            return;
        }
        if let Some(op) = <&cmp::Sge as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "sge");
            return;
        }
        if let Some(op) = <&cmp::Eq as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "eq");
            return;
        }
        if let Some(op) = <&cmp::Ne as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_cmp(inst_id, *op.lhs(), *op.rhs(), "ne");
            return;
        }
        if let Some(op) = <&cmp::IsZero as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(arg_ty) = self.value_ty(*op.lhs()) else {
                return;
            };
            if !arg_ty.is_integral() && !is_pointer_ty(self.ctx, arg_ty) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "iszero operand must be integral or pointer",
                        location.clone(),
                    )
                    .with_note(format!("found operand type {arg_ty:?}")),
                );
            }
            self.expect_result_ty(inst_id, Type::I1, location);
            return;
        }

        if let Some(op) = <&cast::Sext as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_ext_cast(inst_id, *op.from(), *op.ty(), true, "sext");
            return;
        }
        if let Some(op) = <&cast::Zext as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_ext_cast(inst_id, *op.from(), *op.ty(), true, "zext");
            return;
        }
        if let Some(op) = <&cast::Trunc as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            self.verify_ext_cast(inst_id, *op.from(), *op.ty(), false, "trunc");
            return;
        }
        if let Some(op) = <&cast::Bitcast as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(from_ty) = self.value_ty(*op.from()) else {
                return;
            };
            let to_ty = *op.ty();
            if self.is_function_ty(from_ty) || self.is_function_ty(to_ty) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "bitcast does not allow function types",
                    location.clone(),
                ));
            }

            let from_size = self.type_size(from_ty);
            let to_size = self.type_size(to_ty);
            if from_size.is_none() || to_size.is_none() || from_size != to_size {
                self.emit(
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

            self.expect_result_ty(inst_id, to_ty, location);
            return;
        }
        if let Some(op) = <&cast::IntToPtr as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(from_ty) = self.value_ty(*op.from()) else {
                return;
            };
            let to_ty = *op.ty();
            if !from_ty.is_integral() || !is_pointer_ty(self.ctx, to_ty) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "int_to_ptr requires integral source and pointer target",
                    location.clone(),
                ));
            }
            self.expect_result_ty(inst_id, to_ty, location);
            return;
        }
        if let Some(op) = <&cast::PtrToInt as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(from_ty) = self.value_ty(*op.from()) else {
                return;
            };
            let to_ty = *op.ty();
            if !is_pointer_ty(self.ctx, from_ty) || !to_ty.is_integral() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "ptr_to_int requires pointer source and integral target",
                    location.clone(),
                ));
            }
            self.expect_result_ty(inst_id, to_ty, location);
            return;
        }

        if let Some(op) = <&data::Mload as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(addr_ty) = self.value_ty(*op.addr()) else {
                return;
            };
            if !is_integral_or_pointer(self.ctx, addr_ty) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "mload address must be integral or pointer",
                    location.clone(),
                ));
            }

            if !self.is_storable_type(*op.ty()) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnstorableTypeInMemoryOp,
                    "mload type is not storable",
                    location.clone(),
                ));
            }

            self.expect_result_ty(inst_id, *op.ty(), location);
            return;
        }

        if let Some(op) = <&data::Mstore as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(addr_ty) = self.value_ty(*op.addr()) else {
                return;
            };
            if !is_integral_or_pointer(self.ctx, addr_ty) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "mstore address must be integral or pointer",
                    location.clone(),
                ));
            }

            if let Some(value_ty) = self.value_ty(*op.value())
                && value_ty != *op.ty()
            {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "mstore value type must match explicit type",
                        location.clone(),
                    )
                    .with_note(format!(
                        "expected {:?}, found {:?}",
                        op.ty(),
                        value_ty
                    )),
                );
            }

            if !self.is_storable_type(*op.ty()) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnstorableTypeInMemoryOp,
                    "mstore type is not storable",
                    location.clone(),
                ));
            }

            self.expect_no_result(inst_id, location);
            return;
        }

        if let Some(op) = <&data::Alloca as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            if !self.is_storable_type(*op.ty()) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnstorableTypeInMemoryOp,
                    "alloca type is not storable",
                    location.clone(),
                ));
            }

            let Some(result_ty) = self.inst_result_ty(inst_id) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "alloca must produce a pointer result",
                    location,
                ));
                return;
            };

            let pointee = self.pointee_ty(result_ty);
            if pointee != Some(*op.ty()) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultTypeMismatch,
                        "alloca result type must be pointer to allocated type",
                        self.inst_location(inst_id),
                    )
                    .with_note(format!(
                        "expected pointer to {:?}, found {:?}",
                        op.ty(),
                        result_ty
                    )),
                );
            }
            return;
        }

        if let Some(op) = <&data::Gep as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(expected_pointee) = self.gep_result_pointee(op.values(), location.clone())
            else {
                return;
            };

            let Some(result_ty) = self.inst_result_ty(inst_id) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "gep must produce a pointer result",
                    location,
                ));
                return;
            };

            if self.pointee_ty(result_ty) != Some(expected_pointee) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultTypeMismatch,
                        "gep result type does not match computed pointee type",
                        self.inst_location(inst_id),
                    )
                    .with_note(format!(
                        "expected pointer to {:?}, found {:?}",
                        expected_pointee, result_ty
                    )),
                );
            }
            return;
        }

        if let Some(op) = <&data::InsertValue as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(dest_ty) = self.value_ty(*op.dest()) else {
                return;
            };
            let Some(index_ty) = self.value_ty(*op.idx()) else {
                return;
            };
            if !index_ty.is_integral() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "insert_value index must be integral",
                    location.clone(),
                ));
                return;
            }

            let Some(field_ty) =
                self.aggregate_field_ty(dest_ty, *op.idx(), true, location.clone())
            else {
                return;
            };

            if let Some(value_ty) = self.value_ty(*op.value())
                && value_ty != field_ty
            {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "insert_value payload type does not match aggregate field type",
                        location.clone(),
                    )
                    .with_note(format!("expected {:?}, found {:?}", field_ty, value_ty)),
                );
            }

            self.expect_result_ty(inst_id, dest_ty, location);
            return;
        }

        if let Some(op) = <&data::ExtractValue as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(dest_ty) = self.value_ty(*op.dest()) else {
                return;
            };
            let Some(index_ty) = self.value_ty(*op.idx()) else {
                return;
            };
            if !index_ty.is_integral() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "extract_value index must be integral",
                    location.clone(),
                ));
                return;
            }

            let Some(field_ty) =
                self.aggregate_field_ty(dest_ty, *op.idx(), false, location.clone())
            else {
                return;
            };

            self.expect_result_ty(inst_id, field_ty, location);
            return;
        }

        if let Some(op) = <&data::GetFunctionPtr as InstDowncast>::downcast(self.ctx.inst_set, inst)
        {
            let location = self.inst_location(inst_id);
            let Some(sig) = self.ctx.get_sig(*op.func()) else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidFuncRef,
                        "get_function_ptr references unknown function",
                        location,
                    )
                    .with_note(format!("missing function id {}", op.func().as_u32())),
                );
                return;
            };

            let Some(result_ty) = self.inst_result_ty(inst_id) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "get_function_ptr must produce a result",
                    self.inst_location(inst_id),
                ));
                return;
            };

            let Some(Type::Compound(func_cmpd_ref)) = self.pointee_ty(result_ty) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "get_function_ptr result must be a pointer to function type",
                    self.inst_location(inst_id),
                ));
                return;
            };

            let matches = self.ctx.with_ty_store(|store| {
                let Some(cmpd) = store.get_compound(func_cmpd_ref) else {
                    return false;
                };

                matches!(cmpd, CompoundType::Func { args, ret_ty } if args.as_slice() == sig.args() && *ret_ty == sig.ret_ty())
            });

            if !matches {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultTypeMismatch,
                        "get_function_ptr result type does not match callee signature",
                        self.inst_location(inst_id),
                    )
                    .with_note(format!(
                        "callee signature is {}({:?}) -> {:?}",
                        sig.name(),
                        sig.args(),
                        sig.ret_ty()
                    )),
                );
            }
            return;
        }

        if let Some(op) = <&data::SymAddr as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            self.verify_symbol_ref(op.sym(), location.clone());
            self.expect_result_ty(inst_id, self.ctx.type_layout.pointer_repl(), location);
            return;
        }

        if let Some(op) = <&data::SymSize as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            self.verify_symbol_ref(op.sym(), location.clone());
            self.expect_result_ty(inst_id, self.ctx.type_layout.pointer_repl(), location);
            return;
        }

        if let Some(op) = <&control_flow::Jump as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let _ = op;
            self.expect_no_result(inst_id, self.inst_location(inst_id));
            return;
        }

        if let Some(op) = <&control_flow::Br as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            if let Some(cond_ty) = self.value_ty(*op.cond())
                && cond_ty != Type::I1
            {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "branch condition type must be i1",
                        self.inst_location(inst_id),
                    )
                    .with_note(format!("found condition type {:?}", cond_ty)),
                );
            }
            self.expect_no_result(inst_id, self.inst_location(inst_id));
            return;
        }

        if let Some(op) =
            <&control_flow::BrTable as InstDowncast>::downcast(self.ctx.inst_set, inst)
        {
            let location = self.inst_location(inst_id);
            let Some(scrutinee_ty) = self.value_ty(*op.scrutinee()) else {
                self.expect_no_result(inst_id, location);
                return;
            };
            if !scrutinee_ty.is_integral() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "br_table scrutinee must be integral",
                    location.clone(),
                ));
            }

            let mut seen_keys = FxHashSet::default();
            for (key, _) in op.table() {
                let Some(key_ty) = self.value_ty(*key) else {
                    continue;
                };
                if key_ty != scrutinee_ty {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InstOperandTypeMismatch,
                            "br_table key type must match scrutinee type",
                            location.clone(),
                        )
                        .with_note(format!("scrutinee {:?}, key {:?}", scrutinee_ty, key_ty)),
                    );
                }

                let Some(imm) = self.value_imm(*key) else {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "br_table keys must be immediate values",
                        location.clone(),
                    ));
                    continue;
                };

                if !seen_keys.insert(imm) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::InstOperandTypeMismatch,
                        "br_table has duplicate key",
                        location.clone(),
                    ));
                }
            }

            self.expect_no_result(inst_id, location);
            return;
        }

        if <&control_flow::Phi as InstDowncast>::downcast(self.ctx.inst_set, inst).is_some() {
            let _ = self.ensure_result_exists(inst_id, self.inst_location(inst_id));
            return;
        }

        if let Some(op) = <&control_flow::Call as InstDowncast>::downcast(self.ctx.inst_set, inst) {
            let location = self.inst_location(inst_id);
            let Some(callee_sig) = self.ctx.get_sig(*op.callee()) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InvalidFuncRef,
                    "call references unknown callee",
                    location,
                ));
                return;
            };

            if op.args().len() != callee_sig.args().len() {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::CallArityMismatch,
                        "call argument count does not match callee signature",
                        self.inst_location(inst_id),
                    )
                    .with_note(format!(
                        "expected {}, found {}",
                        callee_sig.args().len(),
                        op.args().len()
                    )),
                );
            }

            for (index, (arg, expected_ty)) in op.args().iter().zip(callee_sig.args()).enumerate() {
                if let Some(actual_ty) = self.value_ty(*arg)
                    && actual_ty != *expected_ty
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::CallArgTypeMismatch,
                            "call argument type does not match callee signature",
                            self.inst_location(inst_id),
                        )
                        .with_note(format!(
                            "arg {index}: expected {:?}, found {:?}",
                            expected_ty, actual_ty
                        )),
                    );
                }
            }

            if callee_sig.ret_ty().is_unit() {
                self.expect_no_result(inst_id, self.inst_location(inst_id));
            } else {
                self.expect_result_ty(inst_id, callee_sig.ret_ty(), self.inst_location(inst_id));
            }
            return;
        }

        if let Some(op) = <&control_flow::Return as InstDowncast>::downcast(self.ctx.inst_set, inst)
        {
            let location = self.inst_location(inst_id);
            let expected_ret_ty = self
                .sig
                .as_ref()
                .map(|sig| sig.ret_ty())
                .unwrap_or(Type::Unit);
            match (expected_ret_ty, op.arg()) {
                (ret_ty, None) if !ret_ty.is_unit() => {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::ReturnTypeMismatch,
                        "non-unit function return requires an argument",
                        location,
                    ));
                }
                (ret_ty, Some(_)) if ret_ty.is_unit() => {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::ReturnTypeMismatch,
                        "unit function return must not carry a value",
                        location,
                    ));
                }
                (ret_ty, Some(value)) => {
                    if let Some(actual_ty) = self.value_ty(*value)
                        && actual_ty != ret_ty
                    {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ReturnTypeMismatch,
                                "return value type does not match function return type",
                                self.inst_location(inst_id),
                            )
                            .with_note(format!("expected {:?}, found {:?}", ret_ty, actual_ty)),
                        );
                    }
                }
                _ => {}
            }

            self.expect_no_result(inst_id, self.inst_location(inst_id));
            return;
        }

        if <&control_flow::Unreachable as InstDowncast>::downcast(self.ctx.inst_set, inst).is_some()
        {
            self.expect_no_result(inst_id, self.inst_location(inst_id));
            return;
        }

        self.verify_evm_inst(inst_id, inst);
    }

    fn verify_evm_inst(&mut self, inst_id: InstId, inst: &dyn Inst) {
        if !self.is_evm_inst(inst) {
            return;
        }

        let location = self.inst_location(inst_id);
        let operands = inst.collect_values();
        let no_result = self.evm_inst_has_no_result(inst);

        if no_result {
            self.expect_no_result(inst_id, location.clone());
        } else {
            let _ = self.ensure_result_exists(inst_id, location.clone());
        }

        for value in &operands {
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

        if let Some(arity) = self.evm_integral_arity(inst) {
            self.verify_evm_same_integral(inst_id, &operands, location.clone(), arity);
            return;
        }

        if self.is_evm_malloc_inst(inst) {
            if operands.len() != 1 {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "evm_malloc expects one size operand",
                    location.clone(),
                ));
            }

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
            return;
        }

        if !no_result
            && let Some(result_ty) = self.inst_result_ty(inst_id)
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

    fn verify_evm_same_integral(
        &mut self,
        inst_id: InstId,
        operands: &[ValueId],
        location: Location,
        expected_arity: usize,
    ) {
        if operands.len() != expected_arity {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "EVM instruction has invalid operand count",
                    location.clone(),
                )
                .with_note(format!(
                    "expected {expected_arity}, found {}",
                    operands.len()
                )),
            );
        }

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

    fn is_evm_inst(&self, inst: &dyn Inst) -> bool {
        macro_rules! is_one_of {
            ($($ty:ty),+ $(,)?) => {
                false $(|| <&$ty as InstDowncast>::downcast(self.ctx.inst_set, inst).is_some())+
            };
        }

        is_one_of!(
            evm::EvmUdiv,
            evm::EvmSdiv,
            evm::EvmUmod,
            evm::EvmSmod,
            evm::EvmStop,
            evm::EvmInvalid,
            evm::EvmAddMod,
            evm::EvmMulMod,
            evm::EvmExp,
            evm::EvmByte,
            evm::EvmClz,
            evm::EvmKeccak256,
            evm::EvmAddress,
            evm::EvmBalance,
            evm::EvmOrigin,
            evm::EvmCaller,
            evm::EvmCallValue,
            evm::EvmCalldataLoad,
            evm::EvmCalldataCopy,
            evm::EvmCalldataSize,
            evm::EvmCodeSize,
            evm::EvmCodeCopy,
            evm::EvmGasPrice,
            evm::EvmExtCodeSize,
            evm::EvmExtCodeCopy,
            evm::EvmReturnDataSize,
            evm::EvmReturnDataCopy,
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
            evm::EvmMstore8,
            evm::EvmSload,
            evm::EvmSstore,
            evm::EvmMsize,
            evm::EvmGas,
            evm::EvmTload,
            evm::EvmTstore,
            evm::EvmMcopy,
            evm::EvmLog0,
            evm::EvmLog1,
            evm::EvmLog2,
            evm::EvmLog3,
            evm::EvmLog4,
            evm::EvmCreate,
            evm::EvmCall,
            evm::EvmCallCode,
            evm::EvmReturn,
            evm::EvmDelegateCall,
            evm::EvmCreate2,
            evm::EvmStaticCall,
            evm::EvmRevert,
            evm::EvmSelfDestruct,
            evm::EvmMalloc,
        )
    }

    fn evm_inst_has_no_result(&self, inst: &dyn Inst) -> bool {
        macro_rules! is_one_of {
            ($($ty:ty),+ $(,)?) => {
                false $(|| <&$ty as InstDowncast>::downcast(self.ctx.inst_set, inst).is_some())+
            };
        }

        is_one_of!(
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
        )
    }

    fn evm_integral_arity(&self, inst: &dyn Inst) -> Option<usize> {
        macro_rules! is_one_of {
            ($($ty:ty),+ $(,)?) => {
                false $(|| <&$ty as InstDowncast>::downcast(self.ctx.inst_set, inst).is_some())+
            };
        }

        if is_one_of!(
            evm::EvmUdiv,
            evm::EvmSdiv,
            evm::EvmUmod,
            evm::EvmSmod,
            evm::EvmExp,
            evm::EvmByte,
        ) {
            return Some(2);
        }

        if is_one_of!(evm::EvmAddMod, evm::EvmMulMod,) {
            return Some(3);
        }

        if is_one_of!(evm::EvmClz,) {
            return Some(1);
        }

        None
    }

    fn is_evm_malloc_inst(&self, inst: &dyn Inst) -> bool {
        <&evm::EvmMalloc as InstDowncast>::downcast(self.ctx.inst_set, inst).is_some()
    }

    fn verify_unary_integral_same(&mut self, inst_id: InstId, arg: ValueId, opname: &str) {
        let location = self.inst_location(inst_id);
        let Some(arg_ty) = self.value_ty(arg) else {
            return;
        };

        if !arg_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operand must be integral"),
                    location.clone(),
                )
                .with_note(format!("found operand type {:?}", arg_ty)),
            );
        }

        self.expect_result_ty(inst_id, arg_ty, location);
    }

    fn verify_binary_integral_same(
        &mut self,
        inst_id: InstId,
        lhs: ValueId,
        rhs: ValueId,
        opname: &str,
    ) {
        let location = self.inst_location(inst_id);
        let Some(lhs_ty) = self.value_ty(lhs) else {
            return;
        };
        let Some(rhs_ty) = self.value_ty(rhs) else {
            return;
        };

        if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must be integral"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }
        if lhs_ty != rhs_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must have identical types"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }

        self.expect_result_ty(inst_id, lhs_ty, location);
    }

    fn verify_shift(&mut self, inst_id: InstId, bits: ValueId, value: ValueId, opname: &str) {
        let location = self.inst_location(inst_id);
        let Some(bits_ty) = self.value_ty(bits) else {
            return;
        };
        let Some(value_ty) = self.value_ty(value) else {
            return;
        };

        if !bits_ty.is_integral() || !value_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must be integral"),
                    location.clone(),
                )
                .with_note(format!("bits {:?}, value {:?}", bits_ty, value_ty)),
            );
        }
        if bits_ty != value_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must have identical types"),
                    location.clone(),
                )
                .with_note(format!("bits {:?}, value {:?}", bits_ty, value_ty)),
            );
        }

        self.expect_result_ty(inst_id, value_ty, location);
    }

    fn verify_cmp(&mut self, inst_id: InstId, lhs: ValueId, rhs: ValueId, opname: &str) {
        let location = self.inst_location(inst_id);
        let Some(lhs_ty) = self.value_ty(lhs) else {
            return;
        };
        let Some(rhs_ty) = self.value_ty(rhs) else {
            return;
        };

        if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must be integral"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }
        if lhs_ty != rhs_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} operands must have identical types"),
                    location.clone(),
                )
                .with_note(format!("lhs {:?}, rhs {:?}", lhs_ty, rhs_ty)),
            );
        }

        self.expect_result_ty(inst_id, Type::I1, location);
    }

    fn verify_ext_cast(
        &mut self,
        inst_id: InstId,
        from: ValueId,
        to_ty: Type,
        is_ext: bool,
        opname: &str,
    ) {
        let location = self.inst_location(inst_id);
        let Some(from_ty) = self.value_ty(from) else {
            return;
        };

        if !from_ty.is_integral() || !to_ty.is_integral() {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                format!("{opname} requires integral source and target types"),
                location.clone(),
            ));
        }

        if is_ext && from_ty >= to_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} requires source type narrower than target type"),
                    location.clone(),
                )
                .with_note(format!("from {:?}, to {:?}", from_ty, to_ty)),
            );
        }
        if !is_ext && from_ty <= to_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    format!("{opname} requires source type wider than target type"),
                    location.clone(),
                )
                .with_note(format!("from {:?}, to {:?}", from_ty, to_ty)),
            );
        }

        self.expect_result_ty(inst_id, to_ty, location);
    }

    fn gep_result_pointee(&mut self, values: &[ValueId], location: Location) -> Option<Type> {
        let Some(base) = values.first().copied() else {
            self.emit(Diagnostic::error(
                DiagnosticCode::GepTypeComputationFailed,
                "gep requires at least one operand",
                location,
            ));
            return None;
        };

        let Some(base_ty) = self.value_ty(base) else {
            return None;
        };
        let Some(_) = self.pointee_ty(base_ty) else {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::GepTypeComputationFailed,
                    "gep base operand must be a pointer",
                    location,
                )
                .with_note(format!("found base type {:?}", base_ty)),
            );
            return None;
        };
        let mut current_ty = base_ty;

        for &idx_value in values.iter().skip(1) {
            let Some(idx_ty) = self.value_ty(idx_value) else {
                return None;
            };
            if !idx_ty.is_integral() {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::GepTypeComputationFailed,
                        "gep index operands must be integral",
                        location.clone(),
                    )
                    .with_note(format!("index type {:?}", idx_ty)),
                );
                return None;
            }

            let Type::Compound(cmpd_ref) = current_ty else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::GepTypeComputationFailed,
                        "gep attempted to index into a non-aggregate scalar type",
                        location.clone(),
                    )
                    .with_note(format!("current type {:?}", current_ty)),
                );
                return None;
            };

            let Some(cmpd) = self
                .ctx
                .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
            else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::GepTypeComputationFailed,
                    "gep references unknown compound type",
                    location.clone(),
                ));
                return None;
            };

            current_ty = match cmpd {
                CompoundType::Ptr(elem) => elem,
                CompoundType::Array { elem, .. } => elem,
                CompoundType::Struct(s) => {
                    let Some(index) = self.imm_to_nonneg_usize(
                        idx_value,
                        DiagnosticCode::GepTypeComputationFailed,
                        "struct gep indices must be non-negative immediate values",
                        location.clone(),
                    ) else {
                        return None;
                    };
                    let Some(field_ty) = s.fields.get(index).copied() else {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::GepTypeComputationFailed,
                                "struct gep index is out of bounds",
                                location.clone(),
                            )
                            .with_note(format!("index {index}, fields {}", s.fields.len())),
                        );
                        return None;
                    };

                    field_ty
                }
                CompoundType::Func { .. } => {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::GepTypeComputationFailed,
                        "gep cannot index into function type",
                        location.clone(),
                    ));
                    return None;
                }
            };
        }

        Some(current_ty)
    }

    fn imm_to_nonneg_usize(
        &mut self,
        value: ValueId,
        code: DiagnosticCode,
        message: &str,
        location: Location,
    ) -> Option<usize> {
        let Some(imm) = self.value_imm(value) else {
            self.emit(Diagnostic::error(code, message, location));
            return None;
        };

        if imm.is_negative() {
            self.emit(
                Diagnostic::error(code, message, location)
                    .with_note(format!("index immediate {:?} is negative", imm)),
            );
            return None;
        }

        Some(imm.as_usize())
    }

    fn aggregate_field_ty(
        &mut self,
        dest_ty: Type,
        idx: ValueId,
        insert_mode: bool,
        location: Location,
    ) -> Option<Type> {
        let Type::Compound(cmpd_ref) = dest_ty else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstOperandTypeMismatch,
                "aggregate operation requires struct or array destination",
                location,
            ));
            return None;
        };

        let Some(cmpd) = self
            .ctx
            .with_ty_store(|store| store.get_compound(cmpd_ref).cloned())
        else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InvalidTypeRef,
                "aggregate operation destination references unknown type",
                location,
            ));
            return None;
        };

        let code = if insert_mode {
            DiagnosticCode::InsertIndexOutOfBounds
        } else {
            DiagnosticCode::ExtractIndexOutOfBounds
        };
        let idx_imm = self.value_imm(idx);
        if let Some(imm) = idx_imm
            && imm.is_negative()
        {
            self.emit(
                Diagnostic::error(code, "aggregate index must be non-negative", location)
                    .with_note(format!("index immediate {:?}", imm)),
            );
            return None;
        }
        let idx_imm = idx_imm.map(Immediate::as_usize);

        match cmpd {
            CompoundType::Array { elem, len } => {
                if let Some(index) = idx_imm
                    && index >= len
                {
                    self.emit(
                        Diagnostic::error(code, "aggregate index is out of bounds", location)
                            .with_note(format!("index {index}, length {len}")),
                    );
                    return None;
                }
                Some(elem)
            }
            CompoundType::Struct(s) => {
                let Some(index) = idx_imm else {
                    self.emit(Diagnostic::error(
                        code,
                        "struct aggregate index must be an immediate value",
                        location,
                    ));
                    return None;
                };

                let Some(field_ty) = s.fields.get(index).copied() else {
                    self.emit(
                        Diagnostic::error(code, "aggregate index is out of bounds", location)
                            .with_note(format!("index {index}, fields {}", s.fields.len())),
                    );
                    return None;
                };

                Some(field_ty)
            }
            CompoundType::Ptr(_) | CompoundType::Func { .. } => {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InstOperandTypeMismatch,
                    "aggregate operation destination must be struct or array",
                    location,
                ));
                None
            }
        }
    }

    fn verify_symbol_ref(&mut self, sym: &SymbolRef, location: Location) {
        match sym {
            SymbolRef::Func(func) => {
                if self.ctx.get_sig(*func).is_none() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidFuncRef,
                            "symbol reference points to unknown function",
                            location,
                        )
                        .with_note(format!("missing function id {}", func.as_u32())),
                    );
                }
            }
            SymbolRef::Global(gv) => {
                if self.ctx.with_gv_store(|store| store.get(*gv).is_none()) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidGlobalRef,
                            "symbol reference points to unknown global",
                            location,
                        )
                        .with_note(format!("missing global id {}", gv.as_u32())),
                    );
                }
            }
            SymbolRef::Embed(embed) => {
                let _ = (embed, location);
            }
        }
    }

    fn check_dominance_rules(&mut self) {
        if self.block_order.is_empty() {
            return;
        }

        let mut covered = FxHashSet::default();
        let mut components = Vec::new();

        if let Some(entry) = self.func.layout.entry_block()
            && self.block_order.contains(&entry)
        {
            let nodes = compute_reachable(entry, &self.succs);
            covered.extend(nodes.iter().copied());
            components.push((entry, nodes));
        }

        if self.cfg.should_run_deep_sanity() {
            let blocks = self.block_order.clone();
            for block in blocks {
                if covered.contains(&block) {
                    continue;
                }
                let nodes = compute_reachable(block, &self.succs);
                covered.extend(nodes.iter().copied());
                components.push((block, nodes));
            }
        }

        let mut idom = FxHashMap::default();
        let block_order_index = self.block_position_map();
        for (root, nodes) in components {
            let local = compute_idom(root, &nodes, &self.succs, &self.preds, &block_order_index);
            idom.extend(local);
        }

        let blocks = self.block_order.clone();
        for block in blocks {
            if !idom.contains_key(&block) {
                continue;
            }

            let insts = self.block_to_insts.get(&block).cloned().unwrap_or_default();
            for inst in &insts {
                let Some(inst_data) = self.func.dfg.get_inst(*inst) else {
                    continue;
                };

                if <&control_flow::Phi as InstDowncast>::downcast(self.ctx.inst_set, inst_data)
                    .is_some()
                {
                    self.check_phi_edge_availability(*inst, &idom, &block_order_index);
                    continue;
                }

                let use_index = self
                    .inst_index_in_block
                    .get(inst)
                    .copied()
                    .unwrap_or(usize::MAX);
                let refs = collect_inst_refs(inst_data);
                for value in refs.values {
                    let Some(Value::Inst { inst: def_inst, .. }) = self.func.dfg.get_value(value)
                    else {
                        continue;
                    };

                    let Some(def_block) = self.inst_to_block.get(def_inst).copied() else {
                        if !self.cfg.allow_detached_entities {
                            self.emit(
                                Diagnostic::error(
                                    DiagnosticCode::DefDoesNotDominateUse,
                                    "value definition is detached from layout",
                                    Location::Inst {
                                        func: self.func_ref,
                                        block: Some(block),
                                        inst: *inst,
                                    },
                                )
                                .with_note(format!(
                                    "value v{} is defined by detached inst {}",
                                    value.as_u32(),
                                    def_inst.as_u32()
                                )),
                            );
                        }
                        continue;
                    };

                    if def_block == block {
                        let Some(def_index) = self.inst_index_in_block.get(def_inst).copied()
                        else {
                            continue;
                        };
                        if def_index >= use_index {
                            self.emit(
                                Diagnostic::error(
                                    DiagnosticCode::UseBeforeDefInBlock,
                                    "instruction uses a value before its local definition",
                                    Location::Inst {
                                        func: self.func_ref,
                                        block: Some(block),
                                        inst: *inst,
                                    },
                                )
                                .with_note(format!(
                                    "def inst {} appears at index {}, use at {}",
                                    def_inst.as_u32(),
                                    def_index,
                                    use_index
                                )),
                            );
                        }
                        continue;
                    }

                    if !dominates(def_block, block, &idom, &block_order_index) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::DefDoesNotDominateUse,
                                "value definition does not dominate its use",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst: *inst,
                                },
                            )
                            .with_note(format!(
                                "value v{} defined in block {}, used in block {}",
                                value.as_u32(),
                                def_block.as_u32(),
                                block.as_u32()
                            )),
                        );
                    }
                }
            }
        }
    }

    fn check_phi_edge_availability(
        &mut self,
        phi_inst: InstId,
        idom: &FxHashMap<BlockId, BlockId>,
        block_order_index: &FxHashMap<BlockId, usize>,
    ) {
        let Some(block) = self.inst_to_block.get(&phi_inst).copied() else {
            return;
        };
        let Some(inst_data) = self.func.dfg.get_inst(phi_inst) else {
            return;
        };
        let Some(phi) =
            <&control_flow::Phi as InstDowncast>::downcast(self.ctx.inst_set, inst_data)
        else {
            return;
        };

        for (value, pred) in phi.args() {
            let Some(Value::Inst { inst: def_inst, .. }) = self.func.dfg.get_value(*value) else {
                continue;
            };

            let Some(def_block) = self.inst_to_block.get(def_inst).copied() else {
                if !self.cfg.allow_detached_entities {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::PhiIncomingNotAvailableOnEdge,
                            "phi incoming value definition is detached from layout",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst: phi_inst,
                            },
                        )
                        .with_note(format!(
                            "value v{} is defined by detached inst {}",
                            value.as_u32(),
                            def_inst.as_u32()
                        )),
                    );
                }
                continue;
            };

            if *def_inst == phi_inst {
                if !dominates(block, *pred, idom, block_order_index) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::SelfReferentialPhiNotInLoop,
                            "self-referential phi incoming is not dominated by phi block",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst: phi_inst,
                            },
                        )
                        .with_note(format!("incoming predecessor block {}", pred.as_u32())),
                    );
                }
                continue;
            }

            if def_block != *pred && !dominates(def_block, *pred, idom, block_order_index) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::PhiIncomingNotAvailableOnEdge,
                        "phi incoming definition is not available on predecessor edge",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst: phi_inst,
                        },
                    )
                    .with_note(format!(
                        "value v{} defined in block {}, incoming predecessor {}",
                        value.as_u32(),
                        def_block.as_u32(),
                        pred.as_u32()
                    )),
                );
            }
        }
    }

    fn check_metadata_consistency(&mut self) {
        for inst in self.func.dfg.insts.keys() {
            let Some(result) = self.func.dfg.try_inst_result(inst).flatten() else {
                continue;
            };

            let Some(value_data) = self.func.dfg.get_value(result) else {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultMapBroken,
                        "inst_results points to a missing value",
                        Location::Inst {
                            func: self.func_ref,
                            block: self.inst_to_block.get(&inst).copied(),
                            inst,
                        },
                    )
                    .with_note(format!("missing value id {}", result.as_u32())),
                );
                continue;
            };

            if !matches!(value_data, Value::Inst { inst: owner, .. } if *owner == inst) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultMapBroken,
                        "inst_results and Value::Inst mapping are inconsistent",
                        Location::Inst {
                            func: self.func_ref,
                            block: self.inst_to_block.get(&inst).copied(),
                            inst,
                        },
                    )
                    .with_note(format!("inst_result points to value v{}", result.as_u32())),
                );
            }
        }

        for (value_id, value_data) in self.func.dfg.values.iter() {
            if let Value::Inst { inst, .. } = value_data
                && self.func.dfg.try_inst_result(*inst).flatten() != Some(value_id)
            {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InstResultMapBroken,
                        "Value::Inst does not map back via inst_results",
                        Location::Value {
                            func: self.func_ref,
                            value: value_id,
                        },
                    )
                    .with_note(format!("owner inst {}", inst.as_u32())),
                );
            }
        }

        if self.cfg.should_check_users() {
            let mut expected: FxHashMap<ValueId, BTreeSet<InstId>> = FxHashMap::default();
            let blocks = self.block_order.clone();
            for block in blocks {
                for &inst in self.block_to_insts.get(&block).into_iter().flatten() {
                    let Some(inst_data) = self.func.dfg.get_inst(inst) else {
                        continue;
                    };

                    inst_data.for_each_value(&mut |value| {
                        expected.entry(value).or_default().insert(inst);
                    });
                }
            }

            for value_id in self.func.dfg.values.keys() {
                let expected_users = expected.remove(&value_id).unwrap_or_default();
                let actual_users = self
                    .func
                    .dfg
                    .users_set(value_id)
                    .cloned()
                    .unwrap_or_default();

                if actual_users != expected_users {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::UsersSetMismatch,
                            "dfg.users set does not match scanned instruction uses",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!(
                            "expected {:?}, found {:?}",
                            expected_users, actual_users
                        )),
                    );
                }
            }
        }

        if self.cfg.should_check_value_caches() {
            let mut immediate_entries: Vec<_> = self
                .func
                .dfg
                .immediates
                .iter()
                .map(|(imm, value_id)| (*imm, *value_id))
                .collect();
            immediate_entries.sort_by(|(lhs_imm, lhs_value), (rhs_imm, rhs_value)| {
                lhs_value
                    .as_u32()
                    .cmp(&rhs_value.as_u32())
                    .then_with(|| format!("{lhs_imm:?}").cmp(&format!("{rhs_imm:?}")))
            });

            for (imm, value_id) in immediate_entries {
                let Some(value_data) = self.func.dfg.get_value(value_id) else {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::ImmediateCacheMismatch,
                            "immediate cache points to missing value",
                            Location::Function(self.func_ref),
                        )
                        .with_note(format!(
                            "immediate {:?} -> v{}",
                            imm,
                            value_id.as_u32()
                        )),
                    );
                    continue;
                };

                match value_data {
                    Value::Immediate { imm: actual, ty } if *actual == imm && *ty == imm.ty() => {}
                    Value::Immediate { imm: actual, ty } => {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ImmediateCacheMismatch,
                                "immediate cache entry does not match value payload",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!(
                                "cache {:?}, value imm {:?}, value ty {:?}",
                                imm, actual, ty
                            )),
                        );
                    }
                    _ => {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ImmediateCacheMismatch,
                                "immediate cache entry points to non-immediate value",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("cache immediate {:?}", imm)),
                        );
                    }
                }
            }

            for (value_id, value_data) in self.func.dfg.values.iter() {
                if let Value::Immediate { imm, .. } = value_data {
                    if self.func.dfg.immediates.get(imm) != Some(&value_id) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::ImmediateCacheMismatch,
                                "immediate value does not round-trip through immediate cache",
                                Location::Value {
                                    func: self.func_ref,
                                    value: value_id,
                                },
                            )
                            .with_note(format!("immediate {:?}", imm)),
                        );
                    }
                }
            }

            let mut global_entries: Vec<_> = self
                .func
                .dfg
                .globals
                .iter()
                .map(|(gv, value_id)| (*gv, *value_id))
                .collect();
            global_entries.sort_by(|(lhs_gv, lhs_value), (rhs_gv, rhs_value)| {
                lhs_gv
                    .as_u32()
                    .cmp(&rhs_gv.as_u32())
                    .then_with(|| lhs_value.as_u32().cmp(&rhs_value.as_u32()))
            });

            for (gv, value_id) in global_entries {
                let Some(value_data) = self.func.dfg.get_value(value_id) else {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::GlobalCacheMismatch,
                            "global cache points to missing value",
                            Location::Function(self.func_ref),
                        )
                        .with_note(format!(
                            "global {} -> v{}",
                            gv.as_u32(),
                            value_id.as_u32()
                        )),
                    );
                    continue;
                };

                if !matches!(value_data, Value::Global { gv: actual, .. } if *actual == gv) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::GlobalCacheMismatch,
                            "global cache entry does not match global value payload",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!("cache global {}", gv.as_u32())),
                    );
                }
            }

            for (value_id, value_data) in self.func.dfg.values.iter() {
                if let Value::Global { gv, .. } = value_data
                    && self.func.dfg.globals.get(gv) != Some(&value_id)
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::GlobalCacheMismatch,
                            "global value does not round-trip through global cache",
                            Location::Value {
                                func: self.func_ref,
                                value: value_id,
                            },
                        )
                        .with_note(format!("global id {}", gv.as_u32())),
                    );
                }
            }
        }
    }

    fn ensure_result_exists(&mut self, inst: InstId, location: Location) -> Option<Type> {
        let Some(value_id) = self.func.dfg.try_inst_result(inst).flatten() else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "instruction is expected to produce a result value",
                location,
            ));
            return None;
        };

        self.value_ty(value_id)
    }

    fn expect_no_result(&mut self, inst: InstId, location: Location) {
        if self.func.dfg.try_inst_result(inst).flatten().is_some() {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "instruction must not produce a result value",
                location,
            ));
        }
    }

    fn expect_result_ty(&mut self, inst: InstId, expected_ty: Type, location: Location) {
        let Some(actual_ty) = self.ensure_result_exists(inst, location.clone()) else {
            return;
        };

        if actual_ty != expected_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "instruction result type does not match expected type",
                    location,
                )
                .with_note(format!("expected {:?}, found {:?}", expected_ty, actual_ty)),
            );
        }
    }

    fn inst_result_ty(&self, inst: InstId) -> Option<Type> {
        let value_id = self.func.dfg.try_inst_result(inst).flatten()?;
        self.value_ty(value_id)
    }

    fn value_ty(&self, value: ValueId) -> Option<Type> {
        match self.func.dfg.get_value(value) {
            Some(Value::Inst { ty, .. })
            | Some(Value::Arg { ty, .. })
            | Some(Value::Immediate { ty, .. })
            | Some(Value::Global { ty, .. })
            | Some(Value::Undef { ty }) => Some(*ty),
            None => None,
        }
    }

    fn value_imm(&self, value: ValueId) -> Option<Immediate> {
        match self.func.dfg.get_value(value) {
            Some(Value::Immediate { imm, .. }) => Some(*imm),
            _ => None,
        }
    }

    fn inst_location(&self, inst: InstId) -> Location {
        Location::Inst {
            func: self.func_ref,
            block: self.inst_to_block.get(&inst).copied(),
            inst,
        }
    }

    fn snippet_for_inst(&self, inst: InstId) -> Option<String> {
        let block = self.inst_to_block.get(&inst).copied()?;
        let insts = self.block_to_insts.get(&block)?;
        let pos = insts.iter().position(|candidate| *candidate == inst)?;

        let mut snippet = String::new();
        if let Some(sig) = &self.sig {
            snippet.push_str(&format!(
                "func %{}({:?}) -> {:?}\n",
                sig.name(),
                sig.args(),
                sig.ret_ty()
            ));
        }
        snippet.push_str(&format!("  {block}:\n"));

        let start = pos.saturating_sub(2);
        let end = (pos + 3).min(insts.len());
        for (idx, inst_id) in insts[start..end].iter().enumerate() {
            let absolute = start + idx;
            let marker = if absolute == pos { '>' } else { ' ' };
            let name = self
                .func
                .dfg
                .get_inst(*inst_id)
                .map(Inst::as_text)
                .unwrap_or("<missing>");
            snippet.push_str(&format!(" {marker} inst{}: {name}\n", inst_id.as_u32()));
        }

        Some(snippet)
    }

    fn type_size(&self, ty: Type) -> Option<usize> {
        if !self.is_type_valid(ty) {
            return None;
        }

        let result = catch_unwind(AssertUnwindSafe(|| self.ctx.size_of(ty)));
        match result {
            Ok(Ok(size)) => Some(size),
            _ => None,
        }
    }

    fn is_function_ty(&self, ty: Type) -> bool {
        let Type::Compound(cmpd_ref) = ty else {
            return false;
        };

        self.ctx.with_ty_store(|store| {
            store
                .get_compound(cmpd_ref)
                .is_some_and(|cmpd| matches!(cmpd, CompoundType::Func { .. }))
        })
    }

    fn is_storable_type(&self, ty: Type) -> bool {
        self.type_size(ty).is_some() && !self.is_function_ty(ty)
    }

    fn is_type_valid(&self, ty: Type) -> bool {
        is_type_valid(self.ctx, ty)
    }

    fn pointee_ty(&self, ty: Type) -> Option<Type> {
        let Type::Compound(cmpd_ref) = ty else {
            return None;
        };

        self.ctx.with_ty_store(|store| {
            let cmpd = store.get_compound(cmpd_ref)?;
            if let CompoundType::Ptr(elem) = cmpd {
                Some(*elem)
            } else {
                None
            }
        })
    }

    fn block_position_map(&self) -> FxHashMap<BlockId, usize> {
        self.block_order
            .iter()
            .enumerate()
            .map(|(index, block)| (*block, index))
            .collect()
    }
}

#[derive(Default)]
struct InstRefs {
    values: Vec<ValueId>,
    blocks: Vec<BlockId>,
    funcs: Vec<FuncRef>,
    globals: Vec<GlobalVariableRef>,
    types: Vec<Type>,
}

fn collect_inst_refs(inst: &dyn Inst) -> InstRefs {
    struct RefCollector<'a> {
        refs: &'a mut InstRefs,
    }

    impl Visitor for RefCollector<'_> {
        fn visit_value_id(&mut self, item: ValueId) {
            self.refs.values.push(item);
        }

        fn visit_block_id(&mut self, item: BlockId) {
            self.refs.blocks.push(item);
        }

        fn visit_func_ref(&mut self, item: FuncRef) {
            self.refs.funcs.push(item);
        }

        fn visit_gv_ref(&mut self, item: GlobalVariableRef) {
            self.refs.globals.push(item);
        }

        fn visit_ty(&mut self, item: &Type) {
            self.refs.types.push(*item);
        }
    }

    let mut refs = InstRefs::default();
    let mut collector = RefCollector { refs: &mut refs };
    inst.accept(&mut collector);
    refs
}

fn iter_nested_types(cmpd: &CompoundType) -> Vec<Type> {
    match cmpd {
        CompoundType::Array { elem, .. } => vec![*elem],
        CompoundType::Ptr(elem) => vec![*elem],
        CompoundType::Struct(data) => data.fields.clone(),
        CompoundType::Func { args, ret_ty } => {
            let mut nested = args.to_vec();
            nested.push(*ret_ty);
            nested
        }
    }
}

fn is_type_valid(ctx: &ModuleCtx, ty: Type) -> bool {
    let Type::Compound(root) = ty else {
        return true;
    };

    let mut reachable = FxHashSet::default();
    let mut stack = vec![root];
    let mut by_value_edges: FxHashMap<CompoundTypeRef, Vec<CompoundTypeRef>> = FxHashMap::default();

    while let Some(cmpd_ref) = stack.pop() {
        if !reachable.insert(cmpd_ref) {
            continue;
        }

        let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
            return false;
        };

        let mut push_nested = |nested: Type, by_value: bool| {
            let Type::Compound(nested_ref) = nested else {
                return;
            };
            stack.push(nested_ref);
            if by_value {
                by_value_edges.entry(cmpd_ref).or_default().push(nested_ref);
            }
        };

        match cmpd {
            CompoundType::Array { elem, .. } => push_nested(elem, true),
            CompoundType::Ptr(elem) => push_nested(elem, false),
            CompoundType::Struct(data) => {
                for field in data.fields {
                    push_nested(field, true);
                }
            }
            CompoundType::Func { args, ret_ty } => {
                for arg in args {
                    push_nested(arg, true);
                }
                push_nested(ret_ty, true);
            }
        }
    }

    #[derive(Clone, Copy)]
    enum VisitState {
        Visiting,
        Done,
    }

    let mut states: FxHashMap<CompoundTypeRef, VisitState> = FxHashMap::default();
    for start in reachable.iter().copied() {
        if states.contains_key(&start) {
            continue;
        }

        states.insert(start, VisitState::Visiting);
        let mut dfs_stack = vec![(start, 0usize)];
        while let Some((node, next_index)) = dfs_stack.last_mut() {
            let successors = by_value_edges.get(node).map(Vec::as_slice).unwrap_or(&[]);
            if *next_index >= successors.len() {
                states.insert(*node, VisitState::Done);
                dfs_stack.pop();
                continue;
            }

            let successor = successors[*next_index];
            *next_index += 1;

            match states.get(&successor) {
                Some(VisitState::Visiting) => return false,
                Some(VisitState::Done) => {}
                None => {
                    states.insert(successor, VisitState::Visiting);
                    dfs_stack.push((successor, 0));
                }
            }
        }
    }

    true
}

fn is_pointer_ty(ctx: &ModuleCtx, ty: Type) -> bool {
    let Type::Compound(cmpd_ref) = ty else {
        return false;
    };

    ctx.with_ty_store(|store| {
        store
            .get_compound(cmpd_ref)
            .is_some_and(|cmpd| matches!(cmpd, CompoundType::Ptr(_)))
    })
}

fn is_integral_or_pointer(ctx: &ModuleCtx, ty: Type) -> bool {
    ty.is_integral() || is_pointer_ty(ctx, ty)
}

fn compute_reachable(
    entry: BlockId,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
) -> FxHashSet<BlockId> {
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::new();

    seen.insert(entry);
    queue.push_back(entry);

    while let Some(block) = queue.pop_front() {
        let mut targets = succs.get(&block).cloned().unwrap_or_default();
        targets.sort_by_key(|b| b.as_u32());

        for target in targets {
            if seen.insert(target) {
                queue.push_back(target);
            }
        }
    }

    seen
}

fn compute_idom(
    root: BlockId,
    nodes: &FxHashSet<BlockId>,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
    preds: &FxHashMap<BlockId, Vec<BlockId>>,
    block_order: &FxHashMap<BlockId, usize>,
) -> FxHashMap<BlockId, BlockId> {
    let mut rpo = compute_rpo(root, nodes, succs, block_order);
    if rpo.is_empty() {
        rpo.push(root);
    }

    let rpo_index: FxHashMap<_, _> = rpo
        .iter()
        .enumerate()
        .map(|(idx, block)| (*block, idx))
        .collect();

    let mut idom = FxHashMap::default();
    idom.insert(root, root);

    let mut changed = true;
    while changed {
        changed = false;

        for block in rpo.iter().copied().skip(1) {
            let mut pred_candidates: Vec<_> = preds
                .get(&block)
                .into_iter()
                .flatten()
                .copied()
                .filter(|pred| nodes.contains(pred) && idom.contains_key(pred))
                .collect();
            pred_candidates.sort_by_key(|pred| pred.as_u32());

            let Some(mut new_idom) = pred_candidates.first().copied() else {
                continue;
            };

            for pred in pred_candidates.into_iter().skip(1) {
                new_idom = intersect_idom(pred, new_idom, &idom, &rpo_index);
            }

            if idom.get(&block).copied() != Some(new_idom) {
                idom.insert(block, new_idom);
                changed = true;
            }
        }
    }

    idom
}

fn compute_rpo(
    root: BlockId,
    nodes: &FxHashSet<BlockId>,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
    block_order: &FxHashMap<BlockId, usize>,
) -> Vec<BlockId> {
    let mut order = Vec::new();
    let mut seen = FxHashSet::default();
    let mut stack = vec![(root, false)];

    while let Some((block, expanded)) = stack.pop() {
        if !nodes.contains(&block) {
            continue;
        }

        if expanded {
            order.push(block);
            continue;
        }

        if !seen.insert(block) {
            continue;
        }

        stack.push((block, true));

        let mut children = succs.get(&block).cloned().unwrap_or_default();
        children.retain(|child| nodes.contains(child));
        children.sort_by_key(|child| {
            (
                block_order.get(child).copied().unwrap_or(usize::MAX),
                child.as_u32(),
            )
        });

        for child in children.into_iter().rev() {
            stack.push((child, false));
        }
    }

    order.reverse();
    order
}

fn intersect_idom(
    mut lhs: BlockId,
    mut rhs: BlockId,
    idom: &FxHashMap<BlockId, BlockId>,
    rpo_index: &FxHashMap<BlockId, usize>,
) -> BlockId {
    while lhs != rhs {
        while rpo_index.get(&lhs).copied().unwrap_or(usize::MAX)
            > rpo_index.get(&rhs).copied().unwrap_or(usize::MAX)
        {
            lhs = idom[&lhs];
        }

        while rpo_index.get(&rhs).copied().unwrap_or(usize::MAX)
            > rpo_index.get(&lhs).copied().unwrap_or(usize::MAX)
        {
            rhs = idom[&rhs];
        }
    }

    lhs
}

fn dominates(
    dom: BlockId,
    block: BlockId,
    idom: &FxHashMap<BlockId, BlockId>,
    block_order: &FxHashMap<BlockId, usize>,
) -> bool {
    if dom == block {
        return true;
    }

    let mut current = block;
    let mut steps = 0usize;
    let step_limit = block_order.len().saturating_add(1);
    while let Some(parent) = idom.get(&current).copied() {
        if parent == dom {
            return true;
        }
        if parent == current {
            return false;
        }
        current = parent;
        steps += 1;
        if steps > step_limit {
            break;
        }
    }

    false
}
