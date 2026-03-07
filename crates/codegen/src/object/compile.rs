use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    GlobalVariableRef, InstDowncast, Module,
    inst::{
        arith::Uaddo,
        data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
    },
    module::FuncRef,
    object::EmbedSymbol,
};
use sonatina_triple::Architecture;
use sonatina_verifier::{
    Location, VerificationLevel, VerifierConfig, verify_module, verify_module_invariants,
};
use tracing::{debug_span, info_span, trace_span};

use super::{
    CompileOptions,
    artifact::ObjectArtifact,
    error::ObjectCompileError,
    link::{LinkSectionError, link_section},
    resolve::{ObjectId, ResolvedProgram, SectionId},
};
use crate::machinst::lower::{LowerBackend, SectionLoweringCtx};

fn compile_required_sections_into_cache<B: LowerBackend>(
    program: &ResolvedProgram<'_>,
    backend: &B,
    required: Option<&FxHashSet<SectionId>>,
    opts: &CompileOptions<B::FixupPolicy>,
) -> Result<FxHashMap<SectionId, super::artifact::SectionArtifact>, Vec<ObjectCompileError>> {
    let _span = debug_span!(
        "sonatina.codegen.object.compile_required_sections_into_cache",
        required_len = ?required.map(|required| required.len())
    )
    .entered();
    let order = {
        let _span = trace_span!("sonatina.codegen.object.topo_sort_sections").entered();
        topo_sort_sections(program)
    };

    let mut cache: FxHashMap<SectionId, super::artifact::SectionArtifact> = FxHashMap::default();
    for section_id in order {
        if required.is_none_or(|required| required.contains(&section_id)) {
            let _span = trace_span!(
                "sonatina.codegen.object.compile_section_if_required",
                section_object = section_id.object.0,
                section = section_id.section
            )
            .entered();
            compile_section(program, backend, section_id, &mut cache, opts)?;
        }
    }

    Ok(cache)
}

fn verify_module_for_codegen(
    module: &Module,
    cfg: &VerifierConfig,
) -> Result<(), Vec<ObjectCompileError>> {
    let _span = debug_span!(
        "sonatina.codegen.object.verify_module_for_codegen",
        verification_level = ?cfg.level
    )
    .entered();
    let fast_invariants_only = matches!(cfg.level, VerificationLevel::Fast)
        && !cfg.should_check_dominance()
        && !cfg.should_check_users()
        && !cfg.should_check_value_caches();
    let report = if fast_invariants_only {
        verify_module_invariants(module, cfg)
    } else {
        verify_module(module, cfg)
    };
    if report.has_errors() {
        return Err(vec![ObjectCompileError::VerifierFailed { report }]);
    }

    if !cfg.should_check_types() {
        let mut type_cfg = cfg.clone();
        type_cfg.level = VerificationLevel::Standard;
        let mut report = verify_module(module, &type_cfg);
        report
            .diagnostics
            .retain(|diagnostic| diagnostic_targets_multi_result_inst(module, &diagnostic.primary));
        if report.has_errors() {
            return Err(vec![ObjectCompileError::VerifierFailed { report }]);
        }
    }

    Ok(())
}

fn diagnostic_targets_multi_result_inst(module: &Module, location: &Location) -> bool {
    let Location::Inst { func, inst, .. } = *location else {
        return false;
    };

    module.func_store.view(func, |function| {
        let inst_data = function.dfg.inst(inst);
        function.dfg.inst_results(inst).len() != 1
            || <&Uaddo as InstDowncast>::downcast(function.inst_set(), inst_data).is_some()
    })
}

fn reject_unsupported_evm_multi_return(
    module: &Module,
    funcs: &[FuncRef],
    object: &sonatina_ir::object::ObjectName,
    section: &sonatina_ir::object::SectionName,
) -> Vec<ObjectCompileError> {
    if !matches!(module.ctx.triple.architecture, Architecture::Evm) {
        return vec![];
    }

    let mut errors = Vec::new();
    for &func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        if sig.ret_tys().len() > 1 {
            errors.push(ObjectCompileError::BackendError {
                object: object.clone(),
                section: section.clone(),
                func,
                message: format!(
                    "EVM backend does not support functions with {} return values",
                    sig.ret_tys().len()
                ),
            });
        }

        module.func_store.view(func, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if let Some(call) = function.dfg.cast_call(inst) {
                        let call_results = function.dfg.inst_results(inst);
                        let callee_name = module
                            .ctx
                            .get_sig(*call.callee())
                            .map(|sig| format!("%{}", sig.name()))
                            .unwrap_or_else(|| format!("{:?}", call.callee()));

                        if call_results.len() > 1 {
                            errors.push(ObjectCompileError::BackendError {
                                object: object.clone(),
                                section: section.clone(),
                                func,
                                message: format!(
                                    "EVM backend does not support call inst{} with {} results to {callee_name}",
                                    inst.as_u32(),
                                    call_results.len()
                                ),
                            });
                        }

                        if let Some(callee_sig) = module.ctx.get_sig(*call.callee()) {
                            if callee_sig.ret_tys().len() > 1 {
                                errors.push(ObjectCompileError::BackendError {
                                    object: object.clone(),
                                    section: section.clone(),
                                    func,
                                    message: format!(
                                        "EVM backend does not support calls to {callee_name} with {} return values",
                                        callee_sig.ret_tys().len()
                                    ),
                                });
                            }
                            if call_results.len() != callee_sig.ret_tys().len() {
                                errors.push(ObjectCompileError::BackendError {
                                    object: object.clone(),
                                    section: section.clone(),
                                    func,
                                    message: format!(
                                        "call inst{} result count {} does not match callee {callee_name} return count {}",
                                        inst.as_u32(),
                                        call_results.len(),
                                        callee_sig.ret_tys().len()
                                    ),
                                });
                            }
                        }
                    }

                    if let Some(return_args) = function.dfg.return_args(inst) {
                        if return_args.len() > 1 {
                            errors.push(ObjectCompileError::BackendError {
                                object: object.clone(),
                                section: section.clone(),
                                func,
                                message: format!(
                                    "EVM backend does not support return inst{} with {} values",
                                    inst.as_u32(),
                                    return_args.len()
                                ),
                            });
                        }
                        if return_args.len() != sig.ret_tys().len() {
                            errors.push(ObjectCompileError::BackendError {
                                object: object.clone(),
                                section: section.clone(),
                                func,
                                message: format!(
                                    "return inst{} value count {} does not match function signature return count {}",
                                    inst.as_u32(),
                                    return_args.len(),
                                    sig.ret_tys().len()
                                ),
                            });
                        }
                    }
                }
            }
        });
    }

    errors
}

pub fn compile_all_objects<B: LowerBackend>(
    module: &Module,
    backend: &B,
    opts: &CompileOptions<B::FixupPolicy>,
) -> Result<Vec<ObjectArtifact>, Vec<ObjectCompileError>> {
    let _span = info_span!("sonatina.codegen.object.compile_all_objects").entered();
    {
        let _span = debug_span!("sonatina.codegen.object.verify").entered();
        verify_module_for_codegen(module, &opts.verifier_cfg)?;
    }
    let program = {
        let _span = debug_span!("sonatina.codegen.object.resolve_program").entered();
        ResolvedProgram::resolve(module)?
    };
    let mut cache = {
        let _span = debug_span!(
            "sonatina.codegen.object.compile_required_sections",
            object_count = program.objects.len()
        )
        .entered();
        compile_required_sections_into_cache(&program, backend, None, opts)?
    };

    let _span = debug_span!(
        "sonatina.codegen.object.materialize_object_artifacts",
        object_count = program.objects.len()
    )
    .entered();
    let mut artifacts = Vec::new();
    for (idx, obj) in program.objects.iter().enumerate() {
        let object_id = ObjectId(idx as u32);
        let mut sections = IndexMap::new();
        for (section_idx, section) in obj.sections.iter().enumerate() {
            let id = SectionId {
                object: object_id,
                section: section_idx as u32,
            };
            let artifact = cache.remove(&id).ok_or_else(|| {
                vec![ObjectCompileError::LinkError {
                    object: obj.name.clone(),
                    section: section.name.clone(),
                    message: "missing compiled section".to_string(),
                }]
            })?;
            sections.insert(section.name.clone(), artifact);
        }
        artifacts.push(ObjectArtifact {
            object: obj.name.clone(),
            sections,
        });
    }

    Ok(artifacts)
}

pub fn compile_object<B: LowerBackend>(
    module: &Module,
    backend: &B,
    object: &str,
    opts: &CompileOptions<B::FixupPolicy>,
) -> Result<ObjectArtifact, Vec<ObjectCompileError>> {
    let _span = info_span!("sonatina.codegen.object.compile_object", object).entered();
    {
        let _span = debug_span!("sonatina.codegen.object.verify").entered();
        verify_module_for_codegen(module, &opts.verifier_cfg)?;
    }
    let program = {
        let _span = debug_span!("sonatina.codegen.object.resolve_program").entered();
        ResolvedProgram::resolve(module)?
    };

    let Some((object_idx, obj)) = program
        .objects
        .iter()
        .enumerate()
        .find(|(_, obj)| obj.name.0.as_str() == object)
    else {
        return Err(vec![ObjectCompileError::ObjectNotFound {
            object: object.to_string(),
        }]);
    };

    let object_id = ObjectId(object_idx as u32);
    let mut required: FxHashSet<SectionId> = FxHashSet::default();
    {
        let _span = debug_span!("sonatina.codegen.object.collect_embed_deps").entered();
        for (section_idx, _) in obj.sections.iter().enumerate() {
            let id = SectionId {
                object: object_id,
                section: section_idx as u32,
            };
            collect_embed_deps(&program, id, &mut required);
        }
    }

    let mut cache = {
        let _span = debug_span!(
            "sonatina.codegen.object.compile_required_sections",
            required_len = required.len()
        )
        .entered();
        compile_required_sections_into_cache(&program, backend, Some(&required), opts)?
    };

    let _span = debug_span!("sonatina.codegen.object.materialize_object").entered();
    let mut sections = IndexMap::new();
    for (section_idx, section) in obj.sections.iter().enumerate() {
        let id = SectionId {
            object: object_id,
            section: section_idx as u32,
        };
        let artifact = cache.remove(&id).ok_or_else(|| {
            vec![ObjectCompileError::LinkError {
                object: obj.name.clone(),
                section: section.name.clone(),
                message: "missing compiled section".to_string(),
            }]
        })?;
        sections.insert(section.name.clone(), artifact);
    }

    Ok(ObjectArtifact {
        object: obj.name.clone(),
        sections,
    })
}

fn compile_section<B: LowerBackend>(
    program: &ResolvedProgram<'_>,
    backend: &B,
    section_id: SectionId,
    cache: &mut FxHashMap<SectionId, super::artifact::SectionArtifact>,
    opts: &CompileOptions<B::FixupPolicy>,
) -> Result<(), Vec<ObjectCompileError>> {
    let _span = trace_span!(
        "sonatina.codegen.object.compile_section",
        section_object = section_id.object.0,
        section = section_id.section
    )
    .entered();
    if cache.contains_key(&section_id) {
        return Ok(());
    }

    let section = program.section(section_id);
    let (object_name, section_name) = program.section_name(section_id);

    let defined_embed_symbols: Vec<EmbedSymbol> =
        section.embeds.iter().map(|e| e.as_symbol.clone()).collect();
    let defined_embed_symbol_set: FxHashSet<EmbedSymbol> =
        defined_embed_symbols.iter().cloned().collect();

    let membership = {
        let _span = trace_span!("sonatina.codegen.object.build_membership").entered();
        build_membership(program, section_id)
    };
    for used in &membership.used_embed_symbols {
        if !defined_embed_symbol_set.contains(used) {
            return Err(vec![ObjectCompileError::UndefinedEmbedSymbol {
                object: object_name.clone(),
                section: section_name.clone(),
                symbol: used.clone(),
            }]);
        }
    }

    let section_ctx = SectionLoweringCtx {
        object: object_name,
        section: section_name,
        embed_symbols: &defined_embed_symbols,
    };

    let funcs = {
        let _span =
            trace_span!("sonatina.codegen.object.compute_function_emission_order").entered();
        compute_function_emission_order(program, section, &membership)
    };

    let mut data: Vec<(GlobalVariableRef, Vec<u8>)> = Vec::new();
    let mut gvs: Vec<GlobalVariableRef> = membership.globals.iter().copied().collect();
    gvs.sort_unstable();
    {
        let _span = trace_span!(
            "sonatina.codegen.object.encode_global_initializers",
            global_count = gvs.len()
        )
        .entered();
        for gv in gvs {
            let bytes = super::data::encode_gv_initializer_to_bytes(&program.module.ctx, gv)
                .map_err(|e| {
                    vec![ObjectCompileError::InvalidGlobalForData {
                        object: object_name.clone(),
                        section: section_name.clone(),
                        gv,
                        reason: format!("{e:?}"),
                    }]
                })?;
            data.push((gv, bytes));
        }
    }

    let mut embeds: Vec<(EmbedSymbol, Vec<u8>)> = Vec::new();
    {
        let _span = trace_span!(
            "sonatina.codegen.object.collect_embeds",
            embed_count = section.embeds.len()
        )
        .entered();
        for embed in &section.embeds {
            let source = cache.get(&embed.source).ok_or_else(|| {
                vec![ObjectCompileError::LinkError {
                    object: object_name.clone(),
                    section: section_name.clone(),
                    message: "missing embedded section artifact".to_string(),
                }]
            })?;
            embeds.push((embed.as_symbol.clone(), source.bytes.clone()));
        }
    }

    let artifact = {
        let _span = trace_span!(
            "sonatina.codegen.object.link_section",
            object = %object_name.0,
            section = %section_name.0
        )
        .entered();
        let backend_errors =
            reject_unsupported_evm_multi_return(program.module, &funcs, object_name, section_name);
        if !backend_errors.is_empty() {
            return Err(backend_errors);
        }
        link_section(
            program.module,
            backend,
            &funcs,
            &data,
            &embeds,
            &section_ctx,
            opts,
        )
        .map_err(|e| match e {
            LinkSectionError::Backend { func, error } => vec![ObjectCompileError::BackendError {
                object: object_name.clone(),
                section: section_name.clone(),
                func,
                message: error.to_string(),
            }],
            LinkSectionError::Link(message) => vec![ObjectCompileError::LinkError {
                object: object_name.clone(),
                section: section_name.clone(),
                message,
            }],
        })?
    };

    cache.insert(section_id, artifact);
    Ok(())
}

#[derive(Default)]
struct SectionMembership {
    funcs: FxHashSet<FuncRef>,
    globals: FxHashSet<GlobalVariableRef>,
    used_embed_symbols: FxHashSet<EmbedSymbol>,
}

fn build_membership(program: &ResolvedProgram<'_>, section_id: SectionId) -> SectionMembership {
    let module = program.module;
    let section = program.section(section_id);

    let mut membership = SectionMembership::default();
    membership.globals.extend(section.data.iter().copied());

    let mut worklist = Vec::new();
    let roots = std::iter::once(section.entry).chain(section.includes.iter().copied());
    for func in roots {
        if membership.funcs.insert(func) {
            worklist.push(func);
        }
    }

    while let Some(func_ref) = worklist.pop() {
        module.func_store.view(func_ref, |func| {
            let is = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        let callee = call.callee();
                        if membership.funcs.insert(callee) {
                            worklist.push(callee);
                        }
                    }

                    let inst = func.dfg.inst(inst_id);

                    if let Some(ptr) = <&GetFunctionPtr as InstDowncast>::downcast(is, inst) {
                        let func = *ptr.func();
                        if membership.funcs.insert(func) {
                            worklist.push(func);
                        }
                    }

                    if let Some(sym) = <&SymAddr as InstDowncast>::downcast(is, inst) {
                        record_symbol(sym.sym(), &mut membership, &mut worklist);
                    }
                    if let Some(sym) = <&SymSize as InstDowncast>::downcast(is, inst) {
                        record_symbol(sym.sym(), &mut membership, &mut worklist);
                    }
                }
            }
        });
    }

    membership
}

fn record_symbol(sym: &SymbolRef, membership: &mut SectionMembership, worklist: &mut Vec<FuncRef>) {
    match sym {
        SymbolRef::Func(func) => {
            if membership.funcs.insert(*func) {
                worklist.push(*func);
            }
        }
        SymbolRef::Global(gv) => {
            membership.globals.insert(*gv);
        }
        SymbolRef::Embed(sym) => {
            membership.used_embed_symbols.insert(sym.clone());
        }
        SymbolRef::CurrentSection => {}
    }
}

fn compute_function_emission_order(
    program: &ResolvedProgram<'_>,
    section: &super::resolve::ResolvedSection,
    membership: &SectionMembership,
) -> Vec<FuncRef> {
    let module = program.module;

    let mut include_priority: FxHashMap<FuncRef, usize> = FxHashMap::default();
    for (idx, func) in section.includes.iter().copied().enumerate() {
        include_priority.entry(func).or_insert(idx);
    }

    let mut func_names: FxHashMap<FuncRef, String> = FxHashMap::default();
    for func in membership.funcs.iter().copied() {
        let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
        func_names.insert(func, name);
    }

    let mut adjacency: FxHashMap<FuncRef, Vec<FuncRef>> = FxHashMap::default();
    for &func_ref in &membership.funcs {
        let mut callees: FxHashSet<FuncRef> = FxHashSet::default();
        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        let callee = call.callee();
                        if membership.funcs.contains(&callee) {
                            callees.insert(callee);
                        }
                    }
                }
            }
        });

        let mut callees: Vec<_> = callees.into_iter().collect();
        callees.sort_by(|a, b| compare_func(*a, *b, &include_priority, &func_names));
        adjacency.insert(func_ref, callees);
    }

    let mut visited: FxHashSet<FuncRef> = FxHashSet::default();
    let mut order = Vec::new();

    fn dfs(
        node: FuncRef,
        adjacency: &FxHashMap<FuncRef, Vec<FuncRef>>,
        visited: &mut FxHashSet<FuncRef>,
        out: &mut Vec<FuncRef>,
    ) {
        if !visited.insert(node) {
            return;
        }
        out.push(node);
        if let Some(callees) = adjacency.get(&node) {
            for &callee in callees {
                dfs(callee, adjacency, visited, out);
            }
        }
    }

    dfs(section.entry, &adjacency, &mut visited, &mut order);

    let mut extra_roots: Vec<FuncRef> = section.includes.to_vec();
    extra_roots.sort_by(|a, b| compare_func(*a, *b, &include_priority, &func_names));
    for root in extra_roots {
        dfs(root, &adjacency, &mut visited, &mut order);
    }

    let mut remaining: Vec<FuncRef> = membership
        .funcs
        .iter()
        .copied()
        .filter(|f| !visited.contains(f))
        .collect();
    remaining.sort_by(|a, b| compare_func(*a, *b, &include_priority, &func_names));
    for root in remaining {
        dfs(root, &adjacency, &mut visited, &mut order);
    }

    debug_assert_eq!(visited.len(), membership.funcs.len());
    order
}

fn compare_func(
    a: FuncRef,
    b: FuncRef,
    include_priority: &FxHashMap<FuncRef, usize>,
    func_names: &FxHashMap<FuncRef, String>,
) -> std::cmp::Ordering {
    let a_pri = include_priority.get(&a).copied().unwrap_or(usize::MAX);
    let b_pri = include_priority.get(&b).copied().unwrap_or(usize::MAX);
    let a_name = func_names.get(&a).unwrap();
    let b_name = func_names.get(&b).unwrap();

    (a_pri, a_name, a.as_u32()).cmp(&(b_pri, b_name, b.as_u32()))
}

fn collect_embed_deps(
    program: &ResolvedProgram<'_>,
    id: SectionId,
    out: &mut FxHashSet<SectionId>,
) {
    if !out.insert(id) {
        return;
    }
    for embed in &program.section(id).embeds {
        collect_embed_deps(program, embed.source, out);
    }
}

fn topo_sort_sections(program: &ResolvedProgram<'_>) -> Vec<SectionId> {
    let roots = program.all_sections();

    let mut visited: FxHashSet<SectionId> = FxHashSet::default();
    let mut order = Vec::new();

    fn dfs(
        program: &ResolvedProgram<'_>,
        node: SectionId,
        visited: &mut FxHashSet<SectionId>,
        order: &mut Vec<SectionId>,
    ) {
        if !visited.insert(node) {
            return;
        }

        for embed in &program.section(node).embeds {
            dfs(program, embed.source, visited, order);
        }
        order.push(node);
    }

    for root in roots {
        dfs(program, root, &mut visited, &mut order);
    }

    order
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::PushWidthPolicy,
        machinst::{
            lower::{FixupUpdate, LowerBackend, LoweredFunction, SectionLoweringCtx},
            vcode::{Label, SymFixup, SymFixupKind, VCode, VCodeFixup, VCodeInst},
        },
        object::{CompileOptions, FrontendProvenanceMap, OBSERVABILITY_SCHEMA_VERSION},
    };
    use cranelift_entity::EntityRef;
    use smallvec::SmallVec;
    use sonatina_ir::{
        InstDowncast, InstDowncastMut, Module,
        inst::{
            arith::Add,
            data::{SymAddr, SymSize},
        },
        module::FuncRef,
    };
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig};
    use std::sync::{Arc, Mutex};

    struct FakeBackend;

    impl LowerBackend for FakeBackend {
        type MInst = u8;
        type Error = String;
        type FixupPolicy = PushWidthPolicy;

        fn lower_function(
            &self,
            module: &Module,
            func: FuncRef,
            section_ctx: &SectionLoweringCtx<'_>,
        ) -> Result<LoweredFunction<Self::MInst>, Self::Error> {
            let _ = section_ctx;

            let mut vcode: VCode<Self::MInst> = VCode::default();
            let mut block_order = Vec::new();

            module.func_store.view(func, |function| {
                let is = function.inst_set();
                for block in function.layout.iter_block() {
                    let _ = &mut vcode.blocks[block];
                    block_order.push(block);

                    for inst_id in function.layout.iter_inst(block) {
                        let inst = function.dfg.inst(inst_id);

                        if let Some(sym) = <&SymAddr as InstDowncast>::downcast(is, inst) {
                            let insn = vcode.add_inst_to_block(0, Some(inst_id), block);
                            vcode.inst_imm_bytes.insert((insn, SmallVec::new()));
                            vcode.fixups.insert((
                                insn,
                                VCodeFixup::Sym(SymFixup {
                                    kind: SymFixupKind::Addr,
                                    sym: sym.sym().clone(),
                                }),
                            ));
                        }

                        if let Some(sym) = <&SymSize as InstDowncast>::downcast(is, inst) {
                            let insn = vcode.add_inst_to_block(0, Some(inst_id), block);
                            vcode.inst_imm_bytes.insert((insn, SmallVec::new()));
                            vcode.fixups.insert((
                                insn,
                                VCodeFixup::Sym(SymFixup {
                                    kind: SymFixupKind::Size,
                                    sym: sym.sym().clone(),
                                }),
                            ));
                        }
                    }
                }
            });

            Ok(LoweredFunction { vcode, block_order })
        }

        fn apply_sym_fixup(
            &self,
            vcode: &mut VCode<Self::MInst>,
            inst: VCodeInst,
            fixup: &SymFixup,
            value: u32,
            policy: &Self::FixupPolicy,
        ) -> Result<FixupUpdate, Self::Error> {
            let _ = fixup;
            let (_, bytes) = vcode
                .inst_imm_bytes
                .get_mut(inst)
                .ok_or_else(|| "missing fixup immediate bytes".to_string())?;

            let new_bytes: SmallVec<[u8; 4]> = match policy {
                PushWidthPolicy::Push4 => SmallVec::from_slice(&value.to_be_bytes()),
                PushWidthPolicy::MinimalRelax => {
                    if value == 0 {
                        SmallVec::new()
                    } else {
                        value
                            .to_be_bytes()
                            .into_iter()
                            .skip_while(|b| *b == 0)
                            .collect()
                    }
                }
            };

            if bytes.as_slice() == new_bytes.as_slice() {
                return Ok(FixupUpdate::Unchanged);
            }

            let layout_changed = bytes.len() != new_bytes.len();
            bytes.clear();
            bytes.extend_from_slice(&new_bytes);
            self.update_opcode_with_immediate_bytes(&mut vcode.insts[inst], bytes);

            Ok(if layout_changed {
                FixupUpdate::LayoutChanged
            } else {
                FixupUpdate::ContentChanged
            })
        }

        fn lower(
            &self,
            ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
            alloc: &mut dyn crate::stackalloc::Allocator,
            inst: sonatina_ir::InstId,
        ) {
            let _ = (ctx, alloc, inst);
            unreachable!("FakeBackend does not use machinst lowering")
        }

        fn enter_function(
            &self,
            ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
            alloc: &mut dyn crate::stackalloc::Allocator,
            function: &sonatina_ir::Function,
        ) {
            let _ = (ctx, alloc, function);
        }

        fn enter_block(
            &self,
            ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
            alloc: &mut dyn crate::stackalloc::Allocator,
            block: sonatina_ir::BlockId,
        ) {
            let _ = (ctx, alloc, block);
        }

        fn update_opcode_with_immediate_bytes(
            &self,
            opcode: &mut Self::MInst,
            bytes: &mut SmallVec<[u8; 8]>,
        ) {
            debug_assert!(bytes.len() <= 32);
            *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
        }

        fn update_opcode_with_label(
            &self,
            opcode: &mut Self::MInst,
            label_offset: u32,
        ) -> SmallVec<[u8; 4]> {
            let bytes = label_offset
                .to_be_bytes()
                .into_iter()
                .skip_while(|b| *b == 0)
                .collect::<SmallVec<_>>();
            debug_assert!(bytes.len() <= 32);
            *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
            bytes
        }

        fn emit_opcode(&self, opcode: &Self::MInst, buf: &mut Vec<u8>) {
            buf.push(*opcode);
        }

        fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
            buf.extend_from_slice(bytes);
        }

        fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
            buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
        }
    }

    #[test]
    fn compile_object_embeds_sections_and_patches_fixups() {
        let s = r#"
target = "evm-ethereum-london"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        return;
}

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        return;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: true,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let artifact = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();

        let runtime = artifact
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "runtime")
            .unwrap()
            .1
            .bytes
            .clone();
        assert_eq!(runtime.len(), 13);
        assert_eq!(runtime[0], 0x63);
        assert_eq!(&runtime[1..5], &10u32.to_be_bytes());
        assert_eq!(runtime[5], 0x63);
        assert_eq!(&runtime[6..10], &3u32.to_be_bytes());
        assert_eq!(&runtime[10..], &[1, 2, 3]);

        let init = artifact
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "init")
            .unwrap()
            .1
            .bytes
            .clone();
        assert_eq!(init.len(), 23);
        assert_eq!(init[0], 0x63);
        assert_eq!(&init[1..5], &10u32.to_be_bytes());
        assert_eq!(init[5], 0x63);
        assert_eq!(&init[6..10], &13u32.to_be_bytes());
        assert_eq!(&init[10..], runtime.as_slice());
    }

    #[test]
    fn compile_object_resolves_current_section_symbols() {
        let s = r#"
target = "evm-ethereum-london"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        return;
}

func public %init() {
    block0:
        v0.i256 = sym_addr .;
        v1.i256 = sym_size .;
        v2.i256 = sym_addr &runtime;
        v3.i256 = sym_size &runtime;
        return;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: true,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let artifact = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();

        let runtime = artifact
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "runtime")
            .unwrap()
            .1
            .bytes
            .clone();
        assert_eq!(runtime.len(), 13);

        let init = artifact
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "init")
            .unwrap()
            .1
            .bytes
            .clone();
        assert_eq!(init.len(), 33);
        assert_eq!(init[0], 0x63);
        assert_eq!(&init[1..5], &0u32.to_be_bytes());
        assert_eq!(init[5], 0x63);
        assert_eq!(&init[6..10], &33u32.to_be_bytes());
        assert_eq!(init[10], 0x63);
        assert_eq!(&init[11..15], &20u32.to_be_bytes());
        assert_eq!(init[15], 0x63);
        assert_eq!(&init[16..20], &13u32.to_be_bytes());
        assert_eq!(&init[20..], runtime.as_slice());
    }

    #[test]
    fn compile_object_emits_observability_when_enabled() {
        let s = r#"
target = "evm-ethereum-london"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        return;
}

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        return;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: true,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let artifact = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();

        let init = artifact.sections.get_index(0).expect("init section").1;
        let runtime = artifact.sections.get_index(1).expect("runtime section").1;
        let init_obs = init
            .observability
            .as_ref()
            .expect("init observability should be emitted");
        let runtime_obs = runtime
            .observability
            .as_ref()
            .expect("runtime observability should be emitted");

        assert_eq!(init_obs.schema_version, OBSERVABILITY_SCHEMA_VERSION);
        assert_eq!(runtime_obs.schema_version, OBSERVABILITY_SCHEMA_VERSION);

        assert_eq!(init_obs.section_bytes, init.bytes.len() as u32);
        assert_eq!(runtime_obs.section_bytes, runtime.bytes.len() as u32);

        assert_eq!(
            init_obs.mapped_code_bytes + init_obs.unmapped_code_bytes,
            init_obs.code_bytes
        );
        assert_eq!(
            runtime_obs.mapped_code_bytes + runtime_obs.unmapped_code_bytes,
            runtime_obs.code_bytes
        );
        assert_eq!(
            init_obs.unmapped_reason_coverage.total_bytes(),
            init_obs.unmapped_code_bytes
        );
        assert_eq!(
            runtime_obs.unmapped_reason_coverage.total_bytes(),
            runtime_obs.unmapped_code_bytes
        );

        let object_obs = artifact
            .observability()
            .expect("object observability should be available");
        assert_eq!(object_obs.schema_version, OBSERVABILITY_SCHEMA_VERSION);
        assert_eq!(
            object_obs.total_section_bytes,
            init.bytes.len() as u32 + runtime.bytes.len() as u32
        );
        assert!(object_obs.to_text().contains("section init"));
        assert!(
            object_obs
                .to_json()
                .contains("\"schema_version\":\"0.1.0\"")
        );
        assert!(
            artifact
                .observability_text()
                .expect("object text observability expected")
                .contains("object schema=0.1.0")
        );
        assert!(
            artifact
                .observability_json()
                .expect("object json observability expected")
                .contains("\"schema_version\":\"0.1.0\"")
        );

        let mut enriched = artifact
            .observability()
            .expect("object observability should be available");
        let target = enriched
            .sections
            .values()
            .flat_map(|section| section.pc_map.iter())
            .find_map(|entry| entry.ir_inst.map(|ir_inst| (entry.func, ir_inst)))
            .expect("expected at least one ir-backed pc-map entry");
        let mut map = FrontendProvenanceMap::default();
        map.insert(target, "mir_stmt:1".to_string());
        enriched.apply_frontend_provenance(&map);
        assert!(
            enriched
                .to_json()
                .contains("\"frontend_provenance\":\"mir_stmt:1\""),
            "frontend provenance must be serialized when provided"
        );
    }

    #[test]
    fn compile_object_omits_observability_when_disabled() {
        let s = r#"
target = "evm-ethereum-london"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        return;
}

object @Contract {
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let artifact = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();
        assert!(
            artifact
                .sections
                .values()
                .all(|section| section.observability.is_none()),
            "observability must be absent when disabled"
        );
        assert!(artifact.observability().is_none());
    }

    #[test]
    fn observability_serialization_is_deterministic_across_repeated_builds() {
        let s = r#"
target = "evm-ethereum-london"

global public const [i8; 3] $blob = [1, 2, 3];

func public %runtime() {
    block0:
        v0.i256 = sym_addr $blob;
        v1.i256 = sym_size $blob;
        return;
}

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        return;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
    data $blob;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: true,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let a = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();
        let b = compile_object(&parsed.module, &backend, "Contract", &opts).unwrap();

        let a_obs = a.observability().expect("observability expected");
        let b_obs = b.observability().expect("observability expected");

        assert_eq!(a_obs.to_text(), b_obs.to_text());
        assert_eq!(a_obs.to_json(), b_obs.to_json());
    }

    #[test]
    fn observability_rejects_invalid_ir_references() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        v0.i32 = add 1.i32 2.i32;
        return;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        struct InvalidIrRefBackend;

        impl LowerBackend for InvalidIrRefBackend {
            type MInst = u8;
            type Error = String;
            type FixupPolicy = PushWidthPolicy;

            fn lower_function(
                &self,
                module: &Module,
                func: FuncRef,
                section_ctx: &SectionLoweringCtx<'_>,
            ) -> Result<LoweredFunction<Self::MInst>, Self::Error> {
                let _ = section_ctx;
                let mut vcode: VCode<Self::MInst> = VCode::default();
                let mut block_order = Vec::new();

                module.func_store.view(func, |function| {
                    let block = function.layout.entry_block().expect("entry block");
                    let _ = &mut vcode.blocks[block];
                    block_order.push(block);
                    let invalid_inst = sonatina_ir::InstId::new(9_999_999);
                    let _ = vcode.add_inst_to_block(0x01, Some(invalid_inst), block);
                });

                Ok(LoweredFunction { vcode, block_order })
            }

            fn apply_sym_fixup(
                &self,
                vcode: &mut VCode<Self::MInst>,
                inst: VCodeInst,
                fixup: &SymFixup,
                value: u32,
                policy: &Self::FixupPolicy,
            ) -> Result<FixupUpdate, Self::Error> {
                let _ = (vcode, inst, fixup, value, policy);
                Err("unexpected sym fixup in InvalidIrRefBackend".to_string())
            }

            fn lower(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                inst: sonatina_ir::InstId,
            ) {
                let _ = (ctx, alloc, inst);
                unreachable!("InvalidIrRefBackend does not use machinst lowering")
            }

            fn enter_function(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                function: &sonatina_ir::Function,
            ) {
                let _ = (ctx, alloc, function);
            }

            fn enter_block(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                block: sonatina_ir::BlockId,
            ) {
                let _ = (ctx, alloc, block);
            }

            fn update_opcode_with_immediate_bytes(
                &self,
                opcode: &mut Self::MInst,
                bytes: &mut SmallVec<[u8; 8]>,
            ) {
                debug_assert!(bytes.len() <= 32);
                *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
            }

            fn update_opcode_with_label(
                &self,
                opcode: &mut Self::MInst,
                label_offset: u32,
            ) -> SmallVec<[u8; 4]> {
                let bytes = label_offset
                    .to_be_bytes()
                    .into_iter()
                    .skip_while(|b| *b == 0)
                    .collect::<SmallVec<_>>();
                debug_assert!(bytes.len() <= 32);
                *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
                bytes
            }

            fn emit_opcode(&self, opcode: &Self::MInst, buf: &mut Vec<u8>) {
                buf.push(*opcode);
            }

            fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
                buf.extend_from_slice(bytes);
            }

            fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
                buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
            }
        }

        let parsed = parse_module(s).unwrap();
        let backend = InvalidIrRefBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: true,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let errs =
            compile_object(&parsed.module, &backend, "O", &opts).expect_err("must reject bad ir");
        let [ObjectCompileError::LinkError { message, .. }] = errs.as_slice() else {
            panic!("expected a single link error, got {errs:?}");
        };
        assert!(
            message.contains("invalid ir reference"),
            "unexpected error message: {message}"
        );
    }

    #[test]
    fn compile_object_reports_verifier_failures_before_codegen() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        v0.i32 = add 1.i32 2.i32;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let errs = compile_object(&parsed.module, &backend, "O", &opts)
            .expect_err("invalid IR should fail verifier preflight");
        assert!(matches!(
            errs.as_slice(),
            [ObjectCompileError::VerifierFailed { .. }]
        ));
    }

    #[test]
    fn compile_object_fast_respects_custom_users_check() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        v0.i32 = add 1.i32 2.i32;
        return;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let module = parsed.module;
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let block = func.layout.entry_block().expect("entry block must exist");
            let inst = func
                .layout
                .first_inst_of(block)
                .expect("first instruction must exist");

            let replacement = func.dfg.make_imm_value(99i32);
            let inst_set = func.inst_set();
            let inst_data = func.dfg.inst_mut(inst);
            let add =
                <&mut Add as InstDowncastMut>::downcast_mut(inst_set, inst_data).expect("add");
            *add.lhs_mut() = replacement;
        });

        let backend = FakeBackend;
        let mut verifier_cfg = VerifierConfig::for_level(VerificationLevel::Fast);
        verifier_cfg.check_users = true;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg,
        };

        let errs = compile_object(&module, &backend, "O", &opts)
            .expect_err("fast preflight should run requested users check");
        let [ObjectCompileError::VerifierFailed { report }] = errs.as_slice() else {
            panic!("expected verifier failure, got {errs:?}");
        };
        assert!(
            report
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_str() == "IR0700"),
            "expected IR0700 users mismatch diagnostic, got {report}"
        );
    }

    #[test]
    fn compile_object_fast_rejects_bad_uaddo_result_shape() {
        let s = r#"
target = "evm-ethereum-london"

func public %main(v0.i32, v1.i32) -> i32 {
    block0:
        v2.i32 = uaddo v0 v1;
        return v2;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };

        let errs = compile_object(&parsed.module, &backend, "O", &opts)
            .expect_err("bad multi-result IR should fail verifier preflight");
        let [ObjectCompileError::VerifierFailed { report }] = errs.as_slice() else {
            panic!("expected verifier failure, got {errs:?}");
        };
        assert!(
            report
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_str() == "IR0601"),
            "expected IR0601, got {report}"
        );
    }

    #[test]
    fn compile_object_rejects_multi_return_functions_for_evm() {
        let s = r#"
target = "evm-ethereum-london"

func public %main(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        (v2.i32, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let errs = compile_object(&parsed.module, &backend, "O", &opts)
            .expect_err("must reject multi-return");
        assert!(
            errs.iter().any(|err| matches!(
                err,
                ObjectCompileError::BackendError { message, .. }
                    if message.contains("does not support functions with 2 return values")
            )),
            "expected multi-return backend error, got {errs:?}"
        );
    }

    #[test]
    fn compile_object_rejects_multi_return_calls_for_evm() {
        let s = r#"
target = "evm-ethereum-london"

declare external %pair_add(i32, i32) -> (i32, i1);

func public %main() {
    block0:
        (v0.i32, v1.i1) = call %pair_add 1.i32 2.i32;
        return;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let backend = FakeBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let errs = compile_object(&parsed.module, &backend, "O", &opts)
            .expect_err("must reject multi-return call");
        assert!(
            errs.iter().any(|err| matches!(
                err,
                ObjectCompileError::BackendError { message, .. }
                    if message.contains("call inst") && message.contains("2 results")
            )),
            "expected multi-return call backend error, got {errs:?}"
        );
    }

    #[test]
    fn observability_reason_buckets_account_for_unmapped_bytes() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        v0.i32 = add 1.i32 2.i32;
        return;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

        struct UnmappedObsBackend;

        impl LowerBackend for UnmappedObsBackend {
            type MInst = u8;
            type Error = String;
            type FixupPolicy = PushWidthPolicy;

            fn lower_function(
                &self,
                module: &Module,
                func: FuncRef,
                section_ctx: &SectionLoweringCtx<'_>,
            ) -> Result<LoweredFunction<Self::MInst>, Self::Error> {
                let _ = section_ctx;
                let mut vcode: VCode<Self::MInst> = VCode::default();
                let mut block_order = Vec::new();

                module.func_store.view(func, |function| {
                    let block = function.layout.entry_block().expect("entry block");
                    let mapped_ir = function
                        .layout
                        .iter_inst(block)
                        .next()
                        .expect("mapped ir inst");

                    let _ = &mut vcode.blocks[block];
                    block_order.push(block);

                    let _synthetic = vcode.add_inst_to_block(0x5b, None, block);
                    let mapped = vcode.add_inst_to_block(0x01, Some(mapped_ir), block);
                    let _mapped_again = vcode.add_inst_to_block(0x02, Some(mapped_ir), block);
                    let label_only = vcode.add_inst_to_block(0x60, None, block);
                    let label = vcode.labels.push(Label::Insn(mapped));
                    vcode.fixups.insert((label_only, VCodeFixup::Label(label)));
                    let _no_ir = vcode.add_inst_to_block(0xaa, None, block);
                });

                Ok(LoweredFunction { vcode, block_order })
            }

            fn apply_sym_fixup(
                &self,
                vcode: &mut VCode<Self::MInst>,
                inst: VCodeInst,
                fixup: &SymFixup,
                value: u32,
                policy: &Self::FixupPolicy,
            ) -> Result<FixupUpdate, Self::Error> {
                let _ = (vcode, inst, fixup, value, policy);
                Err("unexpected sym fixup in UnmappedObsBackend".to_string())
            }

            fn lower(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                inst: sonatina_ir::InstId,
            ) {
                let _ = (ctx, alloc, inst);
                unreachable!("UnmappedObsBackend does not use machinst lowering")
            }

            fn enter_function(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                function: &sonatina_ir::Function,
            ) {
                let _ = (ctx, alloc, function);
            }

            fn enter_block(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                block: sonatina_ir::BlockId,
            ) {
                let _ = (ctx, alloc, block);
            }

            fn update_opcode_with_immediate_bytes(
                &self,
                opcode: &mut Self::MInst,
                bytes: &mut SmallVec<[u8; 8]>,
            ) {
                debug_assert!(bytes.len() <= 32);
                *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
            }

            fn update_opcode_with_label(
                &self,
                opcode: &mut Self::MInst,
                label_offset: u32,
            ) -> SmallVec<[u8; 4]> {
                let bytes = label_offset
                    .to_be_bytes()
                    .into_iter()
                    .skip_while(|b| *b == 0)
                    .collect::<SmallVec<_>>();
                debug_assert!(bytes.len() <= 32);
                *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
                bytes
            }

            fn emit_opcode(&self, opcode: &Self::MInst, buf: &mut Vec<u8>) {
                buf.push(*opcode);
            }

            fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
                buf.extend_from_slice(bytes);
            }

            fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
                buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
            }
        }

        let parsed = parse_module(s).unwrap();
        let backend = UnmappedObsBackend;
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: true,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        let artifact = compile_object(&parsed.module, &backend, "O", &opts).unwrap();
        let runtime = artifact
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "runtime")
            .expect("runtime section")
            .1;
        let obs = runtime
            .observability
            .as_ref()
            .expect("runtime observability should be emitted");

        assert_eq!(obs.section_bytes, runtime.bytes.len() as u32);
        assert_eq!(obs.code_bytes, runtime.bytes.len() as u32);
        assert_eq!(
            obs.mapped_code_bytes + obs.unmapped_code_bytes,
            obs.code_bytes
        );
        assert_eq!(
            obs.unmapped_reason_coverage.total_bytes(),
            obs.unmapped_code_bytes
        );

        assert!(obs.mapped_code_bytes > 0);
        assert!(obs.unmapped_code_bytes > 0);
        assert!(obs.unmapped_reason_coverage.synthetic > 0);
        assert!(obs.unmapped_reason_coverage.label_or_fixup_only > 0);
        assert!(obs.unmapped_reason_coverage.no_ir_inst > 0);

        let mut ir_counts: std::collections::HashMap<sonatina_ir::InstId, usize> =
            std::collections::HashMap::new();
        for entry in &obs.pc_map {
            if let Some(ir_inst) = entry.ir_inst {
                *ir_counts.entry(ir_inst).or_default() += 1;
            }
        }
        assert!(
            ir_counts.values().any(|count| *count > 1),
            "expected at least one many-to-one mapping from vcode instructions to the same ir instruction"
        );

        for pair in obs.pc_map.windows(2) {
            assert!(pair[0].pc_end <= pair[1].pc_start);
        }
    }

    #[test]
    fn emits_functions_in_call_graph_dfs_order() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        call %b;
        call %c;
        return;
}

func public %b() {
    block0:
        return;
}

func public %c() {
    block0:
        return;
}

func public %d() {
    block0:
        call %e;
        return;
}

func public %e() {
    block0:
        return;
}

object @O {
  section runtime {
    entry %main;
    include %c;
    include %d;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let order: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));

        struct RecordingBackend {
            order: Arc<Mutex<Vec<String>>>,
        }

        impl LowerBackend for RecordingBackend {
            type MInst = u8;
            type Error = String;
            type FixupPolicy = PushWidthPolicy;

            fn lower_function(
                &self,
                module: &Module,
                func: FuncRef,
                section_ctx: &SectionLoweringCtx<'_>,
            ) -> Result<LoweredFunction<Self::MInst>, Self::Error> {
                let _ = section_ctx;
                let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
                self.order.lock().unwrap().push(name);
                Ok(LoweredFunction {
                    vcode: VCode::default(),
                    block_order: Vec::new(),
                })
            }

            fn apply_sym_fixup(
                &self,
                vcode: &mut VCode<Self::MInst>,
                inst: VCodeInst,
                fixup: &SymFixup,
                value: u32,
                policy: &Self::FixupPolicy,
            ) -> Result<FixupUpdate, Self::Error> {
                let _ = (vcode, inst, fixup, value, policy);
                Err("unexpected sym fixup in RecordingBackend".to_string())
            }

            fn lower(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                inst: sonatina_ir::InstId,
            ) {
                let _ = (ctx, alloc, inst);
                unreachable!("RecordingBackend does not use machinst lowering")
            }

            fn enter_function(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                function: &sonatina_ir::Function,
            ) {
                let _ = (ctx, alloc, function);
            }

            fn enter_block(
                &self,
                ctx: &mut crate::machinst::lower::Lower<Self::MInst>,
                alloc: &mut dyn crate::stackalloc::Allocator,
                block: sonatina_ir::BlockId,
            ) {
                let _ = (ctx, alloc, block);
            }

            fn update_opcode_with_immediate_bytes(
                &self,
                opcode: &mut Self::MInst,
                bytes: &mut SmallVec<[u8; 8]>,
            ) {
                debug_assert!(bytes.len() <= 32);
                *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
            }

            fn update_opcode_with_label(
                &self,
                opcode: &mut Self::MInst,
                label_offset: u32,
            ) -> SmallVec<[u8; 4]> {
                let bytes = label_offset
                    .to_be_bytes()
                    .into_iter()
                    .skip_while(|b| *b == 0)
                    .collect::<SmallVec<_>>();
                debug_assert!(bytes.len() <= 32);
                *opcode = 0x5f_u8.saturating_add(bytes.len() as u8);
                bytes
            }

            fn emit_opcode(&self, opcode: &Self::MInst, buf: &mut Vec<u8>) {
                buf.push(*opcode);
            }

            fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
                buf.extend_from_slice(bytes);
            }

            fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
                buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
            }
        }

        let backend = RecordingBackend {
            order: order.clone(),
        };
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::Push4,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Standard),
        };

        compile_object(&parsed.module, &backend, "O", &opts).unwrap();

        let got = order.lock().unwrap().clone();
        assert_eq!(got, vec!["main", "c", "b", "d", "e"]);
    }
}
