use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    GlobalVariableRef, InstDowncast, Module,
    inst::data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
    module::FuncRef,
    object::EmbedSymbol,
};

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
    let order = topo_sort_sections(program);

    let mut cache: FxHashMap<SectionId, super::artifact::SectionArtifact> = FxHashMap::default();
    for section_id in order {
        if required.is_none_or(|required| required.contains(&section_id)) {
            compile_section(program, backend, section_id, &mut cache, opts)?;
        }
    }

    Ok(cache)
}

pub fn compile_all_objects<B: LowerBackend>(
    module: &Module,
    backend: &B,
    opts: &CompileOptions<B::FixupPolicy>,
) -> Result<Vec<ObjectArtifact>, Vec<ObjectCompileError>> {
    let program = ResolvedProgram::resolve(module)?;
    let mut cache = compile_required_sections_into_cache(&program, backend, None, opts)?;

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
    let program = ResolvedProgram::resolve(module)?;

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
    for (section_idx, _) in obj.sections.iter().enumerate() {
        let id = SectionId {
            object: object_id,
            section: section_idx as u32,
        };
        collect_embed_deps(&program, id, &mut required);
    }

    let mut cache = compile_required_sections_into_cache(&program, backend, Some(&required), opts)?;

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
    if cache.contains_key(&section_id) {
        return Ok(());
    }

    let section = program.section(section_id);
    let (object_name, section_name) = program.section_name(section_id);

    let defined_embed_symbols: Vec<EmbedSymbol> =
        section.embeds.iter().map(|e| e.as_symbol.clone()).collect();
    let defined_embed_symbol_set: FxHashSet<EmbedSymbol> =
        defined_embed_symbols.iter().cloned().collect();

    let membership = build_membership(program, section_id);
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

    let funcs = compute_function_emission_order(program, section, &membership);

    let mut data: Vec<(GlobalVariableRef, Vec<u8>)> = Vec::new();
    let mut gvs: Vec<GlobalVariableRef> = membership.globals.iter().copied().collect();
    gvs.sort_unstable();
    for gv in gvs {
        let bytes =
            super::data::encode_gv_initializer_to_bytes(&program.module.ctx, gv).map_err(|e| {
                vec![ObjectCompileError::InvalidGlobalForData {
                    object: object_name.clone(),
                    section: section_name.clone(),
                    gv,
                    reason: format!("{e:?}"),
                }]
            })?;
        data.push((gv, bytes));
    }

    let mut embeds: Vec<(EmbedSymbol, Vec<u8>)> = Vec::new();
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

    let artifact = link_section(
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
    })?;

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
            vcode::{SymFixup, SymFixupKind, VCode, VCodeFixup, VCodeInst},
        },
        object::CompileOptions,
    };
    use smallvec::SmallVec;
    use sonatina_ir::{
        InstDowncast, Module,
        inst::data::{SymAddr, SymSize},
        module::FuncRef,
    };
    use sonatina_parser::parse_module;
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
        };

        compile_object(&parsed.module, &backend, "O", &opts).unwrap();

        let got = order.lock().unwrap().clone();
        assert_eq!(got, vec!["main", "c", "b", "d", "e"]);
    }
}
