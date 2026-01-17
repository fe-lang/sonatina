use crate::{
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    isa::evm::{EvmBackend, opcode::OpCode},
    liveness::Liveness,
    machinst::{
        assemble::ObjectLayout,
        lower::Lower,
        vcode::{SymFixupKind, VCode, VCodeFixup, VCodeInst},
    },
    stackalloc::StackifyAlloc,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Function, GlobalVariableRef, Module, cfg::ControlFlowGraph, inst::data::SymbolRef,
    module::FuncRef, object::EmbedSymbol,
};

use super::{
    EvmLoweringBackend, FixupKind, LoweredFunction, SectionArtifact, SectionLoweringCtx, SymbolDef,
    SymbolId,
};

pub struct EvmObjectBackend {
    backend: EvmBackend,
}

impl EvmObjectBackend {
    pub fn new(backend: EvmBackend) -> Self {
        Self { backend }
    }

    pub(crate) fn compile_section_minimal_relax(
        &self,
        module: &Module,
        funcs: &[FuncRef],
        data: &[(GlobalVariableRef, Vec<u8>)],
        embeds: &[(EmbedSymbol, Vec<u8>)],
        emit_symtab: bool,
    ) -> Result<SectionArtifact, String> {
        const MAX_ITERS: usize = 64;

        struct LoweredVCode {
            func: FuncRef,
            vcode: VCode<OpCode>,
            block_order: Vec<BlockId>,
            sym_fixups: Vec<(VCodeInst, FixupKind)>,
        }

        let mut lowered: Vec<LoweredVCode> = Vec::with_capacity(funcs.len());
        for &func in funcs {
            let lowered_fn =
                module
                    .func_store
                    .modify(func, |function| -> Result<LoweredVCode, String> {
                        let (vcode, block_order) =
                            lower_function_to_vcode(function, &module.ctx, &self.backend)?;
                        let sym_fixups = vcode
                            .fixups
                            .values()
                            .filter_map(|(insn, fixup)| {
                                let VCodeFixup::Sym(fixup) = fixup else {
                                    return None;
                                };
                                let sym = symbol_id(&fixup.sym);
                                let kind = match fixup.kind {
                                    SymFixupKind::Addr => FixupKind::SymAddr(sym),
                                    SymFixupKind::Size => FixupKind::SymSize(sym),
                                };
                                Some((*insn, kind))
                            })
                            .collect();
                        Ok(LoweredVCode {
                            func,
                            vcode,
                            block_order,
                            sym_fixups,
                        })
                    })?;
            lowered.push(lowered_fn);
        }

        let mut fixups: Vec<(FuncRef, VCodeInst, FixupKind)> = Vec::new();
        let layout_funcs: Vec<_> = lowered
            .into_iter()
            .map(|lowered| {
                fixups.extend(
                    lowered
                        .sym_fixups
                        .into_iter()
                        .map(|(insn, kind)| (lowered.func, insn, kind)),
                );
                (lowered.func, lowered.vcode, lowered.block_order)
            })
            .collect();

        let mut layout = ObjectLayout::new(layout_funcs, 0);

        for _ in 0..MAX_ITERS {
            while layout.resize(&self.backend, 0) {}

            let symtab = build_section_symtab(&layout, funcs, data, embeds)?;

            let mut changed = false;
            for (func, insn, kind) in &fixups {
                let value = fixup_value(&symtab, kind)?;
                let new_bytes = u32_to_evm_push_bytes(value);

                let vcode = layout
                    .func_vcode_mut(*func)
                    .ok_or_else(|| "missing function vcode".to_string())?;
                let (_, bytes) = vcode
                    .inst_imm_bytes
                    .get_mut(*insn)
                    .ok_or_else(|| "missing fixup immediate bytes".to_string())?;

                if bytes.as_slice() != new_bytes.as_slice() {
                    bytes.clear();
                    bytes.extend_from_slice(&new_bytes);
                    changed = true;
                }
            }

            if !changed {
                let section_size: usize = symtab.values().map(|def| def.size as usize).sum();
                let mut bytes = Vec::with_capacity(section_size);
                layout.emit(&self.backend, &mut bytes);
                for (_, blob) in data {
                    bytes.extend_from_slice(blob);
                }
                for (_, blob) in embeds {
                    bytes.extend_from_slice(blob);
                }

                return Ok(SectionArtifact {
                    bytes,
                    symtab: if emit_symtab {
                        symtab
                    } else {
                        FxHashMap::default()
                    },
                });
            }
        }

        Err("EVM fixup relaxation did not converge".to_string())
    }
}

impl EvmLoweringBackend for EvmObjectBackend {
    type Error = String;

    fn lower_function(
        &self,
        module: &Module,
        func: FuncRef,
        section_ctx: &SectionLoweringCtx<'_>,
    ) -> Result<LoweredFunction, Self::Error> {
        let func_name = module.ctx.func_sig(func, |sig| sig.name().to_string());
        Err(format!(
            "EvmObjectBackend does not support per-function lowering; compile a whole object section for relaxation (section={}::{}, func={func_name})",
            section_ctx.object.0.as_str(),
            section_ctx.section.0.as_str(),
        ))
    }

    fn compile_section(
        &self,
        module: &Module,
        funcs: &[FuncRef],
        data: &[(GlobalVariableRef, Vec<u8>)],
        embeds: &[(EmbedSymbol, Vec<u8>)],
        section_ctx: &SectionLoweringCtx<'_>,
        opts: &super::CompileOptions,
    ) -> Result<Option<SectionArtifact>, Self::Error> {
        self.compile_section_minimal_relax(module, funcs, data, embeds, opts.emit_symtab)
            .map(Some)
            .map_err(|e| {
                format!(
                    "EVM section compilation failed (section={}::{}): {e}",
                    section_ctx.object.0.as_str(),
                    section_ctx.section.0.as_str(),
                )
            })
    }
}

fn lower_function_to_vcode(
    function: &mut Function,
    module: &sonatina_ir::module::ModuleCtx,
    backend: &EvmBackend,
) -> Result<(VCode<OpCode>, Vec<BlockId>), String> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let mut splitter = CriticalEdgeSplitter::new();
    splitter.run(function, &mut cfg);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);

    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let alloc = StackifyAlloc::for_function(function, &cfg, &dom, &liveness, 16);
    let mut alloc = alloc;

    let lower = Lower::new(module, function);
    let vcode = lower
        .lower(backend, &mut alloc)
        .map_err(|e| format!("{e:?}"))?;
    let block_order = dom.rpo().to_owned();

    Ok((vcode, block_order))
}

fn build_section_symtab(
    layout: &ObjectLayout<OpCode>,
    funcs: &[FuncRef],
    data: &[(GlobalVariableRef, Vec<u8>)],
    embeds: &[(EmbedSymbol, Vec<u8>)],
) -> Result<FxHashMap<SymbolId, SymbolDef>, String> {
    let mut symtab: FxHashMap<SymbolId, SymbolDef> = FxHashMap::default();

    let mut code_end: u32 = 0;
    for &func in funcs {
        let offset = layout.func_offset(func);
        let size = layout
            .func_size(func)
            .ok_or_else(|| "missing function size".to_string())?;

        let end = offset
            .checked_add(size)
            .ok_or_else(|| "function offset overflow".to_string())?;
        code_end = code_end.max(end);
        symtab.insert(SymbolId::Func(func), SymbolDef { offset, size });
    }

    let mut cursor = code_end;
    for (gv, bytes) in data {
        let size: u32 = bytes
            .len()
            .try_into()
            .map_err(|_| "data size overflow".to_string())?;
        let offset = cursor;
        cursor = cursor
            .checked_add(size)
            .ok_or_else(|| "data offset overflow".to_string())?;
        symtab.insert(SymbolId::Global(*gv), SymbolDef { offset, size });
    }

    for (symbol, bytes) in embeds {
        let size: u32 = bytes
            .len()
            .try_into()
            .map_err(|_| "embed size overflow".to_string())?;
        let offset = cursor;
        cursor = cursor
            .checked_add(size)
            .ok_or_else(|| "embed offset overflow".to_string())?;
        symtab.insert(SymbolId::Embed(symbol.clone()), SymbolDef { offset, size });
    }

    Ok(symtab)
}

fn fixup_value(symtab: &FxHashMap<SymbolId, SymbolDef>, kind: &FixupKind) -> Result<u32, String> {
    match kind {
        FixupKind::SymAddr(sym) => Ok(symtab
            .get(sym)
            .ok_or_else(|| "unknown symbol".to_string())?
            .offset),
        FixupKind::SymSize(sym) => Ok(symtab
            .get(sym)
            .ok_or_else(|| "unknown symbol".to_string())?
            .size),
    }
}

fn u32_to_evm_push_bytes(value: u32) -> SmallVec<[u8; 4]> {
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

fn symbol_id(sym: &SymbolRef) -> SymbolId {
    match sym {
        SymbolRef::Func(func) => SymbolId::Func(*func),
        SymbolRef::Global(gv) => SymbolId::Global(*gv),
        SymbolRef::Embed(sym) => SymbolId::Embed(sym.clone()),
    }
}
