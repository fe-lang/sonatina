use crate::machinst::{
    assemble::ObjectLayout,
    lower::{FixupUpdate, LowerBackend, SectionLoweringCtx},
    vcode::{SymFixup, SymFixupKind, VCodeFixup, VCodeInst},
};
use cranelift_entity::EntityRef;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, GlobalVariableRef, Module, inst::data::SymbolRef, module::FuncRef, object::EmbedSymbol,
};

use super::{
    CompileOptions,
    artifact::{
        OBSERVABILITY_SCHEMA_VERSION, PcMapEntry, SectionArtifact, SectionObservability, SymbolDef,
        SymbolId, UnmappedReason, UnmappedReasonCoverage,
    },
};

#[derive(Debug)]
pub enum LinkSectionError<E> {
    Backend { func: FuncRef, error: E },
    Link(String),
}

struct BuildSectionObservabilityInput<'a, Op> {
    module: &'a Module,
    layout: &'a ObjectLayout<Op>,
    funcs: &'a [FuncRef],
    symtab: &'a FxHashMap<SymbolId, SymbolDef>,
    data: &'a [(GlobalVariableRef, Vec<u8>)],
    embeds: &'a [(EmbedSymbol, Vec<u8>)],
    section_ctx: &'a SectionLoweringCtx<'a>,
    section_bytes: u32,
}

pub fn link_section<B: LowerBackend>(
    module: &Module,
    backend: &B,
    funcs: &[FuncRef],
    data: &[(GlobalVariableRef, Vec<u8>)],
    embeds: &[(EmbedSymbol, Vec<u8>)],
    section_ctx: &SectionLoweringCtx<'_>,
    opts: &CompileOptions<B::FixupPolicy>,
) -> Result<SectionArtifact, LinkSectionError<B::Error>> {
    const MAX_ITERS: usize = 64;

    backend.prepare_section(module, funcs, section_ctx);

    let mut sym_fixups: Vec<(FuncRef, VCodeInst, SymFixup)> = Vec::new();
    let mut layout_funcs = Vec::with_capacity(funcs.len());

    for &func in funcs {
        let lowered = backend
            .lower_function(module, func, section_ctx)
            .map_err(|error| LinkSectionError::Backend { func, error })?;

        for (insn, fixup) in lowered.vcode.fixups.values() {
            let VCodeFixup::Sym(fixup) = fixup else {
                continue;
            };
            sym_fixups.push((func, *insn, fixup.clone()));
        }

        layout_funcs.push((func, lowered.vcode, lowered.block_order));
    }

    let mut layout = ObjectLayout::new(layout_funcs, 0);

    for _ in 0..MAX_ITERS {
        while layout.resize(backend, 0) {}

        let symtab =
            build_section_symtab(&layout, funcs, data, embeds).map_err(LinkSectionError::Link)?;

        let mut layout_changed = false;
        for (func, insn, fixup) in &sym_fixups {
            let value = fixup_value(&symtab, fixup).map_err(LinkSectionError::Link)?;

            let vcode = layout
                .func_vcode_mut(*func)
                .ok_or_else(|| LinkSectionError::Link("missing function vcode".to_string()))?;

            let update = backend
                .apply_sym_fixup(vcode, *insn, fixup, value, &opts.fixup_policy)
                .map_err(|error| LinkSectionError::Backend { func: *func, error })?;

            layout_changed |= update == FixupUpdate::LayoutChanged;
        }

        if !layout_changed {
            while layout.resize(backend, 0) {}

            let section_size: usize = symtab.values().map(|def| def.size as usize).sum();
            let mut bytes = Vec::with_capacity(section_size);
            layout.emit(backend, &mut bytes);
            for (_, blob) in data {
                bytes.extend_from_slice(blob);
            }
            for (_, blob) in embeds {
                bytes.extend_from_slice(blob);
            }

            let section_bytes: u32 = bytes
                .len()
                .try_into()
                .map_err(|_| LinkSectionError::Link("section size overflow".to_string()))?;

            let observability = if opts.emit_observability {
                Some(
                    build_section_observability(BuildSectionObservabilityInput {
                        module,
                        layout: &layout,
                        funcs,
                        symtab: &symtab,
                        data,
                        embeds,
                        section_ctx,
                        section_bytes,
                    })
                    .map_err(LinkSectionError::Link)?,
                )
            } else {
                None
            };

            return Ok(SectionArtifact {
                bytes,
                symtab: if opts.emit_symtab {
                    symtab
                } else {
                    FxHashMap::default()
                },
                observability,
            });
        }
    }

    Err(LinkSectionError::Link(
        "fixup relaxation did not converge".to_string(),
    ))
}

fn build_section_symtab<Op>(
    layout: &ObjectLayout<Op>,
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

fn fixup_value(symtab: &FxHashMap<SymbolId, SymbolDef>, fixup: &SymFixup) -> Result<u32, String> {
    let sym = symbol_id(&fixup.sym);
    let def = symtab
        .get(&sym)
        .ok_or_else(|| "unknown symbol".to_string())?;
    match fixup.kind {
        SymFixupKind::Addr => Ok(def.offset),
        SymFixupKind::Size => Ok(def.size),
    }
}

fn symbol_id(sym: &SymbolRef) -> SymbolId {
    match sym {
        SymbolRef::Func(func) => SymbolId::Func(*func),
        SymbolRef::Global(gv) => SymbolId::Global(*gv),
        SymbolRef::Embed(sym) => SymbolId::Embed(sym.clone()),
    }
}

fn build_section_observability<Op>(
    input: BuildSectionObservabilityInput<'_, Op>,
) -> Result<SectionObservability, String> {
    let BuildSectionObservabilityInput {
        module,
        layout,
        funcs,
        symtab,
        data,
        embeds,
        section_ctx,
        section_bytes,
    } = input;

    let mut code_bytes: u32 = 0;
    for &func in funcs {
        let def = symtab
            .get(&SymbolId::Func(func))
            .ok_or_else(|| format!("missing function symbol for {:?}", func))?;
        let end = def
            .offset
            .checked_add(def.size)
            .ok_or_else(|| "function bounds overflow".to_string())?;
        code_bytes = code_bytes.max(end);
    }

    let mut data_bytes = 0_u32;
    for (_, blob) in data {
        let sz: u32 = blob
            .len()
            .try_into()
            .map_err(|_| "data bytes overflow".to_string())?;
        data_bytes = data_bytes
            .checked_add(sz)
            .ok_or_else(|| "data bytes overflow".to_string())?;
    }

    let mut embed_bytes = 0_u32;
    for (_, blob) in embeds {
        let sz: u32 = blob
            .len()
            .try_into()
            .map_err(|_| "embed bytes overflow".to_string())?;
        embed_bytes = embed_bytes
            .checked_add(sz)
            .ok_or_else(|| "embed bytes overflow".to_string())?;
    }

    let expected_section_bytes = code_bytes
        .checked_add(data_bytes)
        .and_then(|n| n.checked_add(embed_bytes))
        .ok_or_else(|| "section byte accounting overflow".to_string())?;
    if expected_section_bytes != section_bytes {
        return Err(format!(
            "section byte mismatch: expected {expected_section_bytes}, got {section_bytes}",
        ));
    }

    let mut pc_map: Vec<PcMapEntry> = Vec::new();
    for &func in funcs {
        let func_layout = layout
            .func_layout(func)
            .ok_or_else(|| format!("missing func layout for {:?}", func))?;
        let func_def = symtab
            .get(&SymbolId::Func(func))
            .ok_or_else(|| format!("missing function symbol for {:?}", func))?;
        let func_name = module.ctx.func_sig(func, |sig| sig.name().to_string());
        let func_end = func_def
            .offset
            .checked_add(func_def.size)
            .ok_or_else(|| "function bounds overflow".to_string())?;

        let mut ordered: Vec<(VCodeInst, BlockId, bool)> = Vec::new();
        for &block in func_layout.block_order() {
            let mut is_head = true;
            for insn in func_layout.block_insns(block) {
                ordered.push((insn, block, is_head));
                is_head = false;
            }
        }

        for (idx, (insn, block, is_head)) in ordered.iter().copied().enumerate() {
            let pc_start = func_layout.insn_offset(insn);
            let pc_end = ordered
                .get(idx + 1)
                .map(|(next, _, _)| func_layout.insn_offset(*next))
                .unwrap_or(func_end);
            if pc_end < pc_start {
                return Err(format!(
                    "pc interval reversed for func {:?} insn {:?}: [{pc_start}, {pc_end})",
                    func, insn
                ));
            }

            let ir_inst = func_layout.vcode().inst_ir[insn].expand();
            if let Some(ir_inst) = ir_inst {
                let valid = module
                    .func_store
                    .view(func, |function| function.dfg.has_inst(ir_inst));
                if !valid {
                    return Err(format!(
                        "invalid ir reference for func {:?}: vcode {:?} -> ir {:?}",
                        func, insn, ir_inst
                    ));
                }
            }
            let unmapped_reason = if ir_inst.is_none() {
                Some(classify_unmapped_reason(func_layout, insn, is_head))
            } else {
                None
            };

            pc_map.push(PcMapEntry {
                pc_start,
                pc_end,
                func,
                func_name: func_name.clone(),
                block,
                vcode_inst: insn,
                ir_inst,
                frontend_provenance: None,
                unmapped_reason,
            });
        }
    }

    pc_map.sort_by_key(|e| {
        (
            e.pc_start,
            e.pc_end,
            e.func.index(),
            e.block.index(),
            e.vcode_inst.index(),
        )
    });

    let mut mapped_code_bytes = 0_u32;
    let mut unmapped_code_bytes = 0_u32;
    let mut unmapped_reason_coverage = UnmappedReasonCoverage::default();
    let mut cursor = 0_u32;
    let mut prev_end = 0_u32;

    for entry in &pc_map {
        if entry.pc_start < prev_end {
            return Err(format!(
                "overlapping pc intervals: previous end {prev_end}, next start {}",
                entry.pc_start
            ));
        }
        if entry.pc_end > code_bytes {
            return Err(format!(
                "pc interval out of bounds: [{}, {}) exceeds code bytes {code_bytes}",
                entry.pc_start, entry.pc_end
            ));
        }

        if entry.pc_start > cursor {
            let gap = entry.pc_start - cursor;
            unmapped_code_bytes = unmapped_code_bytes
                .checked_add(gap)
                .ok_or_else(|| "unmapped code bytes overflow".to_string())?;
            unmapped_reason_coverage.add_bytes(UnmappedReason::Unknown, gap);
            cursor = entry.pc_start;
        }

        let span = entry.pc_end - entry.pc_start;
        if entry.ir_inst.is_some() {
            mapped_code_bytes = mapped_code_bytes
                .checked_add(span)
                .ok_or_else(|| "mapped code bytes overflow".to_string())?;
        } else {
            let reason = entry.unmapped_reason.unwrap_or(UnmappedReason::Unknown);
            unmapped_code_bytes = unmapped_code_bytes
                .checked_add(span)
                .ok_or_else(|| "unmapped code bytes overflow".to_string())?;
            unmapped_reason_coverage.add_bytes(reason, span);
        }

        cursor = cursor.max(entry.pc_end);
        prev_end = entry.pc_end;
    }

    if cursor < code_bytes {
        let gap = code_bytes - cursor;
        unmapped_code_bytes = unmapped_code_bytes
            .checked_add(gap)
            .ok_or_else(|| "unmapped code bytes overflow".to_string())?;
        unmapped_reason_coverage.add_bytes(UnmappedReason::Unknown, gap);
    }

    if mapped_code_bytes
        .checked_add(unmapped_code_bytes)
        .ok_or_else(|| "coverage accounting overflow".to_string())?
        != code_bytes
    {
        return Err(format!(
            "coverage mismatch: mapped {mapped_code_bytes} + unmapped {unmapped_code_bytes} != code {code_bytes}",
        ));
    }

    if unmapped_reason_coverage.total_bytes() != unmapped_code_bytes {
        return Err(format!(
            "unmapped reason totals mismatch: reasons {} != unmapped {unmapped_code_bytes}",
            unmapped_reason_coverage.total_bytes(),
        ));
    }

    Ok(SectionObservability {
        schema_version: OBSERVABILITY_SCHEMA_VERSION,
        section: section_ctx.section.clone(),
        section_bytes,
        code_bytes,
        data_bytes,
        embed_bytes,
        mapped_code_bytes,
        unmapped_code_bytes,
        unmapped_reason_coverage,
        pc_map,
    })
}

fn classify_unmapped_reason<Op>(
    func_layout: &crate::machinst::assemble::FuncLayout<Op>,
    insn: VCodeInst,
    is_block_head: bool,
) -> UnmappedReason {
    if matches!(
        func_layout.vcode().fixups.get(insn),
        Some((_, VCodeFixup::Label(_)))
    ) {
        UnmappedReason::LabelOrFixupOnly
    } else if is_block_head {
        UnmappedReason::Synthetic
    } else {
        UnmappedReason::NoIrInst
    }
}
