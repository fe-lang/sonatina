use crate::{
    isa::evm::{EvmBackend, EvmPreparedSection, PushWidthPolicy, opcode::OpCode},
    machinst::{
        assemble::{CodeUnitOwner, ObjectLayout},
        lower::LoweredFunction,
        vcode::{SymFixup, SymFixupKind, VCodeFixup, VCodeInst},
    },
    transform::evm::CONST_WORD_POOL_PREFIX,
};
use cranelift_entity::EntityRef;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, GlobalVariableRef, Linkage, Module,
    inst::data::SymbolRef,
    module::FuncRef,
    object::{EmbedSymbol, SectionName},
};
use tracing::{debug_span, info_span, trace_span};

use super::{
    CompileOptions,
    artifact::{
        OBSERVABILITY_SCHEMA_VERSION, PcMapEntry, SectionArtifact, SectionObservability, SymbolDef,
        SymbolId, UnmappedReason, UnmappedReasonCoverage,
    },
};

#[derive(Debug)]
pub(crate) enum LinkSectionError {
    Backend { func: FuncRef, error: String },
    BackendFixup { owner: CodeUnitOwner, error: String },
    Link(String),
}

struct BuildSectionObservabilityInput<'a, Op> {
    module: &'a Module,
    layout: &'a ObjectLayout<Op>,
    funcs: &'a [FuncRef],
    symtab: &'a FxHashMap<SymbolId, SymbolDef>,
    data: &'a SectionDataPlan,
    embeds: &'a [(EmbedSymbol, Vec<u8>)],
    section: &'a SectionName,
    section_bytes: u32,
}

#[derive(Debug)]
struct SectionDataPlan {
    blobs: Vec<Vec<u8>>,
    mergeable_blobs: Vec<bool>,
    symbols: Vec<DataSymbolDef>,
}

#[derive(Debug)]
struct DataSymbolDef {
    gv: GlobalVariableRef,
    blob: usize,
    offset_in_blob: u32,
    size: u32,
}

impl SectionDataPlan {
    fn build(module: &Module, data: &[(GlobalVariableRef, Vec<u8>)]) -> Result<Self, String> {
        let mut plan = Self {
            blobs: Vec::new(),
            mergeable_blobs: Vec::new(),
            symbols: Vec::with_capacity(data.len()),
        };
        let mut mergeable = Vec::new();

        for (idx, (gv, bytes)) in data.iter().enumerate() {
            if is_mergeable_const_pool(module, *gv) {
                mergeable.push((idx, *gv, bytes));
            } else {
                plan.push_unique(*gv, bytes)?;
            }
        }

        mergeable.sort_by_key(|(idx, gv, bytes)| {
            (
                std::cmp::Reverse(bytes.len()),
                gv.as_u32(),
                u32::try_from(*idx).unwrap_or(u32::MAX),
            )
        });
        for (_, gv, bytes) in mergeable {
            plan.push_mergeable(gv, bytes)?;
        }

        Ok(plan)
    }

    fn push_unique(&mut self, gv: GlobalVariableRef, bytes: &[u8]) -> Result<(), String> {
        self.push_blob(gv, bytes, false)
    }

    fn push_blob(
        &mut self,
        gv: GlobalVariableRef,
        bytes: &[u8],
        mergeable: bool,
    ) -> Result<(), String> {
        let blob = self.blobs.len();
        self.blobs.push(bytes.to_vec());
        self.mergeable_blobs.push(mergeable);
        self.push_symbol(gv, blob, 0, bytes)
    }

    fn push_mergeable(&mut self, gv: GlobalVariableRef, bytes: &[u8]) -> Result<(), String> {
        if let Some((blob, offset_in_blob)) = self.find_word_subrange(bytes)? {
            return self.push_symbol(gv, blob, offset_in_blob, bytes);
        }

        if let Some((blob, offset_in_blob)) = self.append_word_overlap(bytes)? {
            return self.push_symbol(gv, blob, offset_in_blob, bytes);
        }

        self.push_blob(gv, bytes, true)
    }

    fn push_symbol(
        &mut self,
        gv: GlobalVariableRef,
        blob: usize,
        offset_in_blob: u32,
        bytes: &[u8],
    ) -> Result<(), String> {
        let size = bytes
            .len()
            .try_into()
            .map_err(|_| "data size overflow".to_string())?;
        self.symbols.push(DataSymbolDef {
            gv,
            blob,
            offset_in_blob,
            size,
        });
        Ok(())
    }

    fn find_word_subrange(&self, needle: &[u8]) -> Result<Option<(usize, u32)>, String> {
        for (blob_idx, blob) in self.blobs.iter().enumerate() {
            if !self.mergeable_blobs[blob_idx] {
                continue;
            }
            for offset in word_offsets(blob.len(), needle.len()) {
                if &blob[offset..offset + needle.len()] == needle {
                    return Ok(Some((blob_idx, checked_u32(offset)?)));
                }
            }
        }
        Ok(None)
    }

    fn append_word_overlap(&mut self, bytes: &[u8]) -> Result<Option<(usize, u32)>, String> {
        for blob_idx in 0..self.blobs.len() {
            if !self.mergeable_blobs[blob_idx] {
                continue;
            }
            let blob = &mut self.blobs[blob_idx];
            if let Some(overlap) = max_word_suffix_prefix_overlap(blob, bytes) {
                let offset = blob
                    .len()
                    .checked_sub(overlap)
                    .ok_or_else(|| "data overlap underflow".to_string())?;
                blob.extend_from_slice(&bytes[overlap..]);
                return Ok(Some((blob_idx, checked_u32(offset)?)));
            }
        }
        Ok(None)
    }

    fn physical_size(&self) -> Result<u32, String> {
        self.blobs.iter().try_fold(0u32, |total, blob| {
            total
                .checked_add(checked_u32(blob.len())?)
                .ok_or_else(|| "data bytes overflow".to_string())
        })
    }
}

const EVM_WORD_BYTES: usize = 32;

fn is_mergeable_const_pool(module: &Module, gv: GlobalVariableRef) -> bool {
    module.ctx.with_gv_store(|store| {
        let data = store.gv_data(gv);
        data.linkage == Linkage::Private && data.symbol.starts_with(CONST_WORD_POOL_PREFIX)
    })
}

fn word_offsets(blob_len: usize, needle_len: usize) -> impl Iterator<Item = usize> {
    let aligned = needle_len != 0
        && needle_len <= blob_len
        && needle_len.is_multiple_of(EVM_WORD_BYTES)
        && blob_len.is_multiple_of(EVM_WORD_BYTES);
    let end = if aligned {
        blob_len - needle_len + 1
    } else {
        0
    };
    (0..end).step_by(EVM_WORD_BYTES)
}

fn max_word_suffix_prefix_overlap(blob: &[u8], bytes: &[u8]) -> Option<usize> {
    if !blob.len().is_multiple_of(EVM_WORD_BYTES) || !bytes.len().is_multiple_of(EVM_WORD_BYTES) {
        return None;
    }

    let max_words = blob.len().min(bytes.len()) / EVM_WORD_BYTES;
    for words in (1..=max_words).rev() {
        let overlap = words * EVM_WORD_BYTES;
        if blob[blob.len() - overlap..] == bytes[..overlap] {
            return Some(overlap);
        }
    }
    None
}

fn checked_u32(value: usize) -> Result<u32, String> {
    value
        .try_into()
        .map_err(|_| "data offset overflow".to_string())
}

pub(crate) fn link_section(
    backend: &EvmBackend,
    prepared: &EvmPreparedSection,
    data: &[(GlobalVariableRef, Vec<u8>)],
    embeds: &[(EmbedSymbol, Vec<u8>)],
    section: &SectionName,
    opts: &CompileOptions,
) -> Result<SectionArtifact, LinkSectionError> {
    const MAX_ITERS: usize = 64;
    let module = prepared.module();
    let funcs = prepared.funcs();
    let data_plan = SectionDataPlan::build(module, data).map_err(LinkSectionError::Link)?;

    let _span = info_span!(
        "sonatina.codegen.link_section",
        funcs = funcs.len(),
        data_items = data.len(),
        embed_items = embeds.len()
    )
    .entered();

    let mut lowered_funcs: Vec<(FuncRef, LoweredFunction<OpCode>)> =
        Vec::with_capacity(funcs.len());

    for &func in funcs {
        let lowered = {
            let _span = trace_span!(
                "sonatina.codegen.link_section.lower_function",
                func_ref = func.as_u32()
            )
            .entered();
            backend
                .lower_function(prepared, func)
                .map_err(|error| LinkSectionError::Backend { func, error })?
        };

        lowered_funcs.push((func, lowered));
    }

    let section_units = backend
        .post_lower_section(prepared, &mut lowered_funcs)
        .map_err(|error| LinkSectionError::Backend {
            func: funcs[0],
            error,
        })?;
    let layout_func_refs = lowered_funcs
        .iter()
        .map(|(func, _)| *func)
        .collect::<Vec<_>>();

    let layout_funcs = lowered_funcs
        .into_iter()
        .map(|(func, lowered)| (func, lowered.vcode, lowered.block_order))
        .collect();

    let mut layout = ObjectLayout::new(layout_funcs, section_units, 0);

    for iter in 0..MAX_ITERS {
        let _span = debug_span!("sonatina.codegen.link_section.relaxation_iter", iter).entered();
        {
            let _span = trace_span!("sonatina.codegen.link_section.resize_layout").entered();
            while layout
                .resize(
                    &mut |opcode, label_offset| {
                        backend.update_opcode_with_label(opcode, label_offset)
                    },
                    &mut |opcode, bytes| backend.update_opcode_with_immediate_bytes(opcode, bytes),
                    0,
                )
                .map_err(|error| LinkSectionError::Link(error.to_string()))?
            {}
        }

        let (symtab, section_size) = {
            let _span = trace_span!("sonatina.codegen.link_section.build_symtab").entered();
            build_section_symtab(&layout, &layout_func_refs, &data_plan, embeds)
                .map_err(LinkSectionError::Link)?
        };

        let layout_changed =
            apply_layout_sym_fixups(backend, &mut layout, &symtab, &opts.fixup_policy)?;

        if !layout_changed {
            {
                let _span = trace_span!("sonatina.codegen.link_section.final_resize").entered();
                while layout
                    .resize(
                        &mut |opcode, label_offset| {
                            backend.update_opcode_with_label(opcode, label_offset)
                        },
                        &mut |opcode, bytes| {
                            backend.update_opcode_with_immediate_bytes(opcode, bytes)
                        },
                        0,
                    )
                    .map_err(|error| LinkSectionError::Link(error.to_string()))?
                {}
            }

            let bytes = {
                let _span = debug_span!(
                    "sonatina.codegen.link_section.emit_section_bytes",
                    section_size
                )
                .entered();
                let mut bytes = Vec::with_capacity(section_size as usize);
                layout.emit(
                    &mut |opcode, buf| backend.emit_opcode(opcode, buf),
                    &mut |imm, buf| backend.emit_immediate_bytes(imm, buf),
                    &mut |address, buf| backend.emit_label(address, buf),
                    &mut bytes,
                );
                for blob in &data_plan.blobs {
                    bytes.extend_from_slice(blob);
                }
                for (_, blob) in embeds {
                    bytes.extend_from_slice(blob);
                }
                bytes
            };

            let section_bytes: u32 = bytes
                .len()
                .try_into()
                .map_err(|_| LinkSectionError::Link("section size overflow".to_string()))?;

            let observability = if opts.emit_observability {
                Some({
                    let _span =
                        debug_span!("sonatina.codegen.link_section.build_observability").entered();
                    build_section_observability(BuildSectionObservabilityInput {
                        module,
                        layout: &layout,
                        funcs: &layout_func_refs,
                        symtab: &symtab,
                        data: &data_plan,
                        embeds,
                        section,
                        section_bytes,
                    })
                    .map_err(LinkSectionError::Link)?
                })
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

fn apply_layout_sym_fixups(
    backend: &EvmBackend,
    layout: &mut ObjectLayout<OpCode>,
    symtab: &FxHashMap<SymbolId, SymbolDef>,
    fixup_policy: &PushWidthPolicy,
) -> Result<bool, LinkSectionError> {
    layout.apply_sym_fixups(|owner, vcode, inst, fixup| {
        let _span = match owner {
            CodeUnitOwner::Function(func) => trace_span!(
                "sonatina.codegen.link_section.apply_fixup",
                func_ref = func.as_u32(),
                inst = inst.as_u32()
            )
            .entered(),
            CodeUnitOwner::SectionUnit(unit) => trace_span!(
                "sonatina.codegen.link_section.apply_fixup",
                section_unit = unit.0,
                inst = inst.as_u32()
            )
            .entered(),
        };
        let value = fixup_value(symtab, fixup).map_err(LinkSectionError::Link)?;
        backend
            .apply_sym_fixup(vcode, inst, fixup, value, fixup_policy)
            .map_err(|error| LinkSectionError::BackendFixup { owner, error })
    })
}

fn build_section_symtab<Op>(
    layout: &ObjectLayout<Op>,
    funcs: &[FuncRef],
    data: &SectionDataPlan,
    embeds: &[(EmbedSymbol, Vec<u8>)],
) -> Result<(FxHashMap<SymbolId, SymbolDef>, u32), String> {
    let mut symtab: FxHashMap<SymbolId, SymbolDef> = FxHashMap::default();
    for &func in funcs {
        let offset = layout.func_offset(func);
        let size = layout
            .func_size(func)
            .ok_or_else(|| "missing function size".to_string())?;

        symtab.insert(SymbolId::Func(func), SymbolDef { offset, size });
    }

    let data_start = layout.code_end();
    let mut blob_offsets = Vec::with_capacity(data.blobs.len());
    let mut cursor = data_start;
    for blob in &data.blobs {
        blob_offsets.push(cursor);
        cursor = cursor
            .checked_add(checked_u32(blob.len())?)
            .ok_or_else(|| "data offset overflow".to_string())?;
    }
    for symbol in &data.symbols {
        let blob_offset = *blob_offsets
            .get(symbol.blob)
            .ok_or_else(|| "data symbol references missing blob".to_string())?;
        let offset = blob_offset
            .checked_add(symbol.offset_in_blob)
            .ok_or_else(|| "data symbol offset overflow".to_string())?;
        symtab.insert(
            SymbolId::Global(symbol.gv),
            SymbolDef {
                offset,
                size: symbol.size,
            },
        );
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

    let section_size = cursor;
    symtab.insert(
        SymbolId::CurrentSection,
        SymbolDef {
            offset: 0,
            size: section_size,
        },
    );

    Ok((symtab, section_size))
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
        SymbolRef::CurrentSection => SymbolId::CurrentSection,
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
        section,
        section_bytes,
    } = input;

    let code_bytes = layout.code_end();

    let data_bytes = data.physical_size()?;

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

    let synthetic_func_base = funcs
        .iter()
        .map(|func| func.as_u32())
        .max()
        .map_or(0, |max| max.saturating_add(1));
    for (idx, (unit_id, unit)) in layout.section_units().iter().enumerate() {
        let func = FuncRef::from_u32(
            synthetic_func_base
                .checked_add(idx as u32)
                .expect("synthetic observability func ref overflow"),
        );
        let func_name = unit.name().to_string();
        let layout = unit.layout();
        let func_end = layout.end();

        let mut ordered: Vec<(VCodeInst, BlockId)> = Vec::new();
        for &block in layout.block_order() {
            for insn in layout.block_insns(block) {
                ordered.push((insn, block));
            }
        }

        for (index, (insn, block)) in ordered.iter().copied().enumerate() {
            let pc_start = layout.insn_offset(insn);
            let pc_end = ordered
                .get(index + 1)
                .map(|(next, _)| layout.insn_offset(*next))
                .unwrap_or(func_end);
            if pc_end < pc_start {
                return Err(format!(
                    "pc interval reversed for section unit {:?} insn {:?}: [{pc_start}, {pc_end})",
                    unit_id, insn
                ));
            }

            pc_map.push(PcMapEntry {
                pc_start,
                pc_end,
                func,
                func_name: func_name.clone(),
                block,
                vcode_inst: insn,
                ir_inst: None,
                frontend_provenance: None,
                unmapped_reason: Some(UnmappedReason::Synthetic),
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
        section: section.clone(),
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
        Some((_, VCodeFixup::Label(_) | VCodeFixup::Sym(_)))
    ) {
        UnmappedReason::LabelOrFixupOnly
    } else if is_block_head {
        UnmappedReason::Synthetic
    } else {
        UnmappedReason::NoIrInst
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::opcode::OpCode,
        machinst::{
            lower::SectionCodeUnit,
            vcode::{SectionCodeUnitId, VCode},
        },
    };
    use smallvec::smallvec;
    use sonatina_ir::{isa::evm::Evm, module::FuncRef};
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn test_backend() -> EvmBackend {
        EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }))
    }

    #[test]
    fn apply_sym_fixups_updates_section_unit_immediates() {
        let backend = test_backend();
        let func = FuncRef::from_u32(0);
        let gv = GlobalVariableRef::from_u32(0);
        let unit_id = SectionCodeUnitId(0);
        let block = BlockId(0);

        let mut func_vcode = VCode::<OpCode>::default();
        func_vcode.add_inst_to_block(OpCode::STOP, None, block);

        let mut unit_vcode = VCode::<OpCode>::default();
        let addr = unit_vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        unit_vcode.inst_imm_bytes.insert((addr, smallvec![]));
        unit_vcode.fixups.insert((
            addr,
            VCodeFixup::Sym(SymFixup {
                kind: SymFixupKind::Addr,
                sym: SymbolRef::Global(gv),
            }),
        ));
        let size = unit_vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        unit_vcode.inst_imm_bytes.insert((size, smallvec![]));
        unit_vcode.fixups.insert((
            size,
            VCodeFixup::Sym(SymFixup {
                kind: SymFixupKind::Size,
                sym: SymbolRef::Global(gv),
            }),
        ));
        unit_vcode.add_inst_to_block(OpCode::STOP, None, block);

        let mut layout = ObjectLayout::new(
            vec![(func, func_vcode, vec![block])],
            vec![SectionCodeUnit {
                id: unit_id,
                name: "__helper".to_string(),
                vcode: unit_vcode,
                block_order: vec![block],
            }],
            0,
        );
        let mut symtab = FxHashMap::default();
        symtab.insert(
            SymbolId::Global(gv),
            SymbolDef {
                offset: 0x1234_5678,
                size: 0x0102_0304,
            },
        );

        let layout_changed =
            apply_layout_sym_fixups(&backend, &mut layout, &symtab, &PushWidthPolicy::Push4)
                .expect("helper fixups should resolve");
        assert!(layout_changed, "PUSH0 should relax to wider PUSH");

        let unit = layout
            .section_units()
            .get(&unit_id)
            .expect("section unit layout should exist");
        let (addr_inst, addr_bytes) = unit
            .layout()
            .vcode()
            .inst_imm_bytes
            .get(addr)
            .expect("addr fixup bytes should exist");
        let (size_inst, size_bytes) = unit
            .layout()
            .vcode()
            .inst_imm_bytes
            .get(size)
            .expect("size fixup bytes should exist");

        assert_eq!(*addr_inst, addr);
        assert_eq!(addr_bytes.as_slice(), &[0x12, 0x34, 0x56, 0x78][..]);
        assert_eq!(unit.layout().vcode().insts[addr] as u8, OpCode::PUSH4 as u8);
        assert_eq!(*size_inst, size);
        assert_eq!(size_bytes.as_slice(), &[0x01, 0x02, 0x03, 0x04][..]);
        assert_eq!(unit.layout().vcode().insts[size] as u8, OpCode::PUSH4 as u8);
    }

    #[test]
    fn apply_sym_fixups_reports_section_unit_context() {
        let backend = test_backend();
        let func = FuncRef::from_u32(0);
        let gv = GlobalVariableRef::from_u32(0);
        let unit_id = SectionCodeUnitId(0);
        let block = BlockId(0);

        let mut func_vcode = VCode::<OpCode>::default();
        func_vcode.add_inst_to_block(OpCode::STOP, None, block);

        let mut unit_vcode = VCode::<OpCode>::default();
        let addr = unit_vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        unit_vcode.fixups.insert((
            addr,
            VCodeFixup::Sym(SymFixup {
                kind: SymFixupKind::Addr,
                sym: SymbolRef::Global(gv),
            }),
        ));

        let mut layout = ObjectLayout::new(
            vec![(func, func_vcode, vec![block])],
            vec![SectionCodeUnit {
                id: unit_id,
                name: "__helper".to_string(),
                vcode: unit_vcode,
                block_order: vec![block],
            }],
            0,
        );
        let mut symtab = FxHashMap::default();
        symtab.insert(
            SymbolId::Global(gv),
            SymbolDef {
                offset: 0x1234_5678,
                size: 0x0102_0304,
            },
        );

        let err = apply_layout_sym_fixups(&backend, &mut layout, &symtab, &PushWidthPolicy::Push4)
            .expect_err("missing section-unit fixup bytes must fail");
        assert!(matches!(
            err,
            LinkSectionError::BackendFixup {
                owner: CodeUnitOwner::SectionUnit(owner),
                error,
            } if owner == unit_id && error == "missing fixup immediate bytes"
        ));
    }
}
