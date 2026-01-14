use crate::machinst::{
    assemble::ObjectLayout,
    lower::{FixupUpdate, LowerBackend, SectionLoweringCtx},
    vcode::{SymFixup, SymFixupKind, VCodeFixup, VCodeInst},
};
use rustc_hash::FxHashMap;
use sonatina_ir::{
    GlobalVariableRef, Module, inst::data::SymbolRef, module::FuncRef, object::EmbedSymbol,
};

use super::{
    CompileOptions,
    artifact::{SectionArtifact, SymbolDef, SymbolId},
};

#[derive(Debug)]
pub enum LinkSectionError<E> {
    Backend { func: FuncRef, error: E },
    Link(String),
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

            return Ok(SectionArtifact {
                bytes,
                symtab: if opts.emit_symtab {
                    symtab
                } else {
                    FxHashMap::default()
                },
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
