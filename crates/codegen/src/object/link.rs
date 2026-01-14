use rustc_hash::FxHashMap;
use sonatina_ir::{GlobalVariableRef, module::FuncRef, object::EmbedSymbol};

use super::{
    PushWidthPolicy,
    artifact::{SectionArtifact, SymbolDef, SymbolId},
};

#[derive(Debug, Clone)]
pub enum Atom {
    Code {
        func: FuncRef,
        bytes: Vec<u8>,
        fixups: Vec<Fixup>,
    },
    Data {
        gv: GlobalVariableRef,
        bytes: Vec<u8>,
    },
    Embed {
        symbol: EmbedSymbol,
        bytes: Vec<u8>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixupKind {
    SymAddr(SymbolId),
    SymSize(SymbolId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixupFormat {
    EvmPush,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixup {
    pub kind: FixupKind,
    pub at: u32,
    pub width_hint: u8,
    pub format: FixupFormat,
}

pub fn link_section(
    atoms: &[Atom],
    push_width_policy: PushWidthPolicy,
    emit_symtab: bool,
) -> Result<SectionArtifact, String> {
    if push_width_policy == PushWidthPolicy::MinimalRelax {
        return link_section_with_relaxation(atoms, emit_symtab);
    }

    let mut symtab: FxHashMap<SymbolId, SymbolDef> = FxHashMap::default();
    let mut fixups: Vec<Fixup> = Vec::new();
    let mut bytes: Vec<u8> = Vec::new();

    for atom in atoms {
        let base = bytes.len() as u32;
        match atom {
            Atom::Code {
                func,
                bytes: atom_bytes,
                fixups: atom_fixups,
            } => {
                symtab.insert(
                    SymbolId::Func(*func),
                    SymbolDef {
                        offset: base,
                        size: atom_bytes.len() as u32,
                    },
                );

                for fixup in atom_fixups {
                    let mut fixup = fixup.clone();
                    fixup.at = fixup
                        .at
                        .checked_add(base)
                        .ok_or_else(|| "fixup offset overflow".to_string())?;
                    fixups.push(fixup);
                }

                bytes.extend_from_slice(atom_bytes);
            }

            Atom::Data {
                gv,
                bytes: atom_bytes,
            } => {
                symtab.insert(
                    SymbolId::Global(*gv),
                    SymbolDef {
                        offset: base,
                        size: atom_bytes.len() as u32,
                    },
                );
                bytes.extend_from_slice(atom_bytes);
            }

            Atom::Embed {
                symbol,
                bytes: atom_bytes,
            } => {
                symtab.insert(
                    SymbolId::Embed(symbol.clone()),
                    SymbolDef {
                        offset: base,
                        size: atom_bytes.len() as u32,
                    },
                );
                bytes.extend_from_slice(atom_bytes);
            }
        }
    }

    patch_fixups(&mut bytes, &symtab, &fixups, push_width_policy)?;

    Ok(SectionArtifact {
        bytes,
        symtab: if emit_symtab {
            symtab
        } else {
            FxHashMap::default()
        },
    })
}

#[derive(Debug, Clone)]
struct RelaxFixup {
    local_at: u32,
    width_hint: u8,
    kind: FixupKind,
    format: FixupFormat,
}

fn link_section_with_relaxation(
    atoms: &[Atom],
    emit_symtab: bool,
) -> Result<SectionArtifact, String> {
    const MAX_ITERS: usize = 32;

    let mut fixups: Vec<RelaxFixup> = Vec::new();
    let mut fixups_by_atom: Vec<Vec<usize>> = vec![Vec::new(); atoms.len()];

    for (atom_idx, atom) in atoms.iter().enumerate() {
        let Atom::Code {
            fixups: atom_fixups,
            ..
        } = atom
        else {
            continue;
        };

        for fixup in atom_fixups {
            let id = fixups.len();
            fixups.push(RelaxFixup {
                local_at: fixup.at,
                width_hint: fixup.width_hint,
                kind: fixup.kind.clone(),
                format: fixup.format,
            });
            fixups_by_atom[atom_idx].push(id);
        }
    }

    // Relaxation operates on a per-fixup width; start from lowering's width hint.
    let mut widths: Vec<u8> = fixups.iter().map(|f| f.width_hint).collect();

    for _ in 0..MAX_ITERS {
        let mut symtab: FxHashMap<SymbolId, SymbolDef> = FxHashMap::default();
        let mut bytes: Vec<u8> = Vec::new();
        let mut abs_at: Vec<u32> = vec![0; fixups.len()];

        for (atom_idx, atom) in atoms.iter().enumerate() {
            let base = bytes.len() as u32;
            match atom {
                Atom::Code {
                    func,
                    bytes: atom_bytes,
                    ..
                } => {
                    let mut atom_fixups = fixups_by_atom[atom_idx].clone();
                    atom_fixups.sort_by_key(|id| fixups[*id].local_at);

                    let mut out = Vec::new();
                    let mut cursor = 0usize;
                    for id in atom_fixups {
                        let fixup = &fixups[id];
                        let at = fixup.local_at as usize;
                        if at < cursor {
                            return Err("overlapping fixups".to_string());
                        }
                        out.extend_from_slice(&atom_bytes[cursor..at]);

                        let out_at = out.len() as u32;
                        abs_at[id] = base
                            .checked_add(out_at)
                            .ok_or_else(|| "fixup offset overflow".to_string())?;

                        if fixup.format != FixupFormat::EvmPush {
                            return Err("unsupported fixup format for relaxation".to_string());
                        }

                        // Replace the original PUSH{width_hint} placeholder with a PUSH{width}
                        // placeholder. We patch the opcode + immediate bytes after convergence.
                        out.push(0);

                        let orig_width = fixup.width_hint as usize;
                        let end = at
                            .checked_add(1)
                            .and_then(|v| v.checked_add(orig_width))
                            .ok_or_else(|| "fixup offset overflow".to_string())?;
                        if end > atom_bytes.len() {
                            return Err("fixup out of bounds".to_string());
                        }
                        cursor = end;

                        let width = widths[id] as usize;
                        out.extend(std::iter::repeat_n(0u8, width));
                    }

                    out.extend_from_slice(&atom_bytes[cursor..]);

                    symtab.insert(
                        SymbolId::Func(*func),
                        SymbolDef {
                            offset: base,
                            size: out.len() as u32,
                        },
                    );
                    bytes.extend_from_slice(&out);
                }

                Atom::Data {
                    gv,
                    bytes: atom_bytes,
                } => {
                    symtab.insert(
                        SymbolId::Global(*gv),
                        SymbolDef {
                            offset: base,
                            size: atom_bytes.len() as u32,
                        },
                    );
                    bytes.extend_from_slice(atom_bytes);
                }

                Atom::Embed {
                    symbol,
                    bytes: atom_bytes,
                } => {
                    symtab.insert(
                        SymbolId::Embed(symbol.clone()),
                        SymbolDef {
                            offset: base,
                            size: atom_bytes.len() as u32,
                        },
                    );
                    bytes.extend_from_slice(atom_bytes);
                }
            }
        }

        let mut changed = false;
        for (idx, fixup) in fixups.iter().enumerate() {
            let value = fixup_value(&symtab, &fixup.kind)?;
            let required = required_push_width(value);
            if widths[idx] != required {
                widths[idx] = required;
                changed = true;
            }
        }

        if !changed {
            for (idx, fixup) in fixups.iter().enumerate() {
                let value = fixup_value(&symtab, &fixup.kind)?;
                let width = widths[idx] as usize;
                let at = abs_at[idx] as usize;
                let end = at
                    .checked_add(1)
                    .and_then(|v| v.checked_add(width))
                    .ok_or_else(|| "fixup offset overflow".to_string())?;
                if end > bytes.len() {
                    return Err("fixup out of bounds".to_string());
                }

                bytes[at] = push_opcode(width)?;
                write_u32_be(&mut bytes[at + 1..end], value);
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

    Err("fixup relaxation did not converge".to_string())
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

fn required_push_width(value: u32) -> u8 {
    if value == 0 {
        return 0;
    }
    let bits = 32u32.saturating_sub(value.leading_zeros());
    bits.div_ceil(8) as u8
}

fn patch_fixups(
    bytes: &mut [u8],
    symtab: &FxHashMap<SymbolId, SymbolDef>,
    fixups: &[Fixup],
    push_width_policy: PushWidthPolicy,
) -> Result<(), String> {
    for fixup in fixups {
        let (sym, value) = match &fixup.kind {
            FixupKind::SymAddr(sym) => (
                sym,
                symtab
                    .get(sym)
                    .ok_or_else(|| "unknown symbol".to_string())?
                    .offset,
            ),
            FixupKind::SymSize(sym) => (
                sym,
                symtab
                    .get(sym)
                    .ok_or_else(|| "unknown symbol".to_string())?
                    .size,
            ),
        };

        let width = match push_width_policy {
            PushWidthPolicy::Push4 => {
                if fixup.width_hint != 4 {
                    return Err(format!(
                        "Push4 policy requires width_hint=4 (got {}) for {sym:?}",
                        fixup.width_hint
                    ));
                }
                4usize
            }
            PushWidthPolicy::MinimalRelax => {
                return Err(
                    "PushWidthPolicy::MinimalRelax must be handled before patch_fixups".to_string(),
                );
            }
        };

        match fixup.format {
            FixupFormat::EvmPush => {
                let at = fixup.at as usize;
                let end = at
                    .checked_add(1)
                    .and_then(|v| v.checked_add(width))
                    .ok_or_else(|| "fixup offset overflow".to_string())?;
                if end > bytes.len() {
                    return Err("fixup out of bounds".to_string());
                }

                bytes[at] = push_opcode(width)?;
                write_u32_be(&mut bytes[at + 1..end], value);
            }
        }
    }

    Ok(())
}

fn push_opcode(width: usize) -> Result<u8, String> {
    if !(0..=32).contains(&width) {
        return Err("invalid PUSH width".to_string());
    }
    0x5f_u8
        .checked_add(width as u8)
        .ok_or_else(|| "invalid PUSH opcode".to_string())
}

fn write_u32_be(dst: &mut [u8], value: u32) {
    dst.fill(0);
    let v = value.to_be_bytes();
    let dst_len = dst.len();
    let v_len = v.len();
    let len = dst_len.min(v_len);
    let dst_start = dst_len - len;
    let v_start = v_len - len;
    dst[dst_start..].copy_from_slice(&v[v_start..]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::module::FuncRef;

    #[test]
    fn patches_sym_addr_and_sym_size_fixups() {
        let func = FuncRef::from_u32(0);
        let embed = EmbedSymbol("runtime".into());

        let code_bytes = vec![0u8; 10];
        let fixups = vec![
            Fixup {
                kind: FixupKind::SymAddr(SymbolId::Embed(embed.clone())),
                at: 0,
                width_hint: 4,
                format: FixupFormat::EvmPush,
            },
            Fixup {
                kind: FixupKind::SymSize(SymbolId::Embed(embed.clone())),
                at: 5,
                width_hint: 4,
                format: FixupFormat::EvmPush,
            },
        ];

        let atoms = vec![
            Atom::Code {
                func,
                bytes: code_bytes,
                fixups,
            },
            Atom::Embed {
                symbol: embed,
                bytes: vec![0xaa, 0xbb, 0xcc],
            },
        ];

        let artifact = link_section(&atoms, PushWidthPolicy::Push4, true).unwrap();
        assert_eq!(artifact.bytes.len(), 13);
        assert_eq!(&artifact.bytes[10..], &[0xaa, 0xbb, 0xcc]);

        assert_eq!(artifact.bytes[0], 0x63);
        assert_eq!(&artifact.bytes[1..5], &10u32.to_be_bytes());

        assert_eq!(artifact.bytes[5], 0x63);
        assert_eq!(&artifact.bytes[6..10], &3u32.to_be_bytes());
    }

    #[test]
    fn minimal_relax_shrinks_push_widths() {
        let func = FuncRef::from_u32(0);
        let embed = EmbedSymbol("runtime".into());

        let code_bytes = vec![0u8; 10];
        let fixups = vec![
            Fixup {
                kind: FixupKind::SymAddr(SymbolId::Embed(embed.clone())),
                at: 0,
                width_hint: 4,
                format: FixupFormat::EvmPush,
            },
            Fixup {
                kind: FixupKind::SymSize(SymbolId::Embed(embed.clone())),
                at: 5,
                width_hint: 4,
                format: FixupFormat::EvmPush,
            },
        ];

        let atoms = vec![
            Atom::Code {
                func,
                bytes: code_bytes,
                fixups,
            },
            Atom::Embed {
                symbol: embed,
                bytes: vec![0xaa, 0xbb, 0xcc],
            },
        ];

        let artifact = link_section(&atoms, PushWidthPolicy::MinimalRelax, true).unwrap();
        assert_eq!(artifact.bytes.len(), 7);
        assert_eq!(&artifact.bytes[4..], &[0xaa, 0xbb, 0xcc]);

        assert_eq!(artifact.bytes[0], 0x60); // PUSH1
        assert_eq!(artifact.bytes[1], 4);
        assert_eq!(artifact.bytes[2], 0x60); // PUSH1
        assert_eq!(artifact.bytes[3], 3);
    }
}
