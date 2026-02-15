use crate::machinst::vcode::VCodeInst;
use cranelift_entity::EntityRef;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, GlobalVariableRef, InstId,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName},
};
use std::fmt::Write as _;

pub const OBSERVABILITY_SCHEMA_VERSION: &str = "0.1.0";

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolId {
    Func(FuncRef),
    Global(GlobalVariableRef),
    Embed(EmbedSymbol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolDef {
    pub offset: u32,
    pub size: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnmappedReason {
    NoIrInst,
    LabelOrFixupOnly,
    Synthetic,
    Unknown,
}

impl UnmappedReason {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::NoIrInst => "no_ir_inst",
            Self::LabelOrFixupOnly => "label_or_fixup_only",
            Self::Synthetic => "synthetic",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct UnmappedReasonCoverage {
    pub no_ir_inst: u32,
    pub label_or_fixup_only: u32,
    pub synthetic: u32,
    pub unknown: u32,
}

impl UnmappedReasonCoverage {
    pub fn add_bytes(&mut self, reason: UnmappedReason, bytes: u32) {
        match reason {
            UnmappedReason::NoIrInst => {
                self.no_ir_inst = self.no_ir_inst.saturating_add(bytes);
            }
            UnmappedReason::LabelOrFixupOnly => {
                self.label_or_fixup_only = self.label_or_fixup_only.saturating_add(bytes);
            }
            UnmappedReason::Synthetic => {
                self.synthetic = self.synthetic.saturating_add(bytes);
            }
            UnmappedReason::Unknown => {
                self.unknown = self.unknown.saturating_add(bytes);
            }
        }
    }

    pub fn total_bytes(self) -> u32 {
        self.no_ir_inst
            .saturating_add(self.label_or_fixup_only)
            .saturating_add(self.synthetic)
            .saturating_add(self.unknown)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PcMapEntry {
    pub pc_start: u32,
    pub pc_end: u32,
    pub func: FuncRef,
    pub block: BlockId,
    pub vcode_inst: VCodeInst,
    pub ir_inst: Option<InstId>,
    pub unmapped_reason: Option<UnmappedReason>,
}

#[derive(Debug, Clone)]
pub struct SectionObservability {
    pub schema_version: &'static str,
    pub section: SectionName,
    pub section_bytes: u32,
    pub code_bytes: u32,
    pub data_bytes: u32,
    pub embed_bytes: u32,
    pub mapped_code_bytes: u32,
    pub unmapped_code_bytes: u32,
    pub unmapped_reason_coverage: UnmappedReasonCoverage,
    pub pc_map: Vec<PcMapEntry>,
}

impl SectionObservability {
    pub fn to_text(&self) -> String {
        let mut out = String::new();
        writeln!(
            &mut out,
            "section {} schema={}",
            self.section.0, self.schema_version
        )
        .expect("in-memory write should not fail");
        writeln!(
            &mut out,
            "bytes total={} code={} data={} embed={}",
            self.section_bytes, self.code_bytes, self.data_bytes, self.embed_bytes
        )
        .expect("in-memory write should not fail");
        writeln!(
            &mut out,
            "coverage mapped={} unmapped={}",
            self.mapped_code_bytes, self.unmapped_code_bytes
        )
        .expect("in-memory write should not fail");
        writeln!(
            &mut out,
            "unmapped no_ir_inst={} label_or_fixup_only={} synthetic={} unknown={}",
            self.unmapped_reason_coverage.no_ir_inst,
            self.unmapped_reason_coverage.label_or_fixup_only,
            self.unmapped_reason_coverage.synthetic,
            self.unmapped_reason_coverage.unknown,
        )
        .expect("in-memory write should not fail");

        let mut entries = self.pc_map.clone();
        entries.sort_by_key(|e| {
            (
                e.pc_start,
                e.pc_end,
                e.func.index(),
                e.block.index(),
                e.vcode_inst.index(),
            )
        });
        for entry in entries {
            let reason = entry
                .unmapped_reason
                .map(UnmappedReason::as_str)
                .unwrap_or("-");
            let ir = entry
                .ir_inst
                .map(|ir| ir.0.to_string())
                .unwrap_or("-".into());
            writeln!(
                &mut out,
                "pc [{}, {}) func={} block={} vcode={} ir={} reason={}",
                entry.pc_start,
                entry.pc_end,
                entry.func.index(),
                entry.block.index(),
                entry.vcode_inst.index(),
                ir,
                reason
            )
            .expect("in-memory write should not fail");
        }

        out
    }

    pub fn to_json(&self) -> String {
        let mut out = String::new();
        write!(&mut out, "{{").expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"schema_version\":\"{}\",",
            json_escape(self.schema_version)
        )
        .expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"section\":\"{}\",",
            json_escape(&self.section.0)
        )
        .expect("in-memory write should not fail");
        write!(&mut out, "\"section_bytes\":{},", self.section_bytes)
            .expect("in-memory write should not fail");
        write!(&mut out, "\"code_bytes\":{},", self.code_bytes)
            .expect("in-memory write should not fail");
        write!(&mut out, "\"data_bytes\":{},", self.data_bytes)
            .expect("in-memory write should not fail");
        write!(&mut out, "\"embed_bytes\":{},", self.embed_bytes)
            .expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"mapped_code_bytes\":{},",
            self.mapped_code_bytes
        )
        .expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"unmapped_code_bytes\":{},",
            self.unmapped_code_bytes
        )
        .expect("in-memory write should not fail");

        write!(&mut out, "\"unmapped_reason_coverage\":{{")
            .expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"no_ir_inst\":{},\"label_or_fixup_only\":{},\"synthetic\":{},\"unknown\":{}",
            self.unmapped_reason_coverage.no_ir_inst,
            self.unmapped_reason_coverage.label_or_fixup_only,
            self.unmapped_reason_coverage.synthetic,
            self.unmapped_reason_coverage.unknown
        )
        .expect("in-memory write should not fail");
        write!(&mut out, "}},").expect("in-memory write should not fail");

        write!(&mut out, "\"pc_map\":[").expect("in-memory write should not fail");
        let mut entries = self.pc_map.clone();
        entries.sort_by_key(|e| {
            (
                e.pc_start,
                e.pc_end,
                e.func.index(),
                e.block.index(),
                e.vcode_inst.index(),
            )
        });
        for (idx, entry) in entries.iter().enumerate() {
            if idx > 0 {
                write!(&mut out, ",").expect("in-memory write should not fail");
            }
            write!(&mut out, "{{").expect("in-memory write should not fail");
            write!(
                &mut out,
                "\"pc_start\":{},\"pc_end\":{},\"func\":{},\"block\":{},\"vcode_inst\":{}",
                entry.pc_start,
                entry.pc_end,
                entry.func.index(),
                entry.block.index(),
                entry.vcode_inst.index()
            )
            .expect("in-memory write should not fail");

            if let Some(ir_inst) = entry.ir_inst {
                write!(&mut out, ",\"ir_inst\":{}", ir_inst.0)
                    .expect("in-memory write should not fail");
            } else {
                write!(&mut out, ",\"ir_inst\":null").expect("in-memory write should not fail");
            }

            if let Some(reason) = entry.unmapped_reason {
                write!(&mut out, ",\"reason\":\"{}\"", reason.as_str())
                    .expect("in-memory write should not fail");
            } else {
                write!(&mut out, ",\"reason\":null").expect("in-memory write should not fail");
            }

            write!(&mut out, "}}").expect("in-memory write should not fail");
        }
        write!(&mut out, "]").expect("in-memory write should not fail");
        write!(&mut out, "}}").expect("in-memory write should not fail");
        out
    }
}

#[derive(Debug, Clone)]
pub struct ObjectObservability {
    pub schema_version: &'static str,
    pub sections: IndexMap<SectionName, SectionObservability>,
    pub total_section_bytes: u32,
    pub total_code_bytes: u32,
    pub total_data_bytes: u32,
    pub total_embed_bytes: u32,
    pub total_mapped_code_bytes: u32,
    pub total_unmapped_code_bytes: u32,
}

impl ObjectObservability {
    pub fn to_text(&self) -> String {
        let mut out = String::new();
        writeln!(&mut out, "object schema={}", self.schema_version)
            .expect("in-memory write should not fail");
        writeln!(
            &mut out,
            "totals section_bytes={} code={} data={} embed={} mapped={} unmapped={}",
            self.total_section_bytes,
            self.total_code_bytes,
            self.total_data_bytes,
            self.total_embed_bytes,
            self.total_mapped_code_bytes,
            self.total_unmapped_code_bytes
        )
        .expect("in-memory write should not fail");

        let mut sections = self.sections.iter().collect::<Vec<_>>();
        sections.sort_by_key(|(name, _)| name.0.as_str());
        for (_, section) in sections {
            writeln!(&mut out).expect("in-memory write should not fail");
            out.push_str(&section.to_text());
        }

        out
    }

    pub fn to_json(&self) -> String {
        let mut out = String::new();
        write!(&mut out, "{{").expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"schema_version\":\"{}\",",
            json_escape(self.schema_version)
        )
        .expect("in-memory write should not fail");
        write!(
            &mut out,
            "\"totals\":{{\"section_bytes\":{},\"code_bytes\":{},\"data_bytes\":{},\"embed_bytes\":{},\"mapped_code_bytes\":{},\"unmapped_code_bytes\":{}}},",
            self.total_section_bytes,
            self.total_code_bytes,
            self.total_data_bytes,
            self.total_embed_bytes,
            self.total_mapped_code_bytes,
            self.total_unmapped_code_bytes
        )
        .expect("in-memory write should not fail");
        write!(&mut out, "\"sections\":[").expect("in-memory write should not fail");

        let mut sections = self.sections.iter().collect::<Vec<_>>();
        sections.sort_by_key(|(name, _)| name.0.as_str());
        for (idx, (_, section)) in sections.into_iter().enumerate() {
            if idx > 0 {
                write!(&mut out, ",").expect("in-memory write should not fail");
            }
            out.push_str(&section.to_json());
        }

        write!(&mut out, "]}}").expect("in-memory write should not fail");
        out
    }
}

#[derive(Debug, Clone)]
pub struct SectionArtifact {
    pub bytes: Vec<u8>,
    pub symtab: FxHashMap<SymbolId, SymbolDef>,
    pub observability: Option<SectionObservability>,
}

#[derive(Debug, Clone)]
pub struct ObjectArtifact {
    pub object: ObjectName,
    pub sections: IndexMap<SectionName, SectionArtifact>,
}

impl ObjectArtifact {
    pub fn observability(&self) -> Option<ObjectObservability> {
        let mut sections: IndexMap<SectionName, SectionObservability> = IndexMap::new();
        let mut total_section_bytes = 0_u32;
        let mut total_code_bytes = 0_u32;
        let mut total_data_bytes = 0_u32;
        let mut total_embed_bytes = 0_u32;
        let mut total_mapped_code_bytes = 0_u32;
        let mut total_unmapped_code_bytes = 0_u32;

        for (section_name, artifact) in &self.sections {
            let Some(observability) = artifact.observability.clone() else {
                continue;
            };

            total_section_bytes = total_section_bytes.saturating_add(observability.section_bytes);
            total_code_bytes = total_code_bytes.saturating_add(observability.code_bytes);
            total_data_bytes = total_data_bytes.saturating_add(observability.data_bytes);
            total_embed_bytes = total_embed_bytes.saturating_add(observability.embed_bytes);
            total_mapped_code_bytes =
                total_mapped_code_bytes.saturating_add(observability.mapped_code_bytes);
            total_unmapped_code_bytes =
                total_unmapped_code_bytes.saturating_add(observability.unmapped_code_bytes);

            sections.insert(section_name.clone(), observability);
        }

        if sections.is_empty() {
            return None;
        }

        Some(ObjectObservability {
            schema_version: OBSERVABILITY_SCHEMA_VERSION,
            sections,
            total_section_bytes,
            total_code_bytes,
            total_data_bytes,
            total_embed_bytes,
            total_mapped_code_bytes,
            total_unmapped_code_bytes,
        })
    }
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c <= '\u{1f}' => {
                let code = c as u32;
                write!(&mut out, "\\u{code:04x}").expect("in-memory write should not fail");
            }
            c => out.push(c),
        }
    }
    out
}
