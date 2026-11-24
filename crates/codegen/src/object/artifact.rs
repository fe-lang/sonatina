use crate::{
    isa::evm::stack_plan::{StackEntry, StackPlan},
    machinst::vcode::{SectionCodeUnitId, VCodeInst},
};
use cranelift_entity::EntityRef;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, GlobalVariableRef, InstId, ValueLabel,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName},
};
use std::fmt::Write as _;

/// The version of the observability text and JSON schema.
///
/// - 0.4.0 adds [`SectionObservability::stack_plans`] and the matching `stack_plan` text lines and
///   `stack_plans` JSON field.
pub const OBSERVABILITY_SCHEMA_VERSION: &str = "0.4.0";

/// The owner of a PC-map range.
///
/// Function machine-instruction IDs are local to their function unit. A
/// function unit and its [`MachineInstId`] must therefore be kept together
/// when consuming an attribution. Synthetic units have no machine instruction
/// owner and are always reported as unmapped.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PcMapUnit {
    Function(FuncRef),
    Synthetic {
        object: ObjectName,
        section: SectionName,
        unit: SectionCodeUnitId,
    },
}

impl PcMapUnit {
    pub fn function(&self) -> Option<FuncRef> {
        match self {
            Self::Function(func) => Some(*func),
            Self::Synthetic { .. } => None,
        }
    }

    pub(crate) fn sort_key(&self) -> (u8, u32, &str, &str, u32) {
        match self {
            Self::Function(func) => (0, func.as_u32(), "", "", 0),
            Self::Synthetic {
                object,
                section,
                unit,
            } => (1, 0, object.0.as_str(), section.0.as_str(), unit.0),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolId {
    Func(FuncRef),
    Global(GlobalVariableRef),
    Embed(EmbedSymbol),
    CurrentSection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolDef {
    pub offset: u32,
    pub size: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnmappedReason {
    MissingProvenance,
    NoMachineInst,
    LabelOrFixupOnly,
    Synthetic,
    Unknown,
}

impl UnmappedReason {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MissingProvenance => "missing_provenance",
            Self::NoMachineInst => "no_machine_inst",
            Self::LabelOrFixupOnly => "label_or_fixup_only",
            Self::Synthetic => "synthetic",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct UnmappedReasonCoverage {
    pub missing_provenance: u32,
    pub no_machine_inst: u32,
    pub label_or_fixup_only: u32,
    pub synthetic: u32,
    pub unknown: u32,
}

impl UnmappedReasonCoverage {
    pub fn add_bytes(&mut self, reason: UnmappedReason, bytes: u32) {
        match reason {
            UnmappedReason::MissingProvenance => {
                self.missing_provenance = self.missing_provenance.saturating_add(bytes);
            }
            UnmappedReason::NoMachineInst => {
                self.no_machine_inst = self.no_machine_inst.saturating_add(bytes);
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
        self.missing_provenance
            .saturating_add(self.no_machine_inst)
            .saturating_add(self.label_or_fixup_only)
            .saturating_add(self.synthetic)
            .saturating_add(self.unknown)
    }
}

/// A machine-IR instruction id, recovered from the vcode `inst_ir` table.
///
/// It is a distinct type from an optimized-IR id so the two namespaces cannot
/// be looked up against each other by accident. Use `.raw()` at the point you
/// deliberately cross back to a bare `InstId`. The inner field is pub on
/// purpose: crossing namespaces requires writing the wrap explicitly, which is
/// the reviewable act. The numeric ID is local to the [`PcMapUnit::Function`]
/// that owns the PC range, not globally unique across functions. Consumers
/// must retain `(PcMapUnit, MachineInstId)` together with the enclosing object
/// and section when consuming a PC map. IDs are not stable across separate
/// compilations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct MachineInstId(pub InstId);

impl MachineInstId {
    pub fn raw(self) -> InstId {
        self.0
    }
}

/// The trace attribution of an emitted PC range.
///
/// A range is mapped only when its machine-IR instruction carries provenance
/// stamped after optimization. Machine-IR identity alone is retained on the
/// unmapped side for diagnostics, but never contributes to mapped coverage.
/// The provenance string is a scalar anchor supplied through the public API
/// after optimization and carried by codegen. It identifies one
/// post-optimization instruction, but does not promise exhaustive
/// transformation ancestry or source ownership for every input that
/// contributed to the emitted range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PcAttribution {
    Mapped {
        machine_inst: MachineInstId,
        post_opt_provenance: String,
    },
    Unmapped {
        machine_inst: Option<MachineInstId>,
        reason: UnmappedReason,
    },
}

impl PcAttribution {
    pub fn machine_inst(&self) -> Option<MachineInstId> {
        match self {
            Self::Mapped { machine_inst, .. } => Some(*machine_inst),
            Self::Unmapped { machine_inst, .. } => *machine_inst,
        }
    }

    pub fn post_opt_provenance(&self) -> Option<&str> {
        match self {
            Self::Mapped {
                post_opt_provenance,
                ..
            } => Some(post_opt_provenance),
            Self::Unmapped { .. } => None,
        }
    }

    pub fn unmapped_reason(&self) -> Option<UnmappedReason> {
        match self {
            Self::Mapped { .. } => None,
            Self::Unmapped { reason, .. } => Some(*reason),
        }
    }

    pub fn is_mapped(&self) -> bool {
        matches!(self, Self::Mapped { .. })
    }
}

/// One emitted PC interval and its owning code unit.
///
/// For a function unit, [`Self::unit`] scopes the optional machine instruction
/// ID in [`Self::attribution`]. Numeric machine IDs must not be joined across
/// entries from different function units.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcMapEntry {
    pub pc_start: u32,
    pub pc_end: u32,
    pub unit: PcMapUnit,
    pub func_name: String,
    pub block: BlockId,
    pub vcode_inst: VCodeInst,
    pub attribution: PcAttribution,
}

/// The operand stack plan of one function unit of a section.
///
/// It is keyed like [`PcMapEntry::attribution`]: `func` is the function of a
/// [`PcMapUnit::Function`] and the [`MachineInstId`]s inside [`Self::plan`] are local to that
/// function. Together they join an emitted PC range to the planned stack of its instruction with
/// [`SectionObservability::stack_before`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionStackPlan {
    pub func: FuncRef,
    pub func_name: String,
    pub plan: StackPlan,
}

impl FunctionStackPlan {
    /// One `stack_plan` line per function, then a line per planned instruction. An entry is
    /// `v<id>`, `<RET>` or `<CALLRET>`; a value has `:dead` and `:const` when flagged and
    /// `@<label>` for each label.
    fn write_text(&self, out: &mut String) {
        writeln!(
            out,
            "stack_plan func={} insts={}",
            self.func_name,
            self.plan.insts.len()
        )
        .expect("in-memory write should not fail");
        for record in &self.plan.insts {
            write!(out, "  inst {} stack=[", record.inst.raw().0)
                .expect("in-memory write should not fail");
            for (idx, entry) in record.stack.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                match entry {
                    StackEntry::Value(value) => {
                        write!(out, "v{}", value.value.index())
                            .expect("in-memory write should not fail");
                        if value.dead {
                            out.push_str(":dead");
                        }
                        if value.constant {
                            out.push_str(":const");
                        }
                        write_text_labels(out, &value.labels);
                    }
                    StackEntry::ReturnAddress => out.push_str("<RET>"),
                    StackEntry::CallContinuation => out.push_str("<CALLRET>"),
                }
            }
            out.push_str("]\n");
        }
    }

    fn write_json(&self, out: &mut String) {
        write!(
            out,
            "{{\"unit\":{{\"kind\":\"function\",\"func\":{}}},\"func_name\":\"{}\",\"insts\":[",
            self.func.index(),
            json_escape(&self.func_name)
        )
        .expect("in-memory write should not fail");
        for (idx, record) in self.plan.insts.iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            write!(
                out,
                "{{\"machine_inst\":{},\"stack\":[",
                record.inst.raw().0
            )
            .expect("in-memory write should not fail");
            for (idx, entry) in record.stack.iter().enumerate() {
                if idx > 0 {
                    out.push(',');
                }
                match entry {
                    StackEntry::Value(value) => {
                        write!(
                            out,
                            "{{\"kind\":\"value\",\"value\":{},\"dead\":{},\"constant\":{},\"labels\":",
                            value.value.index(),
                            value.dead,
                            value.constant
                        )
                        .expect("in-memory write should not fail");
                        write_json_labels(out, &value.labels);
                        out.push('}');
                    }
                    StackEntry::ReturnAddress => out.push_str("{\"kind\":\"return_address\"}"),
                    StackEntry::CallContinuation => {
                        out.push_str("{\"kind\":\"call_continuation\"}")
                    }
                }
            }
            out.push_str("]}");
        }
        out.push_str("]}");
    }
}

/// Observability captured while linking one section.
///
/// This schema describes EVM object-section bytes and program-counter ranges;
/// it is not a target-neutral provenance format. This is an owned snapshot of
/// the section at compilation time. It is not a live view of the module and
/// does not retain historical states if the module
/// is mutated between optimization, stamping, and compilation.
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
    /// The planned operand stack of each function unit that the section lays out, in the order of
    /// the section's layout of its functions. Empty unless the compiler was asked to capture stack
    /// plans (`EvmCompiler::with_stack_plans`), which does not change the generated code. Code
    /// that belongs to no function has no plan. See [`StackPlan`] for what a plan means and for
    /// its scope.
    pub stack_plans: Vec<FunctionStackPlan>,
}

impl SectionObservability {
    /// The operand stack planned for `inst` of the function unit `unit`, when this section
    /// captured stack plans and the plan has a record for it.
    ///
    /// This is the join from a PC map entry to its stack: pass the entry's `unit` and the
    /// [`MachineInstId`] of its attribution. Every PC map entry of one instruction maps to the
    /// same record. The record describes the stack before the first opcode of the instruction,
    /// which is the entry of the instruction with the lowest `pc_start`; see
    /// [`InstStack`](crate::isa::evm::stack_plan::InstStack) for the later opcodes. The lookup
    /// scans the list of functions, so a consumer that visits every PC map entry should index
    /// [`Self::stack_plans`] by function once.
    pub fn stack_before(
        &self,
        unit: &PcMapUnit,
        inst: MachineInstId,
    ) -> Option<&crate::isa::evm::stack_plan::InstStack> {
        let func = unit.function()?;
        self.stack_plans
            .iter()
            .find(|function| function.func == func)?
            .plan
            .stack_before(inst)
    }

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
            "unmapped missing_provenance={} no_machine_inst={} label_or_fixup_only={} synthetic={} unknown={}",
            self.unmapped_reason_coverage.missing_provenance,
            self.unmapped_reason_coverage.no_machine_inst,
            self.unmapped_reason_coverage.label_or_fixup_only,
            self.unmapped_reason_coverage.synthetic,
            self.unmapped_reason_coverage.unknown,
        )
        .expect("in-memory write should not fail");

        let mut entries = self.pc_map.clone();
        sort_pc_map_entries(&mut entries);
        for entry in entries {
            let reason = entry
                .attribution
                .unmapped_reason()
                .map(UnmappedReason::as_str)
                .unwrap_or("-");
            let post_opt = entry.attribution.post_opt_provenance().unwrap_or("-");
            let ir = entry
                .attribution
                .machine_inst()
                .map(|ir| ir.raw().0.to_string())
                .unwrap_or("-".into());
            writeln!(
                &mut out,
                "pc [{}, {}) func={} block={} vcode={} machine={} reason={} post_opt={}",
                entry.pc_start,
                entry.pc_end,
                entry.func_name,
                entry.block.index(),
                entry.vcode_inst.index(),
                ir,
                reason,
                post_opt
            )
            .expect("in-memory write should not fail");
        }

        for function in &self.stack_plans {
            function.write_text(&mut out);
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
            "\"missing_provenance\":{},\"no_machine_inst\":{},\"label_or_fixup_only\":{},\"synthetic\":{},\"unknown\":{}",
            self.unmapped_reason_coverage.missing_provenance,
            self.unmapped_reason_coverage.no_machine_inst,
            self.unmapped_reason_coverage.label_or_fixup_only,
            self.unmapped_reason_coverage.synthetic,
            self.unmapped_reason_coverage.unknown
        )
        .expect("in-memory write should not fail");
        write!(&mut out, "}},").expect("in-memory write should not fail");

        write!(&mut out, "\"pc_map\":[").expect("in-memory write should not fail");
        let mut entries = self.pc_map.clone();
        sort_pc_map_entries(&mut entries);
        for (idx, entry) in entries.iter().enumerate() {
            if idx > 0 {
                write!(&mut out, ",").expect("in-memory write should not fail");
            }
            write!(&mut out, "{{").expect("in-memory write should not fail");
            write!(
                &mut out,
                "\"pc_start\":{},\"pc_end\":{},\"block\":{},\"vcode_inst\":{}",
                entry.pc_start,
                entry.pc_end,
                entry.block.index(),
                entry.vcode_inst.index()
            )
            .expect("in-memory write should not fail");
            match &entry.unit {
                PcMapUnit::Function(func) => write!(
                    &mut out,
                    ",\"unit\":{{\"kind\":\"function\",\"func\":{}}}",
                    func.index()
                ),
                PcMapUnit::Synthetic {
                    object,
                    section,
                    unit,
                } => write!(
                    &mut out,
                    ",\"unit\":{{\"kind\":\"synthetic\",\"object\":\"{}\",\"section\":\"{}\",\"unit\":{}}}",
                    json_escape(&object.0),
                    json_escape(&section.0),
                    unit.0
                ),
            }
            .expect("in-memory write should not fail");
            write!(
                &mut out,
                ",\"func_name\":\"{}\"",
                json_escape(&entry.func_name)
            )
            .expect("in-memory write should not fail");

            match &entry.attribution {
                PcAttribution::Mapped {
                    machine_inst,
                    post_opt_provenance,
                } => write!(
                    &mut out,
                    ",\"attribution\":{{\"status\":\"mapped\",\"machine_inst\":{},\"post_opt_provenance\":\"{}\"}}",
                    machine_inst.raw().0,
                    json_escape(post_opt_provenance)
                ),
                PcAttribution::Unmapped { machine_inst, reason } => {
                    write!(
                        &mut out,
                        ",\"attribution\":{{\"status\":\"unmapped\",\"machine_inst\":"
                    )
                    .expect("in-memory write should not fail");
                    if let Some(machine_inst) = machine_inst {
                        write!(&mut out, "{}", machine_inst.raw().0)
                            .expect("in-memory write should not fail");
                    } else {
                        write!(&mut out, "null").expect("in-memory write should not fail");
                    }
                    write!(&mut out, ",\"reason\":\"{}\"}}", reason.as_str())
                }
            }
            .expect("in-memory write should not fail");

            write!(&mut out, "}}").expect("in-memory write should not fail");
        }
        write!(&mut out, "]").expect("in-memory write should not fail");
        write!(&mut out, ",\"stack_plans\":[").expect("in-memory write should not fail");
        for (idx, function) in self.stack_plans.iter().enumerate() {
            if idx > 0 {
                write!(&mut out, ",").expect("in-memory write should not fail");
            }
            function.write_json(&mut out);
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

fn sort_pc_map_entries(entries: &mut [PcMapEntry]) {
    entries.sort_by(|a, b| {
        (a.pc_start, a.pc_end)
            .cmp(&(b.pc_start, b.pc_end))
            .then_with(|| a.unit.sort_key().cmp(&b.unit.sort_key()))
            .then_with(|| a.block.index().cmp(&b.block.index()))
            .then_with(|| a.vcode_inst.index().cmp(&b.vcode_inst.index()))
    });
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
    /// Build the aggregate object-level observability view from per-section observability data.
    ///
    /// Returns `None` when observability was not emitted at compile time.
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

    /// Deterministic text serialization of object-level observability, if available.
    pub fn observability_text(&self) -> Option<String> {
        self.observability().map(|obs| obs.to_text())
    }

    /// Deterministic JSON serialization of object-level observability, if available.
    pub fn observability_json(&self) -> Option<String> {
        self.observability().map(|obs| obs.to_json())
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

/// Appends `@<label>` for each label.
fn write_text_labels(out: &mut String, labels: &[ValueLabel]) {
    for label in labels {
        write!(out, "@{}", label.0).expect("in-memory write should not fail");
    }
}

/// Appends a JSON array of label numbers.
fn write_json_labels(out: &mut String, labels: &[ValueLabel]) {
    out.push('[');
    for (idx, label) in labels.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        write!(out, "{}", label.0).expect("in-memory write should not fail");
    }
    out.push(']');
}
