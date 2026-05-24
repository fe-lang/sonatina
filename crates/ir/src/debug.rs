use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};

use crate::InstId;

/// Function-local handle for an opaque frontend origin record.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrontendOriginId(u32);
entity_impl!(FrontendOriginId, "frontend_origin");

/// Function-local handle for an instruction debug location.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DebugLocId(u32);
entity_impl!(DebugLocId, "debug_loc");

/// Function-local handle for frontend-neutral debug tags.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DebugTagId(u32);
entity_impl!(DebugTagId, "debug_tag");

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceSpan {
    pub file: Option<String>,
    pub start: u32,
    pub end: u32,
    pub start_line: Option<u32>,
    pub start_column: Option<u32>,
    pub end_line: Option<u32>,
    pub end_column: Option<u32>,
}

impl SourceSpan {
    pub fn new(start: u32, end: u32) -> Self {
        Self {
            file: None,
            start,
            end,
            start_line: None,
            start_column: None,
            end_line: None,
            end_column: None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FrontendOriginKind {
    SourceExpr,
    SourceStmt,
    SourceDecl,
    SourceType,
    SourcePattern,
    Synthetic,
    SemanticScope,
    InlineCallsite,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontendOriginRecord {
    /// Frontend-owned serialized identity. Sonatina never parses this string.
    pub external_key: Option<String>,
    pub source_span: Option<SourceSpan>,
    pub display_label: Option<String>,
    pub kind: FrontendOriginKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DebugConfidence {
    Exact,
    Conservative,
    Combined,
    Synthetic,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DebugLoc {
    pub primary_origin: Option<FrontendOriginId>,
    pub source_span: Option<SourceSpan>,
    pub confidence: DebugConfidence,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DebugTagKind {
    InlineCallsite,
    SemanticScope,
    SyntheticReason,
    LoweringReason,
    FrontendLabel,
    OptimizationNote,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DebugTagPayload {
    Empty,
    Text(String),
    KeyValue { key: String, value: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DebugTag {
    pub kind: DebugTagKind,
    pub origin: Option<FrontendOriginId>,
    pub payload: DebugTagPayload,
}

#[derive(Clone, Debug, Default)]
pub struct DebugMetadata {
    frontend_origins: PrimaryMap<FrontendOriginId, FrontendOriginRecord>,
    debug_locs: PrimaryMap<DebugLocId, DebugLoc>,
    debug_tags: PrimaryMap<DebugTagId, DebugTag>,
    inst_locs: SecondaryMap<InstId, Option<DebugLocId>>,
    inst_tags: SecondaryMap<InstId, Vec<DebugTagId>>,
}

impl DebugMetadata {
    pub fn add_frontend_origin(&mut self, record: FrontendOriginRecord) -> FrontendOriginId {
        self.frontend_origins.push(record)
    }

    pub fn frontend_origin(&self, origin: FrontendOriginId) -> Option<&FrontendOriginRecord> {
        self.frontend_origins.get(origin)
    }

    pub fn frontend_origins(
        &self,
    ) -> impl Iterator<Item = (FrontendOriginId, &FrontendOriginRecord)> + '_ {
        self.frontend_origins.iter()
    }

    pub fn add_debug_loc(&mut self, loc: DebugLoc) -> DebugLocId {
        self.debug_locs.push(loc)
    }

    pub fn debug_loc(&self, loc: DebugLocId) -> Option<&DebugLoc> {
        self.debug_locs.get(loc)
    }

    pub fn debug_locs(&self) -> impl Iterator<Item = (DebugLocId, &DebugLoc)> + '_ {
        self.debug_locs.iter()
    }

    pub fn add_debug_tag(&mut self, tag: DebugTag) -> DebugTagId {
        self.debug_tags.push(tag)
    }

    pub fn debug_tag(&self, tag: DebugTagId) -> Option<&DebugTag> {
        self.debug_tags.get(tag)
    }

    pub fn debug_tags(&self) -> impl Iterator<Item = (DebugTagId, &DebugTag)> + '_ {
        self.debug_tags.iter()
    }

    pub fn set_inst_debug_loc(&mut self, inst: InstId, loc: DebugLocId) {
        self.inst_locs[inst] = Some(loc);
    }

    pub fn clear_inst_debug_loc(&mut self, inst: InstId) {
        self.inst_locs[inst] = None;
    }

    pub fn inst_debug_loc(&self, inst: InstId) -> Option<DebugLocId> {
        self.inst_locs.get(inst).copied().flatten()
    }

    pub fn add_inst_debug_tag(&mut self, inst: InstId, tag: DebugTagId) {
        self.inst_tags[inst].push(tag);
    }

    pub fn set_inst_debug_tags(&mut self, inst: InstId, tags: Vec<DebugTagId>) {
        self.inst_tags[inst] = tags;
    }

    pub fn inst_debug_tags(&self, inst: InstId) -> &[DebugTagId] {
        self.inst_tags.get(inst).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn clear_inst_debug(&mut self, inst: InstId) {
        self.clear_inst_debug_loc(inst);
        self.inst_tags[inst].clear();
    }

    pub fn copy_inst_debug(&mut self, from: InstId, to: InstId) {
        self.inst_locs[to] = self.inst_debug_loc(from);
        self.inst_tags[to] = self.inst_debug_tags(from).to_vec();
    }
}
