use std::fmt;

use sonatina_ir::{BlockId, GlobalVariableRef, InstId, Type, ValueId, module::FuncRef};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum DiagnosticCode {
    InvalidValueRef,
    InvalidBlockRef,
    InvalidFuncRef,
    InvalidTypeRef,
    InvalidInstRef,
    InvalidGlobalRef,
    LayoutBlockCycle,
    LayoutInstCycle,
    InstInMultipleBlocks,
    InsertedButUnlisted,
    UnlistedButInserted,
    MissingEntryBlock,
    EmptyBlock,
    MissingTerminator,
    TerminatorNotLast,
    NonTerminatorAtEnd,
    BranchToMissingBlock,
    BranchToNonInsertedBlock,
    BranchInfoMismatch,
    BranchToEntryDisallowed,
    UnreachableBlock,
    PhiNotAtBlockTop,
    PhiInEntryBlock,
    PhiArgCountMismatchPreds,
    PhiHasNonPredIncoming,
    PhiDuplicateIncomingBlock,
    PhiIncomingTypeMismatch,
    UseBeforeDefInBlock,
    DefDoesNotDominateUse,
    PhiIncomingNotAvailableOnEdge,
    SelfReferentialPhiNotInLoop,
    InstOperandTypeMismatch,
    InstResultTypeMismatch,
    CallArgTypeMismatch,
    CallArityMismatch,
    ReturnTypeMismatch,
    UnstorableTypeInMemoryOp,
    GepTypeComputationFailed,
    ExtractIndexOutOfBounds,
    InsertIndexOutOfBounds,
    ValueTypeMismatch,
    InvalidSignature,
    UsersSetMismatch,
    InstResultMapBroken,
    ImmediateCacheMismatch,
    GlobalCacheMismatch,
}

impl DiagnosticCode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidValueRef => "IR0001",
            Self::InvalidBlockRef => "IR0002",
            Self::InvalidFuncRef => "IR0003",
            Self::InvalidTypeRef => "IR0004",
            Self::InvalidInstRef => "IR0005",
            Self::InvalidGlobalRef => "IR0006",
            Self::LayoutBlockCycle => "IR0100",
            Self::LayoutInstCycle => "IR0101",
            Self::InstInMultipleBlocks => "IR0102",
            Self::InsertedButUnlisted => "IR0103",
            Self::UnlistedButInserted => "IR0104",
            Self::MissingEntryBlock => "IR0105",
            Self::EmptyBlock => "IR0200",
            Self::MissingTerminator => "IR0201",
            Self::TerminatorNotLast => "IR0202",
            Self::NonTerminatorAtEnd => "IR0203",
            Self::BranchToMissingBlock => "IR0300",
            Self::BranchToNonInsertedBlock => "IR0301",
            Self::BranchInfoMismatch => "IR0302",
            Self::BranchToEntryDisallowed => "IR0303",
            Self::UnreachableBlock => "IR0304",
            Self::PhiNotAtBlockTop => "IR0400",
            Self::PhiInEntryBlock => "IR0401",
            Self::PhiArgCountMismatchPreds => "IR0402",
            Self::PhiHasNonPredIncoming => "IR0403",
            Self::PhiDuplicateIncomingBlock => "IR0404",
            Self::PhiIncomingTypeMismatch => "IR0405",
            Self::UseBeforeDefInBlock => "IR0500",
            Self::DefDoesNotDominateUse => "IR0501",
            Self::PhiIncomingNotAvailableOnEdge => "IR0502",
            Self::SelfReferentialPhiNotInLoop => "IR0503",
            Self::InstOperandTypeMismatch => "IR0600",
            Self::InstResultTypeMismatch => "IR0601",
            Self::CallArgTypeMismatch => "IR0602",
            Self::CallArityMismatch => "IR0603",
            Self::ReturnTypeMismatch => "IR0604",
            Self::UnstorableTypeInMemoryOp => "IR0605",
            Self::GepTypeComputationFailed => "IR0606",
            Self::ExtractIndexOutOfBounds => "IR0607",
            Self::InsertIndexOutOfBounds => "IR0608",
            Self::ValueTypeMismatch => "IR0609",
            Self::InvalidSignature => "IR0610",
            Self::UsersSetMismatch => "IR0700",
            Self::InstResultMapBroken => "IR0701",
            Self::ImmediateCacheMismatch => "IR0702",
            Self::GlobalCacheMismatch => "IR0703",
        }
    }
}

impl fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Severity {
    Error,
    Warning,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => "error".fmt(f),
            Self::Warning => "warning".fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Location {
    Module,
    Function(FuncRef),
    Global(GlobalVariableRef),
    Object {
        name: String,
        section: Option<String>,
    },
    Block {
        func: FuncRef,
        block: BlockId,
    },
    Inst {
        func: FuncRef,
        block: Option<BlockId>,
        inst: InstId,
    },
    Value {
        func: FuncRef,
        value: ValueId,
    },
    Type {
        func: Option<FuncRef>,
        ty: Type,
    },
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module => "module".fmt(f),
            Self::Function(func) => write!(f, "func{}", func.as_u32()),
            Self::Global(gv) => write!(f, "global{}", gv.as_u32()),
            Self::Object { name, section } => {
                if let Some(section) = section {
                    write!(f, "object @{name}.{section}")
                } else {
                    write!(f, "object @{name}")
                }
            }
            Self::Block { func, block } => write!(f, "func{}:{}", func.as_u32(), block),
            Self::Inst { func, block, inst } => {
                if let Some(block) = block {
                    write!(f, "func{}:{}:inst{}", func.as_u32(), block, inst.as_u32())
                } else {
                    write!(f, "func{}:inst{}", func.as_u32(), inst.as_u32())
                }
            }
            Self::Value { func, value } => write!(f, "func{}:v{}", func.as_u32(), value.as_u32()),
            Self::Type { func, ty } => {
                if let Some(func) = func {
                    write!(f, "func{}:type:{ty:?}", func.as_u32())
                } else {
                    write!(f, "type:{ty:?}")
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Note {
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub severity: Severity,
    pub message: String,
    pub primary: Location,
    pub notes: Vec<Note>,
    pub snippet: Option<String>,
}

impl Diagnostic {
    pub fn new(
        code: DiagnosticCode,
        severity: Severity,
        message: impl Into<String>,
        primary: Location,
    ) -> Self {
        Self {
            code,
            severity,
            message: message.into(),
            primary,
            notes: Vec::new(),
            snippet: None,
        }
    }

    pub fn error(code: DiagnosticCode, message: impl Into<String>, primary: Location) -> Self {
        Self::new(code, Severity::Error, message, primary)
    }

    pub fn warning(code: DiagnosticCode, message: impl Into<String>, primary: Location) -> Self {
        Self::new(code, Severity::Warning, message, primary)
    }

    pub fn with_note(mut self, message: impl Into<String>) -> Self {
        self.notes.push(Note {
            message: message.into(),
        });
        self
    }

    pub fn with_snippet(mut self, snippet: Option<String>) -> Self {
        self.snippet = snippet;
        self
    }

    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{} [{}] {} @ {}",
            self.severity, self.code, self.message, self.primary
        )?;

        for note in &self.notes {
            writeln!(f, "  note: {}", note.message)?;
        }

        if let Some(snippet) = &self.snippet {
            writeln!(f, "{snippet}")?;
        }

        Ok(())
    }
}
