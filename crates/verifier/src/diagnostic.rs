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
    StructuralInvariantViolation,
    UsersSetMismatch,
    InstResultMapBroken,
    ImmediateCacheMismatch,
    GlobalCacheMismatch,
}

impl DiagnosticCode {
    pub const fn as_u16(self) -> u16 {
        match self {
            Self::InvalidValueRef => 1,
            Self::InvalidBlockRef => 2,
            Self::InvalidFuncRef => 3,
            Self::InvalidTypeRef => 4,
            Self::InvalidInstRef => 5,
            Self::InvalidGlobalRef => 6,
            Self::LayoutBlockCycle => 100,
            Self::LayoutInstCycle => 101,
            Self::InstInMultipleBlocks => 102,
            Self::InsertedButUnlisted => 103,
            Self::UnlistedButInserted => 104,
            Self::MissingEntryBlock => 105,
            Self::EmptyBlock => 200,
            Self::MissingTerminator => 201,
            Self::TerminatorNotLast => 202,
            Self::NonTerminatorAtEnd => 203,
            Self::BranchToMissingBlock => 300,
            Self::BranchToNonInsertedBlock => 301,
            Self::BranchInfoMismatch => 302,
            Self::BranchToEntryDisallowed => 303,
            Self::UnreachableBlock => 304,
            Self::PhiNotAtBlockTop => 400,
            Self::PhiInEntryBlock => 401,
            Self::PhiArgCountMismatchPreds => 402,
            Self::PhiHasNonPredIncoming => 403,
            Self::PhiDuplicateIncomingBlock => 404,
            Self::PhiIncomingTypeMismatch => 405,
            Self::UseBeforeDefInBlock => 500,
            Self::DefDoesNotDominateUse => 501,
            Self::PhiIncomingNotAvailableOnEdge => 502,
            Self::SelfReferentialPhiNotInLoop => 503,
            Self::InstOperandTypeMismatch => 600,
            Self::InstResultTypeMismatch => 601,
            Self::CallArgTypeMismatch => 602,
            Self::CallArityMismatch => 603,
            Self::ReturnTypeMismatch => 604,
            Self::UnstorableTypeInMemoryOp => 605,
            Self::GepTypeComputationFailed => 606,
            Self::ExtractIndexOutOfBounds => 607,
            Self::InsertIndexOutOfBounds => 608,
            Self::ValueTypeMismatch => 609,
            Self::InvalidSignature => 610,
            Self::StructuralInvariantViolation => 611,
            Self::UsersSetMismatch => 700,
            Self::InstResultMapBroken => 701,
            Self::ImmediateCacheMismatch => 702,
            Self::GlobalCacheMismatch => 703,
        }
    }

    pub fn as_str(self) -> String {
        format!("IR{:04}", self.as_u16())
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
pub struct DiagnosticContext {
    pub function_name: Option<String>,
    pub inst_text: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub severity: Severity,
    pub message: String,
    pub primary: Location,
    pub notes: Vec<Note>,
    pub context: Option<DiagnosticContext>,
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
            context: None,
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

    pub fn with_context(mut self, context: DiagnosticContext) -> Self {
        self.context = Some(context);
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
        write!(
            f,
            "{} [{}] {} @ {}",
            self.severity, self.code, self.message, self.primary
        )?;

        if let Some(context) = &self.context {
            match (&context.function_name, &context.inst_text) {
                (Some(function_name), Some(inst_text)) => {
                    write!(f, " ({function_name}, {inst_text})")?;
                }
                (Some(function_name), None) => {
                    write!(f, " ({function_name})")?;
                }
                (None, Some(inst_text)) => {
                    write!(f, " ({inst_text})")?;
                }
                (None, None) => {}
            }
        }

        writeln!(f)?;

        for note in &self.notes {
            writeln!(f, "  note: {}", note.message)?;
        }

        if let Some(snippet) = &self.snippet {
            writeln!(f, "{snippet}")?;
        }

        Ok(())
    }
}
