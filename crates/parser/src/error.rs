use std::io;

use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};
use smol_str::SmolStr;
use sonatina_triple::{InvalidTriple, TargetTriple};

use crate::{Span, syntax::Rule};

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Error {
    NumberOutOfBounds(Span),
    InvalidTarget(InvalidTriple, Span),
    SyntaxError(pest::error::Error<Rule>),
    Undefined(UndefinedKind, Span),
    DuplicateValueName(SmolStr, Span),
    DuplicatedDeclaration(SmolStr, Span),

    InstArgKindMismatch {
        expected: SmolStr,
        actual: Option<SmolStr>,
        span: Span,
    },

    InstArgNumMismatch {
        expected: ir::InstArity,
        actual: usize,
        span: Span,
    },

    UnexpectedTrailingInstArg(Span),

    UnsupportedInst {
        triple: TargetTriple,
        inst: SmolStr,
        span: Span,
    },

    TypeError {
        expected: String,
        span: Span,
    },
}

#[derive(Debug)]
pub enum UndefinedKind {
    Block(ir::BlockId),
    Func(SmolStr),
    Type(SmolStr),
    Value(SmolStr),
    Inst(SmolStr),
}

impl Error {
    pub fn span(&self) -> Span {
        match self {
            Error::NumberOutOfBounds(span) => *span,
            Error::InvalidTarget(_, span) => *span,
            Error::Undefined(_, span) => *span,
            Error::DuplicateValueName(_, span) => *span,
            Error::DuplicatedDeclaration(_, span) => *span,

            Error::SyntaxError(err) => match err.location {
                pest::error::InputLocation::Pos(p) => Span(p as u32, p as u32),
                pest::error::InputLocation::Span((s, e)) => Span(s as u32, e as u32),
            },
            Error::UnexpectedTrailingInstArg(span) => *span,
            Error::InstArgKindMismatch { span, .. } => *span,
            Error::InstArgNumMismatch { span, .. } => *span,
            Error::UnsupportedInst { span, .. } => *span,
            Error::TypeError { span, .. } => *span,
        }
    }

    pub fn print(
        &self,
        mut w: impl io::Write,
        path: &str,
        content: &str,
        colors: bool,
    ) -> io::Result<()> {
        let label = match self {
            Error::NumberOutOfBounds(_) => "number out of bounds".into(),

            Error::InvalidTarget(err, _) => err.to_string(),

            Error::SyntaxError(err) => err.to_string(),

            Error::Undefined(kind, _) => match kind {
                UndefinedKind::Block(id) => format!("undefined block: `block{}`", id.0),
                UndefinedKind::Func(name) => format!("undefined function: `%{name}`"),
                UndefinedKind::Type(name) => format!("undefined type: `@{name}`"),
                UndefinedKind::Value(name) => format!("undefined value: `{name}`"),
                UndefinedKind::Inst(name) => format!("unknown inst: `{name}`"),
            },

            Error::DuplicatedDeclaration(name, _) => format!("{name} is already declared"),
            Error::DuplicateValueName(name, _) => format!("value name `{name}` is already defined"),

            Error::UnexpectedTrailingInstArg(_) => "unexpected trailing inst argument".to_string(),

            Error::InstArgKindMismatch {
                expected, actual, ..
            } => {
                let actual = actual.as_ref().map(|s| s.as_str()).unwrap_or("none");
                format!("inst arg kind mismtach: expected `{expected}`, but `{actual}` given")
            }

            Error::InstArgNumMismatch {
                expected, actual, ..
            } => match expected {
                ir::InstArity::Exact(n) => {
                    format!("expected `{n}` number of arguments, but given `{actual}")
                }
                ir::InstArity::AtLeast(n) => {
                    format!("expected at least `{n}` number of arguments, but given `{actual}")
                }
                ir::InstArity::AtMost(n) => {
                    format!("expected at most `{n}` number of arguments, but given `{actual}")
                }
                ir::InstArity::Range { min, max } => {
                    format!(
                        "expected between `{min}` and `{max}` number of arguments, but given `{actual}"
                    )
                }
            },

            Error::UnsupportedInst { triple, inst, .. } => {
                format!("{triple} doesn't support {inst}")
            }

            Error::TypeError { expected, .. } => {
                format!("type error: expected `{expected}` here")
            }
        };
        let snippet = Level::ERROR.primary_title("parse error").element(
            Snippet::source(content)
                .line_start(0)
                .path(path)
                .fold(true)
                .annotation(
                    AnnotationKind::Primary
                        .span(self.span().as_range())
                        .label(&label),
                ),
        );
        let rend = if colors {
            Renderer::styled()
        } else {
            Renderer::plain()
        };
        let disp = rend.render(&[snippet]);
        writeln!(w, "{disp}")
    }

    pub fn print_to_string(&self, path: &str, content: &str, colors: bool) -> String {
        let mut v = vec![];
        self.print(&mut v, path, content, colors).unwrap();
        String::from_utf8(v).unwrap()
    }
}
