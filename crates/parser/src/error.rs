use std::io;

use annotate_snippets::{Level, Renderer, Snippet};
use smol_str::SmolStr;
use sonatina_triple::{InvalidTriple, TargetTriple};

use crate::{syntax::Rule, Span};

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Error {
    NumberOutOfBounds(Span),
    InvalidTarget(InvalidTriple, Span),
    SyntaxError(pest::error::Error<Rule>),
    Undefined(UndefinedKind, Span),
    DuplicateValueName(SmolStr, Span),

    InstArgKindMismatch {
        expected: SmolStr,
        actual: Option<SmolStr>,
        span: Span,
    },

    InstArgNumMismatch {
        expected: ArityBound,
        actual: usize,
        span: Span,
    },

    UnexpectedTrailingInstArg(Span),

    UnsupportedInst {
        triple: TargetTriple,
        inst: SmolStr,
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
            Error::SyntaxError(err) => match err.location {
                pest::error::InputLocation::Pos(p) => Span(p as u32, p as u32),
                pest::error::InputLocation::Span((s, e)) => Span(s as u32, e as u32),
            },
            Error::UnexpectedTrailingInstArg(span) => *span,
            Error::InstArgKindMismatch { span, .. } => *span,
            Error::InstArgNumMismatch { span, .. } => *span,
            Error::UnsupportedInst { span, .. } => *span,
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
                UndefinedKind::Type(name) => format!("undefined type: `%{name}`"),
                UndefinedKind::Value(name) => format!("undefined value: `{name}`"),
                UndefinedKind::Inst(name) => format!("unknown inst: `{name}`"),
            },

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
                ArityBound::Exact(n) => {
                    format!("expected `{n}` number of arguments, but given `{actual}")
                }
                ArityBound::AtLeast(n) => {
                    format!("expected at least `{n}` number of arguments, but given `{actual}")
                }
                ArityBound::AtMost(n) => {
                    format!("expected at most `{n}` number of arguments, but given `{actual}")
                }
            },

            Error::UnsupportedInst { triple, inst, .. } => {
                format!("{triple} doesn't support {inst}")
            }
        };
        let snippet = Level::Error.title("parse error").snippet(
            Snippet::source(content)
                .line_start(0)
                .origin(path)
                .fold(true)
                .annotation(Level::Error.span(self.span().as_range()).label(&label)),
        );
        let rend = if colors {
            Renderer::styled()
        } else {
            Renderer::plain()
        };
        let disp = rend.render(snippet);
        write!(w, "{}", disp)
    }

    pub fn print_to_string(&self, path: &str, content: &str, colors: bool) -> String {
        let mut v = vec![];
        self.print(&mut v, path, content, colors).unwrap();
        String::from_utf8(v).unwrap()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ArityBound {
    Exact(usize),
    AtLeast(usize),
    AtMost(usize),
}

impl ArityBound {
    pub fn verify_arity(&self, arity: usize, span: Span) -> Result<(), Box<Error>> {
        let is_ok = match self {
            Self::Exact(n) => *n == arity,

            Self::AtLeast(n) => *n <= arity,

            Self::AtMost(n) => *n >= arity,
        };

        if is_ok {
            Ok(())
        } else {
            Err(Box::new(Error::InstArgNumMismatch {
                expected: *self,
                actual: arity,
                span,
            }))
        }
    }
}
