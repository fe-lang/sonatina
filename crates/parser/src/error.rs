use std::io;

use crate::{syntax::Rule, Span};
use annotate_snippets::{Level, Renderer, Snippet};
use smol_str::SmolStr;
use sonatina_triple::InvalidTriple;

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Error {
    NumberOutOfBounds(Span),
    InvalidTarget(InvalidTriple, Span),
    SyntaxError(pest::error::Error<Rule>),
    Undefined(UndefinedKind, Span),
    DuplicateValueName(SmolStr, Span),
    TypeMismatch {
        specified: SmolStr,
        inferred: SmolStr,
        span: Span,
    },
}

#[derive(Debug)]
pub enum UndefinedKind {
    Block(ir::Block),
    Func(SmolStr),
    Type(SmolStr),
    Value(SmolStr),
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
            Error::TypeMismatch { span, .. } => *span,
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
            },
            Error::DuplicateValueName(name, _) => format!("value name `{name}` is already defined"),
            Error::TypeMismatch {
                specified,
                inferred,
                ..
            } => format!(
                "type mismatch: value declared as `{specified}`, but inferred type is `{inferred}`",
            ),
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
