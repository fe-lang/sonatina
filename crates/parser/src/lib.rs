pub mod parser;

mod lexer;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub line: u32,
}

impl Error {
    pub fn new(kind: ErrorKind, line: u32) -> Self {
        Self { kind, line }
    }
}

#[derive(Debug)]
pub enum ErrorKind {
    InvalidToken(String),
    SyntaxError(String),
    SemanticError(String),
}
