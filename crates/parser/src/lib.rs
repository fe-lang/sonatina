pub mod parser;

mod lexer;

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;

#[derive(Debug)]
pub struct Error<'a> {
    pub kind: ErrorKind<'a>,
    pub line: u32,
}

impl<'a> Error<'a> {
    pub fn new(kind: ErrorKind<'a>, line: u32) -> Self {
        Self { kind, line }
    }
}

#[derive(Debug)]
pub enum ErrorKind<'a> {
    InvalidToken(&'a str),
}
