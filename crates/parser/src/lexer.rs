use std::fmt;

use sonatina_codegen::ir::{insn::DataLocationKind, Linkage, Type};

use super::{Error, ErrorKind, Result};

pub(super) struct Lexer<'a> {
    input: &'a [u8],
    peek: Option<WithLoc<Token<'a>>>,
    cur: usize,
    line: u32,
}

macro_rules! try_eat_variant {
    (
        $self:ident,
        ($first_name:expr, $first_code:expr),
        $(($name:expr, $code:expr),)*
    ) => {
        if $self.eat_string_if($first_name).is_some() {
            Some($first_code)
        } $(else if $self.eat_string_if($name).is_some() {
            Some($code)
        })* else {
             None
        }
    }
}

impl<'a> Lexer<'a> {
    pub(super) fn new(input: &'a str) -> Self {
        debug_assert!(input.is_ascii());

        Self {
            input: input.as_bytes(),
            peek: None,
            cur: 0,
            line: 1,
        }
    }

    pub(super) fn next_token(&mut self) -> Result<Option<WithLoc<Token<'a>>>> {
        self.peek_token()?;
        Ok(self.peek.take())
    }

    pub(super) fn peek_token(&mut self) -> Result<Option<&WithLoc<Token<'a>>>> {
        if self.peek.is_some() {
            return Ok(self.peek.as_ref());
        }

        while let Some(c) = self.eat_char_if(|c| c.is_whitespace() || c.is_ascii_control()) {
            if c == '\n' {
                self.line += 1;
            }
        }

        if self.peek_char().is_none() {
            return Ok(None);
        }

        let token = if self.eat_char_if(|c| c == ':').is_some() {
            Token::Colon
        } else if self.eat_char_if(|c| c == ';').is_some() {
            Token::SemiColon
        } else if self.eat_char_if(|c| c == ',').is_some() {
            Token::Comma
        } else if self.eat_char_if(|c| c == '(').is_some() {
            Token::LParen
        } else if self.eat_char_if(|c| c == ')').is_some() {
            Token::RParen
        } else if self.eat_char_if(|c| c == '[').is_some() {
            Token::LBracket
        } else if self.eat_char_if(|c| c == ']').is_some() {
            Token::RBracket
        } else if self.eat_char_if(|c| c == '=').is_some() {
            Token::Eq
        } else if self.eat_char_if(|c| c == '.').is_some() {
            Token::Dot
        } else if self.eat_char_if(|c| c == '*').is_some() {
            Token::Star
        } else if self.eat_char_if(|c| c == '@').is_some() {
            let loc = if self.eat_string_if(b"memory").is_some() {
                DataLocationKind::Memory
            } else if self.eat_string_if(b"storage").is_some() {
                DataLocationKind::Storage
            } else {
                return Err(self.invalid_token());
            };
            Token::DataLocationKind(loc)
        } else if self.eat_char_if(|c| c == '#').is_some() {
            let is_module = self.eat_char_if(|c| c == '!').is_some();
            let start = self.cur;
            while self.eat_char_if(|c| c != '\n').is_some() {}
            let end = self.cur;
            let comment = self.from_raw_parts(start, end);
            if is_module {
                Token::ModuleComment(comment)
            } else {
                Token::FuncComment(comment)
            }
        } else if self.eat_char_if(|c| c == '%').is_some() {
            if let Some(ident) = self.try_eat_ident() {
                Token::Ident(ident)
            } else {
                return Err(self.invalid_token());
            }
        } else if self.eat_char_if(|c| c == '"').is_some() {
            self.eat_string_lit()?
        } else if self.eat_string_if(b"target").is_some() {
            Token::Target
        } else if self.eat_string_if(b"func").is_some() {
            Token::Func
        } else if self.eat_string_if(b"declare").is_some() {
            Token::Declare
        } else if self.eat_string_if(b"public").is_some() {
            Token::Linkage(Linkage::Public)
        } else if self.eat_string_if(b"private").is_some() {
            Token::Linkage(Linkage::Private)
        } else if self.eat_string_if(b"external").is_some() {
            Token::Linkage(Linkage::External)
        } else if self.eat_string_if(b"undef").is_some() {
            Token::Undef
        } else if self.eat_string_if(b"->").is_some() {
            Token::RArrow
        } else if let Some(code) = self.try_eat_opcode() {
            Token::OpCode(code)
        } else if let Some(ty) = self.try_eat_base_ty() {
            Token::BaseTy(ty)
        } else if self.eat_string_if(b"block").is_some() {
            if let Some(id) = self.try_eat_id() {
                Token::Block(id)
            } else {
                return Err(self.invalid_token());
            }
        } else if self.eat_string_if(b"v").is_some() {
            if let Some(id) = self.try_eat_id() {
                Token::Value(id)
            } else {
                return Err(self.invalid_token());
            }
        } else if let Some(integer) = self.try_eat_integer() {
            Token::Integer(integer)
        } else {
            return Err(self.invalid_token());
        };

        self.peek = Some(WithLoc {
            item: token,
            line: self.line,
        });
        Ok(self.peek.as_ref())
    }

    pub(super) fn line(&mut self) -> u32 {
        self.line
    }

    fn eat_char_if(&mut self, f: impl FnOnce(char) -> bool) -> Option<char> {
        match self.peek_char() {
            Some(peek) if f(peek) => {
                self.next_char();
                Some(peek)
            }
            _ => None,
        }
    }

    fn eat_string_if(&mut self, s: &[u8]) -> Option<&'a str> {
        let start = self.cur;
        let mut cur = self.cur;
        for i in s {
            if *i == self.input[cur] {
                cur += 1;
            } else {
                return None;
            }
        }

        self.cur = cur;
        Some(self.from_raw_parts(start, cur))
    }

    fn eat_string_lit(&mut self) -> Result<Token<'a>> {
        let start = self.cur;
        let mut cur = self.cur;
        loop {
            match self.input.get(cur) {
                Some(c) => {
                    if *c == b'"' {
                        self.cur = cur + 1;
                        break;
                    } else {
                        cur += 1;
                    }
                }
                None => {
                    return Err(Error::new(
                        ErrorKind::SyntaxError("missing closing `\"`".into()),
                        self.line,
                    ))
                }
            }
        }

        Ok(Token::String(self.from_raw_parts(start, cur)))
    }

    fn try_eat_opcode(&mut self) -> Option<Code> {
        try_eat_variant! {
            self,
            (b"not", Code::Not),
            (b"neg", Code::Neg),
            (b"add", Code::Add),
            (b"sub", Code::Sub),
            (b"mul", Code::Mul),
            (b"udiv", Code::Udiv),
            (b"sdiv", Code::Sdiv),
            (b"lt", Code::Lt),
            (b"gt", Code::Gt),
            (b"slt", Code::Slt),
            (b"sgt", Code::Sgt),
            (b"le", Code::Le),
            (b"ge", Code::Ge),
            (b"sle", Code::Sle),
            (b"sge", Code::Sge),
            (b"eq", Code::Eq),
            (b"ne", Code::Ne),
            (b"and", Code::And),
            (b"or", Code::Or),
            (b"xor", Code::Xor),
            (b"sext", Code::Sext),
            (b"zext", Code::Zext),
            (b"trunc", Code::Trunc),
            (b"load", Code::Load),
            (b"store", Code::Store),
            (b"call", Code::Call),
            (b"jump", Code::Jump),
            (b"fallthrough", Code::FallThrough),
            (b"br_table", Code::BrTable),
            (b"br", Code::Br),
            (b"alloca", Code::Alloca),
            (b"return", Code::Return),
            (b"phi", Code::Phi),
        }
    }

    fn try_eat_base_ty(&mut self) -> Option<Type> {
        try_eat_variant! {
            self,
            (b"i8", Type::I8),
            (b"i16", Type::I16),
            (b"i32", Type::I32),
            (b"i64", Type::I64),
            (b"i128", Type::I128),
            (b"i256", Type::I256),
            (b"i1", Type::I1),
            (b"void", Type::Void),
        }
    }

    fn try_eat_id(&mut self) -> Option<u32> {
        let start = self.cur;
        while self.eat_char_if(|c| c.is_digit(10)).is_some() {}
        let end = self.cur;
        self.from_raw_parts(start, end).parse().ok()
    }

    fn try_eat_ident(&mut self) -> Option<&'a str> {
        let start = self.cur;
        while self
            .eat_char_if(|c| c.is_alphanumeric() || c == '_')
            .is_some()
        {}
        let end = self.cur;
        if start == end {
            None
        } else {
            Some(self.from_raw_parts(start, end))
        }
    }

    fn try_eat_integer(&mut self) -> Option<&'a str> {
        let start = self.cur;
        self.eat_char_if(|c| c == '-');
        while self.eat_char_if(|c| c.is_digit(10)).is_some() {}
        let end = self.cur;

        if start == end {
            None
        } else {
            Some(self.from_raw_parts(start, end))
        }
    }

    fn next_char(&mut self) -> Option<char> {
        let next = self.peek_char();
        self.cur += 1;
        next
    }

    fn peek_char(&mut self) -> Option<char> {
        self.input.get(self.cur).map(|peek| *peek as char)
    }

    fn from_raw_parts(&self, start: usize, end: usize) -> &'a str {
        unsafe { std::str::from_utf8_unchecked(&self.input[start..end]) }
    }

    fn invalid_token(&mut self) -> Error {
        let start = self.cur;
        while self
            .eat_char_if(|c| !c.is_whitespace() && !c.is_ascii_control())
            .is_some()
        {}
        let end = self.cur;
        let invalid_token = self.from_raw_parts(start, end);
        Error::new(
            ErrorKind::InvalidToken(invalid_token.to_string()),
            self.line,
        )
    }
}

#[derive(Debug, Clone)]
pub(super) struct WithLoc<T> {
    pub(super) item: T,
    pub(super) line: u32,
}

#[derive(Debug, Clone)]
pub(super) enum Token<'a> {
    Func,
    Declare,
    Linkage(Linkage),
    RArrow,
    Colon,
    SemiColon,
    Comma,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Eq,
    Dot,
    Star,
    Undef,
    Target,
    ModuleComment(&'a str),
    FuncComment(&'a str),
    Block(u32),
    Value(u32),
    Ident(&'a str),
    String(&'a str),
    DataLocationKind(DataLocationKind),
    OpCode(Code),
    BaseTy(Type),
    Integer(&'a str),
}

impl<'a> Token<'a> {
    pub(super) fn id(&self) -> u32 {
        match self {
            Self::Block(id) | Self::Value(id) => *id,
            _ => unreachable!(),
        }
    }

    pub(super) fn string(&self) -> &'a str {
        match self {
            Self::ModuleComment(s)
            | Self::FuncComment(s)
            | Self::Ident(s)
            | Self::Integer(s)
            | Self::String(s) => s,
            _ => unreachable!(),
        }
    }

    pub(super) fn opcode(&self) -> Code {
        if let Self::OpCode(code) = self {
            *code
        } else {
            unreachable!()
        }
    }

    pub(super) fn ty(&self) -> &Type {
        if let Self::BaseTy(ty) = self {
            ty
        } else {
            unreachable!()
        }
    }
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Func => write!(w, "func"),
            Self::Declare => write!(w, "declare"),
            Self::Linkage(linkage) => write!(w, "{}", linkage),
            Self::RArrow => write!(w, "=>"),
            Self::Colon => write!(w, ":"),
            Self::SemiColon => write!(w, ";"),
            Self::Comma => write!(w, ","),
            Self::LParen => write!(w, "("),
            Self::RParen => write!(w, ")"),
            Self::LBracket => write!(w, "["),
            Self::RBracket => write!(w, "]"),
            Self::Eq => write!(w, "="),
            Self::DataLocationKind(loc) => {
                write!(w, "@")?;

                match loc {
                    DataLocationKind::Memory => write!(w, "memory"),
                    DataLocationKind::Storage => write!(w, "storage"),
                }
            }
            Self::Dot => write!(w, "."),
            Self::Star => write!(w, "*"),
            Self::Undef => write!(w, "undef"),
            Self::Target => write!(w, "target"),
            Self::String(s) => write!(w, "{}", s),
            Self::ModuleComment(comment) => write!(w, "#!{}", comment),
            Self::FuncComment(comment) => write!(w, "#{}", comment),
            Self::Block(id) => write!(w, "block{}", id),
            Self::Value(id) => write!(w, "v{}", id),
            Self::Ident(ident) => write!(w, "%{}", ident),
            Self::OpCode(code) => write!(w, "{}", code),
            Self::BaseTy(ty) => write!(w, "{}", ty),
            Self::Integer(num) => w.write_str(num),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum Code {
    // Unary ops.
    Not,
    Neg,

    // Binary ops.
    Add,
    Sub,
    Mul,
    Udiv,
    Sdiv,
    Lt,
    Gt,
    Slt,
    Sgt,
    Le,
    Ge,
    Sle,
    Sge,
    Eq,
    Ne,
    And,
    Or,
    Xor,

    // Cast ops.
    Sext,
    Zext,
    Trunc,

    Load,
    Store,

    // Function Call ops.
    Call,

    // Jump ops.
    Jump,
    FallThrough,

    // Branch ops.
    Br,
    BrTable,

    Alloca,

    Return,

    Phi,
}

impl fmt::Display for Code {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        use Code::*;

        let s = match self {
            Not => "not",
            Neg => "neg",
            Add => "add",
            Sub => "sub",
            Mul => "mul",
            Udiv => "udiv",
            Sdiv => "sdiv",
            Lt => "lt",
            Gt => "gt",
            Slt => "slt",
            Sgt => "sgt",
            Le => "le",
            Ge => "ge",
            Sle => "sle",
            Sge => "sge",
            Eq => "eq",
            Ne => "ne",
            And => "and",
            Or => "or",
            Xor => "xor",
            Sext => "sext",
            Zext => "zext",
            Trunc => "trunc",
            Load => "load",
            Store => "store",
            Call => "call",
            Jump => "jump",
            FallThrough => "fallthrough",
            Alloca => "alloca",
            Br => "br",
            BrTable => "br_table",
            Return => "return",
            Phi => "phi",
        };

        w.write_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_with_return() {
        let input = "func private %test_func() -> i32, i64:
    block0:
        return 311.i32 -120.i64;";
        let mut lexer = Lexer::new(input);

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Func
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Linkage(Linkage::Private),
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Ident("test_func")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::LParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::RParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::RArrow
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I32)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Comma
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Block(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::OpCode(Code::Return)
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Integer("311")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I32)
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Integer("-120")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I64)
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::SemiColon
        ));

        assert!(lexer.next_token().unwrap().is_none());
    }

    #[test]
    fn lexer_with_arg() {
        let input = "func public %test_func(i32, i64):
    block0:
        v2.i64 = sext v0;
        v3.i64 = mul v2 v1;
        return;
";
        let mut lexer = Lexer::new(input);
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Func
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Linkage(Linkage::Public)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Ident("test_func")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::LParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I32)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Comma
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::RParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Block(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Value(2)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Eq
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::OpCode(Code::Sext)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Value(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::SemiColon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Value(3)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::BaseTy(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Eq
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::OpCode(Code::Mul)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Value(2)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::Value(1)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::SemiColon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::OpCode(Code::Return)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Token::SemiColon
        ));

        assert!(lexer.next_token().unwrap().is_none());
    }
}
