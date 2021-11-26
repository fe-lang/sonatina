use std::fmt;

use sonatina_codegen::ir::Type;

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
        } else if self.eat_char_if(|c| c == '=').is_some() {
            Token::Eq
        } else if self.eat_char_if(|c| c == '.').is_some() {
            Token::Dot
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
        } else if self.eat_string_if(b"func").is_some() {
            Token::Func
        } else if self.eat_string_if(b"->").is_some() {
            Token::RArrow
        } else if let Some(code) = self.try_eat_opcode() {
            Token::OpCode(code)
        } else if let Some(ty) = self.try_eat_ty() {
            Token::Ty(ty)
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

    fn try_eat_opcode(&mut self) -> Option<Code> {
        try_eat_variant! {
            self,
            (b"not", Code::Not),
            (b"add", Code::Add),
            (b"sub", Code::Sub),
            (b"mul", Code::Mul),
            (b"udiv", Code::UDiv),
            (b"sdiv", Code::SDiv),
            (b"lt", Code::Lt),
            (b"gt", Code::Gt),
            (b"slt", Code::Slt),
            (b"sgt", Code::Sgt),
            (b"eq", Code::Eq),
            (b"and", Code::And),
            (b"or", Code::Or),
            (b"sext", Code::Sext),
            (b"zext", Code::Zext),
            (b"trunc", Code::Trunc),
            (b"load", Code::Load),
            (b"store", Code::Store),
            (b"jump", Code::Jump),
            (b"fallthrough", Code::FallThrough),
            (b"br", Code::Br),
            (b"return", Code::Return),
            (b"phi", Code::Phi),
        }
    }

    fn try_eat_ty(&mut self) -> Option<Type> {
        let base = try_eat_variant! {
            self,
            (b"i8", Type::I8),
            (b"i16", Type::I16),
            (b"i32", Type::I32),
            (b"i64", Type::I64),
            (b"i128", Type::I128),
            (b"i256", Type::I256),
        };

        if base.is_none() && self.eat_char_if(|c| c == '[').is_some() {
            let ty = self.try_eat_ty().unwrap();
            self.eat_char_if(|c| c == ';').unwrap();
            let len = self.try_eat_integer().unwrap().parse().unwrap();
            self.eat_char_if(|c| c == ']').unwrap();
            Some(Type::make_array(ty, len))
        } else {
            base
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
    RArrow,
    Colon,
    SemiColon,
    Comma,
    LParen,
    RParen,
    Eq,
    Dot,
    ModuleComment(&'a str),
    FuncComment(&'a str),
    Block(u32),
    Value(u32),
    Ident(&'a str),
    OpCode(Code),
    Ty(Type),
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
            Self::ModuleComment(s) | Self::FuncComment(s) | Self::Ident(s) | Self::Integer(s) => s,
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
        if let Self::Ty(ty) = self {
            ty
        } else {
            unreachable!()
        }
    }
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;

        match self {
            Func => w.write_str("func"),
            RArrow => w.write_str("=>"),
            Colon => w.write_str(":"),
            SemiColon => w.write_str(";"),
            Comma => w.write_str(","),
            LParen => w.write_str("("),
            RParen => w.write_str(")"),
            Eq => w.write_str("="),
            Dot => w.write_str("."),
            ModuleComment(comment) => write!(w, "#!{}", comment),
            FuncComment(comment) => write!(w, "#{}", comment),
            Block(id) => write!(w, "block{}", id),
            Value(id) => write!(w, "v{}", id),
            Ident(ident) => write!(w, "%{}", ident),
            OpCode(code) => write!(w, "{}", code),
            Ty(ty) => write!(w, "{}", ty),
            Integer(num) => w.write_str(num),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum Code {
    // Unary ops.
    Not,

    // Binary ops.
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    Lt,
    Gt,
    Slt,
    Sgt,
    Eq,
    And,
    Or,

    // Cast ops.
    Sext,
    Zext,
    Trunc,

    Load,
    Store,

    // Jump ops.
    Jump,
    FallThrough,

    // Branch ops.
    Br,

    Return,

    Phi,
}

impl fmt::Display for Code {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        use Code::*;

        let s = match self {
            Not => "not",
            Add => "add",
            Sub => "sub",
            Mul => "mul",
            UDiv => "udiv",
            SDiv => "sdiv",
            Lt => "lt",
            Gt => "gt",
            Slt => "slt",
            Sgt => "sgt",
            Eq => "eq",
            And => "and",
            Or => "or",
            Sext => "sext",
            Zext => "zext",
            Trunc => "trunc",
            Load => "load",
            Store => "store",
            Jump => "jump",
            FallThrough => "fallthrough",
            Br => "br",
            Return => "return",
            Phi => "phi",
        };

        w.write_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use Token::*;

    #[test]
    fn lexer_with_return() {
        let input = "func %test_func() -> i32, i64:
    block0:
        return 311.i32 -120.i64;";
        let mut lexer = Lexer::new(input);

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Func
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ident("test_func")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            LParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            RParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            RArrow
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I32)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Comma
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Block(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            OpCode(Code::Return)
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Integer("311")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I32)
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Integer("-120")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I64)
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            SemiColon
        ));

        assert!(lexer.next_token().unwrap().is_none());
    }

    #[test]
    fn lexer_with_arg() {
        let input = "func %test_func(i32, i64):
    block0:
        v2.i64 = sext v0;
        v3.i64 = mul v2 v1;
        return;
";
        let mut lexer = Lexer::new(input);
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Func
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ident("test_func")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            LParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I32)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Comma
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            RParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Block(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(2)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Eq
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            OpCode(Code::Sext)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            SemiColon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(3)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Dot
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ty(Type::I64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Eq
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            OpCode(Code::Mul)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(2)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(1)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            SemiColon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            OpCode(Code::Return)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            SemiColon
        ));

        assert!(lexer.next_token().unwrap().is_none());
    }

    #[test]
    fn lexer_with_array_ty() {
        let input = "func %test_func([i32;4], [[i128;3];4]):
    block0:
        return;";
        let mut lexer = Lexer::new(input);

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Func
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Ident("test_func")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            LParen
        ));
        assert!(
            matches!(lexer.next_token().ok().flatten().unwrap().item, Ty(ty) if ty == Type::make_array(Type::I32, 4))
        );
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Comma
        ));
        assert!(
            matches!(lexer.next_token().ok().flatten().unwrap().item, Ty(ty) if ty == Type::make_array(Type::make_array(Type::I128, 3), 4))
        );
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            RParen
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Colon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Block(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Colon
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            OpCode(Code::Return)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            SemiColon
        ));

        assert!(lexer.next_token().unwrap().is_none());
    }
}
