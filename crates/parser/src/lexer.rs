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

macro_rules! impl_next_token_kind {
    ($fn_name:ident, $variant:path, $ret_ty:ty) => {
        pub(super) fn $fn_name(&mut self) -> Result<Option<WithLoc<$ret_ty>>> {
            Ok(match self.peek_token()? {
                Some(WithLoc {
                    item: $variant(_),
                    line,
                }) => match self.next_token()?.unwrap().item {
                    $variant(data) => Some(WithLoc {
                        item: data,
                        line: *line,
                    }),
                    _ => None,
                },
                _ => None,
            })
        }
    };

    ($fn_name:ident, $variant:path) => {
        pub(super) fn $fn_name(&mut self) -> Result<Option<WithLoc<()>>> {
            Ok(match self.peek_token()? {
                Some(WithLoc { line, .. }) => {
                    self.next_token()?;
                    Some(WithLoc {
                        item: (),
                        line: *line,
                    })
                }
                _ => None,
            })
        }
    };
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
            let start = self.cur;
            while self
                .eat_char_if(|c| !c.is_whitespace() && !c.is_ascii_control())
                .is_some()
            {}
            let end = self.cur;
            let invalid_token = self.from_raw_parts(start, end);
            return Err(Error::new(
                ErrorKind::InvalidToken(invalid_token),
                self.line,
            ));
        };

        self.peek = Some(WithLoc {
            item: token,
            line: self.line,
        });
        Ok(self.peek.as_ref())
    }

    impl_next_token_kind!(next_func, Token::Func);
    impl_next_token_kind!(next_right_arrow, Token::RArrow);
    impl_next_token_kind!(next_colon, Token::Colon);
    impl_next_token_kind!(next_semicolon, Token::SemiColon);
    impl_next_token_kind!(next_comma, Token::Comma);
    impl_next_token_kind!(next_lparen, Token::LParen);
    impl_next_token_kind!(next_rparen, Token::RParen);
    impl_next_token_kind!(next_eq, Token::Eq);
    impl_next_token_kind!(next_dot, Token::Dot);
    impl_next_token_kind!(next_module_comment, Token::ModuleComment, &'a str);
    impl_next_token_kind!(next_func_comment, Token::FuncComment, &'a str);

    impl_next_token_kind!(next_block, Token::Block, u32);
    impl_next_token_kind!(next_value, Token::Value, u32);
    impl_next_token_kind!(next_opcode, Token::OpCode, Code);
    impl_next_token_kind!(next_ident, Token::Ident, &'a str);
    impl_next_token_kind!(next_ty, Token::Ty, Type);
    impl_next_token_kind!(next_integer, Token::Integer, &'a str);

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
            (b"imm_i8", Code::ImmI8),
            (b"imm_i16", Code::ImmI16),
            (b"imm_i32", Code::ImmI32),
            (b"imm_i64", Code::ImmI64),
            (b"imm_i128", Code::ImmI128),
            (b"imm_u8", Code::ImmU8),
            (b"imm_u16", Code::ImmU16),
            (b"imm_u32", Code::ImmU32),
            (b"imm_u64", Code::ImmU64),
            (b"imm_u128", Code::ImmU128),
            (b"imm_u256", Code::ImmU256),
            (b"add",Code::Add),
            (b"sub",Code::Sub),
            (b"mul",Code::Mul),
            (b"udiv",Code::UDiv),
            (b"sdiv",Code::SDiv),
            (b"lt",Code::Lt),
            (b"gt",Code::Gt),
            (b"slt",Code::Slt),
            (b"sgt",Code::Sgt),
            (b"eq",Code::Eq),
            (b"and",Code::And),
            (b"or",Code::Or),
            (b"sext",Code::Sext),
            (b"zext",Code::Zext),
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
        Error::new(ErrorKind::InvalidToken(invalid_token), self.line)
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

#[derive(Debug, Clone, Copy)]
pub(super) enum Code {
    // Immediate ops.
    ImmI8,
    ImmI16,
    ImmI32,
    ImmI64,
    ImmI128,
    ImmU8,
    ImmU16,
    ImmU32,
    ImmU64,
    ImmU128,
    ImmU256,

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

#[cfg(test)]
mod tests {
    use super::*;

    use Token::*;

    #[test]
    fn lexer_with_return() {
        let input = "func %test_func() -> i32, i64:
    block0:
        v0.i32 = imm_i32 311;
        v1.i64 = imm_i64 120;
        return v0 v1;";
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
            Value(0)
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
            Eq
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            OpCode(Code::ImmI32)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Integer("311")
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            SemiColon
        ));

        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(1)
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
            OpCode(Code::ImmI64)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Integer("120")
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
            Value(0)
        ));
        assert!(matches!(
            lexer.next_token().ok().flatten().unwrap().item,
            Value(1)
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
