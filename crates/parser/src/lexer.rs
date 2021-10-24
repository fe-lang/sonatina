use sonatina_codegen::ir::Type;

pub(super) struct Lexer<'a> {
    input: &'a [u8],
    peek: Option<Token<'a>>,
    cur: usize,
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
        pub(super) fn $fn_name(&mut self) -> Option<$ret_ty> {
            match self.peek_token() {
                Some($variant(_)) => match self.next_token().unwrap() {
                    $variant(data) => Some(data),
                    _ => unreachable!(),
                },
                _ => None,
            }
        }
    };

    ($fn_name:ident, $variant:path) => {
        pub(super) fn $fn_name(&mut self) -> Option<()> {
            match self.peek_token() {
                Some($variant) => {
                    self.next_token();
                    Some(())
                }
                _ => None,
            }
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
        }
    }

    pub(super) fn next_token(&mut self) -> Option<Token<'a>> {
        self.peek_token();
        self.peek.take()
    }

    pub(super) fn peek_token(&mut self) -> Option<&Token<'a>> {
        if self.peek.is_some() {
            return self.peek.as_ref();
        }

        while self
            .eat_char_if(|c| c.is_whitespace() || c.is_ascii_control())
            .is_some()
        {}

        if self.peek_char().is_none() {
            return None;
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
        } else if self.eat_char_if(|c| c == '%').is_some() {
            let ident = self.try_eat_ident().unwrap();
            Token::Ident(ident)
        } else if self.eat_string_if(b"func").is_some() {
            Token::Func
        } else if self.eat_string_if(b"->").is_some() {
            Token::RArrow
        } else if let Some(code) = self.try_eat_opcode() {
            Token::OpCode(code)
        } else if let Some(ty) = self.try_eat_ty() {
            Token::Ty(ty)
        } else if self.eat_string_if(b"block").is_some() {
            let id = self.try_eat_id().unwrap();
            Token::Block(id)
        } else if self.eat_string_if(b"v").is_some() {
            let id = self.try_eat_id().unwrap();
            self.eat_char_if(|c| c == '.').unwrap();
            let ty = self.try_eat_ty().unwrap();
            Token::Value(ValueData::new(id, ty))
        } else if let Some(integer) = self.try_eat_integer() {
            Token::Integer(integer)
        } else {
            let start = self.cur;
            while self
                .eat_char_if(|c| !c.is_whitespace() && !c.is_ascii_control())
                .is_some()
            {}
            let end = self.cur;
            let unexpected_token = self.from_raw_parts(start, end);
            panic!("unexpected token: {}", unexpected_token);
        };

        self.peek = Some(token);
        self.peek.as_ref()
    }

    impl_next_token_kind!(next_func, Token::Func);
    impl_next_token_kind!(next_right_arrow, Token::RArrow);
    impl_next_token_kind!(next_colon, Token::Colon);
    impl_next_token_kind!(next_semicolon, Token::SemiColon);
    impl_next_token_kind!(next_comma, Token::Comma);
    impl_next_token_kind!(next_lparen, Token::LParen);
    impl_next_token_kind!(next_rparen, Token::RParen);
    impl_next_token_kind!(next_eq, Token::Eq);

    impl_next_token_kind!(next_block, Token::Block, u32);
    impl_next_token_kind!(next_value, Token::Value, ValueData);
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
            (b"div",Code::Div),
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
            (b"brz", Code::Brz),
            (b"brnz", Code::Brnz),
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
            (b"bool", Type::Bool),
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
    Block(u32),
    Value(ValueData),
    Ident(&'a str),
    OpCode(Code),
    Ty(Type),
    Integer(&'a str),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ValueData {
    pub id: u32,
    pub ty: Type,
}

impl ValueData {
    fn new(id: u32, ty: Type) -> Self {
        Self { id, ty }
    }
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
    Div,
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
    Brz,
    Brnz,

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
        return v0.i32 v1.i64;";
        let mut lexer = Lexer::new(&input);

        assert!(matches!(lexer.next_token().unwrap(), Func));
        assert!(matches!(lexer.next_token().unwrap(), Ident("test_func")));
        assert!(matches!(lexer.next_token().unwrap(), LParen));
        assert!(matches!(lexer.next_token().unwrap(), RParen));
        assert!(matches!(lexer.next_token().unwrap(), RArrow));
        assert!(matches!(lexer.next_token().unwrap(), Ty(Type::I32)));
        assert!(matches!(lexer.next_token().unwrap(), Comma));
        assert!(matches!(lexer.next_token().unwrap(), Ty(Type::I64)));
        assert!(matches!(lexer.next_token().unwrap(), Colon));

        assert!(matches!(lexer.next_token().unwrap(), Block(0)));
        assert!(matches!(lexer.next_token().unwrap(), Colon));

        assert_eq!(lexer.next_value().unwrap(), ValueData::new(0, Type::I32));
        assert!(matches!(lexer.next_token().unwrap(), Eq));
        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::ImmI32)));
        assert!(matches!(lexer.next_token().unwrap(), Integer("311")));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert_eq!(lexer.next_value().unwrap(), ValueData::new(1, Type::I64));
        assert!(matches!(lexer.next_token().unwrap(), Eq));
        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::ImmI64)));
        assert!(matches!(lexer.next_token().unwrap(), Integer("120")));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::Return)));
        assert_eq!(lexer.next_value().unwrap(), ValueData::new(0, Type::I32));
        assert_eq!(lexer.next_value().unwrap(), ValueData::new(1, Type::I64));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert!(lexer.next_token().is_none());
    }

    #[test]
    fn lexer_with_arg() {
        let input = "func %test_func(i32, i64):
    block0:
        v2.i64 = sext v0.i32;
        v3.i64 = mul v2.i64 v1.i64;
        return;
";
        let mut lexer = Lexer::new(&input);
        assert!(matches!(lexer.next_token().unwrap(), Func));
        assert!(matches!(lexer.next_token().unwrap(), Ident("test_func")));
        assert!(matches!(lexer.next_token().unwrap(), LParen));
        assert!(matches!(lexer.next_token().unwrap(), Ty(Type::I32)));
        assert!(matches!(lexer.next_token().unwrap(), Comma));
        assert!(matches!(lexer.next_token().unwrap(), Ty(Type::I64)));
        assert!(matches!(lexer.next_token().unwrap(), RParen));
        assert!(matches!(lexer.next_token().unwrap(), Colon));

        assert!(matches!(lexer.next_token().unwrap(), Block(0)));
        assert!(matches!(lexer.next_token().unwrap(), Colon));

        assert_eq!(lexer.next_value().unwrap(), ValueData::new(2, Type::I64));
        assert!(matches!(lexer.next_token().unwrap(), Eq));
        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::Sext)));
        assert_eq!(lexer.next_value().unwrap(), ValueData::new(0, Type::I32));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert_eq!(lexer.next_value().unwrap(), ValueData::new(3, Type::I64));
        assert!(matches!(lexer.next_token().unwrap(), Eq));
        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::Mul)));
        assert_eq!(lexer.next_value().unwrap(), ValueData::new(2, Type::I64));
        assert_eq!(lexer.next_value().unwrap(), ValueData::new(1, Type::I64));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::Return)));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert!(lexer.next_token().is_none());
    }

    #[test]
    fn lexer_with_array_ty() {
        let input = "func %test_func([i32;4], [[i128;3];4]):
    block0:
        return;";
        let mut lexer = Lexer::new(&input);

        assert!(matches!(lexer.next_token().unwrap(), Func));
        assert!(matches!(lexer.next_token().unwrap(), Ident("test_func")));
        assert!(matches!(lexer.next_token().unwrap(), LParen));
        assert!(
            matches!(lexer.next_token().unwrap(), Ty(ty) if ty == Type::make_array(Type::I32, 4))
        );
        assert!(matches!(lexer.next_token().unwrap(), Comma));
        assert!(
            matches!(lexer.next_token().unwrap(), Ty(ty) if ty == Type::make_array(Type::make_array(Type::I128, 3), 4))
        );
        assert!(matches!(lexer.next_token().unwrap(), RParen));
        assert!(matches!(lexer.next_token().unwrap(), Colon));

        assert!(matches!(lexer.next_token().unwrap(), Block(0)));
        assert!(matches!(lexer.next_token().unwrap(), Colon));
        assert!(matches!(lexer.next_token().unwrap(), OpCode(Code::Return)));
        assert!(matches!(lexer.next_token().unwrap(), SemiColon));

        assert!(lexer.next_token().is_none());
    }
}
