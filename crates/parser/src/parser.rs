use std::collections::HashSet;

use sonatina_codegen::ir::{
    func_cursor::{CursorLocation, FuncCursor},
    insn::{BinaryOp, CastOp, ImmediateOp, JumpOp},
    Block, BlockData, Function, Insn, InsnData, Signature, Type, Value, ValueData,
};

use super::lexer::{Code, Lexer, Token, WithLoc};
use super::{Error, ErrorKind, Result};

pub struct Parser {}

impl Parser {
    pub fn parse(input: &str) -> Result<ParsedModule> {
        let mut lexer = Lexer::new(input);

        let mut comments = Vec::new();
        while let Some(WithLoc {
            item: Token::ModuleComment(comment),
            ..
        }) = lexer.peek_token()?
        {
            comments.push(comment.to_string());
            lexer.next_token()?;
        }

        let mut funcs = Vec::new();
        while let Some(func) = FuncParser::new(&mut lexer).parse()? {
            funcs.push(func);
        }

        Ok(ParsedModule { comments, funcs })
    }
}

// TODO: Reconsider module design when IR define module.
pub struct ParsedModule {
    pub comments: Vec<String>,
    pub funcs: Vec<ParsedFunction>,
}

pub struct ParsedFunction {
    pub comments: Vec<String>,
    pub func: Function,
}

struct FuncParser<'a, 'b> {
    lexer: &'b mut Lexer<'a>,
}

macro_rules! eat_token {
    ($self:ident, $token:pat) => {
        if matches!(
            $self.lexer.peek_token()?,
            Some(WithLoc { item: $token, .. })
        ) {
            Ok(Some($self.lexer.next_token()?.unwrap().item))
        } else {
            Ok(None)
        }
    };
}

macro_rules! expect_token {
    ($self:ident, $token:pat, $expected:expr) => {
        if let Some(tok) = eat_token!($self, $token)? {
            Ok(tok)
        } else {
            let (tok, line) = match $self.lexer.next_token()? {
                Some(tok) => ((tok.item.to_string(), tok.line)),
                None => (("EOF".to_string(), $self.lexer.line())),
            };
            Err(Error::new(
                ErrorKind::SyntaxError(format!("expected `{}`, but got `{}`", $expected, tok)),
                line,
            ))
        }
    };
}

impl<'a, 'b> FuncParser<'a, 'b> {
    fn new(lexer: &'b mut Lexer<'a>) -> Self {
        Self { lexer }
    }

    fn parse(&mut self) -> Result<Option<ParsedFunction>> {
        if self.lexer.peek_token()?.is_none() {
            return Ok(None);
        }

        let comments = self.parse_comment()?;
        expect_token!(self, Token::Func, "func")?;

        let fn_name = expect_token!(self, Token::Ident(..), "func name")?.string();

        expect_token!(self, Token::LParen, "(")?;
        let mut func = Function::new(fn_name.to_string(), Signature::default());
        let mut inserter = InsnInserter::new(&mut func);

        if let Some(value) = eat_token!(self, Token::Value(..))? {
            let value = Value(value.id());
            inserter.def_value(value, self.lexer.line())?;
            expect_token!(self, Token::Dot, "dot")?;
            let ty = expect_token!(self, Token::Ty(..), "type")?.ty().clone();
            inserter.append_arg_value(value, ty);

            while eat_token!(self, Token::Comma)?.is_some() {
                let value = Value(expect_token!(self, Token::Value(..), "value")?.id());
                inserter.def_value(value, self.lexer.line())?;
                expect_token!(self, Token::Dot, "dot")?;
                let ty = expect_token!(self, Token::Ty(..), "type")?.ty().clone();
                inserter.append_arg_value(value, ty);
            }
        }
        expect_token!(self, Token::RParen, ")")?;

        if eat_token!(self, Token::RArrow)?.is_some() {
            let ty = expect_token!(self, Token::Ty(..), "type")?;
            inserter.func.sig.append_return(ty.ty().clone());
            while eat_token!(self, Token::Comma)?.is_some() {
                let ty = expect_token!(self, Token::Ty(..), "type")?;
                inserter.func.sig.append_return(ty.ty().clone());
            }
        }
        expect_token!(self, Token::Colon, ":")?;

        self.parse_body(&mut inserter)?;

        Ok(Some(ParsedFunction { comments, func }))
    }

    fn parse_body(&mut self, inserter: &mut InsnInserter) -> Result<()> {
        while let Some(id) = eat_token!(self, Token::Block(..))? {
            expect_token!(self, Token::Colon, ":")?;
            self.parse_block_body(inserter, Block(id.id()))?;
        }

        Ok(())
    }

    fn parse_block_body(&mut self, inserter: &mut InsnInserter, block: Block) -> Result<()> {
        inserter.def_block(block, self.lexer.line(), BlockData::default())?;
        inserter.append_block(block);
        inserter.set_loc(CursorLocation::BlockTop(block));

        loop {
            if let Some(value) = eat_token!(self, Token::Value(..))? {
                expect_token!(self, Token::Dot, ".")?;
                let ty = expect_token!(self, Token::Ty(..), "type")?.ty().clone();
                expect_token!(self, Token::Eq, "=")?;
                let opcode = expect_token!(self, Token::OpCode(..), "opcode")?.opcode();
                let insn_data = opcode.parse_args(self, Some(ty))?;
                let insn = inserter.insert_insn_data(insn_data);
                let value = Value(value.id());
                inserter.def_value(value, self.lexer.line())?;
                let result = inserter.func.dfg.make_result(insn).unwrap();
                inserter.func.dfg.values[value] = result;
                inserter.func.dfg.attach_result(insn, value);
            } else if let Some(opcode) = eat_token!(self, Token::OpCode(..))? {
                let insn_data = opcode.opcode().parse_args(self, None)?;
                inserter.insert_insn_data(insn_data);
            } else {
                break;
            }
        }

        Ok(())
    }

    fn expect_value(&mut self) -> Result<Value> {
        let id = expect_token!(self, Token::Value(..), "value")?.id();
        Ok(Value(id))
    }

    fn expect_block(&mut self) -> Result<Block> {
        let id = expect_token!(self, Token::Block(..), "block")?.id();
        Ok(Block(id))
    }

    fn parse_comment(&mut self) -> Result<Vec<String>> {
        let mut comments = Vec::new();
        while let Some(line) = eat_token!(self, Token::FuncComment(..))? {
            comments.push(line.string().to_string());
        }
        Ok(comments)
    }
}

struct InsnInserter<'a> {
    func: &'a mut Function,
    loc: CursorLocation,
    defined_values: HashSet<Value>,
    defined_blocks: HashSet<Block>,
}

impl<'a> InsnInserter<'a> {
    fn new(func: &'a mut Function) -> Self {
        Self {
            func,
            loc: CursorLocation::NoWhere,
            defined_values: HashSet::new(),
            defined_blocks: HashSet::new(),
        }
    }

    fn def_value(&mut self, value: Value, line: u32) -> Result<()> {
        if self.defined_values.contains(&value) {
            return Err(Error::new(
                ErrorKind::SemanticError(format!("v{} is already defined", value.0)),
                line,
            ));
        }
        self.defined_values.insert(value);

        let value_len = self.func.dfg.values.len();
        let value_id = value.0 as usize;

        if value_len <= value_id {
            self.func.dfg.values.reserve(value_id);
            for _ in 0..(value_id - value_len + 1) {
                // Make dummy value.
                self.func.dfg.values.push(ValueData::Arg {
                    ty: Type::I8,
                    idx: usize::MAX,
                });
            }
        }

        Ok(())
    }

    fn def_block(&mut self, block: Block, line: u32, block_data: BlockData) -> Result<()> {
        if self.defined_blocks.contains(&block) {
            return Err(Error::new(
                ErrorKind::SemanticError(format!("block{} is already defined", block.0)),
                line,
            ));
        }
        self.defined_blocks.insert(block);

        let block_id = block.0 as usize;
        let block_len = self.func.dfg.blocks.len();

        if block_len <= block_id {
            self.func.dfg.blocks.reserve(block_id);
            for _ in 0..(block_id - block_len + 1) {
                // Make dummy block.
                self.func.dfg.blocks.push(BlockData::default());
            }
        }

        self.func.dfg.blocks[block] = block_data;
        Ok(())
    }

    fn insert_insn_data(&mut self, insn_data: InsnData) -> Insn {
        let insn = self.func.dfg.make_insn(insn_data);
        self.insert_insn(insn);
        self.set_loc(CursorLocation::At(insn));
        insn
    }

    fn append_arg_value(&mut self, value: Value, ty: Type) {
        let idx = self.func.arg_values.len();

        let value_data = self.func.dfg.make_arg_value(&ty, idx);
        self.func.sig.append_arg(ty);
        self.func.dfg.values[value] = value_data;
        self.func.arg_values.push(value);
    }
}

impl<'a> FuncCursor for InsnInserter<'a> {
    fn set_loc(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    fn func(&self) -> &Function {
        self.func
    }

    fn func_mut(&mut self) -> &mut Function {
        &mut self.func
    }

    fn loc(&self) -> CursorLocation {
        self.loc
    }
}

macro_rules! make_immediate {
    ($parser:ident, $ty:ty, $code:path) => {{
        let imm = expect_token!($parser, Token::Integer(..), "integer literal")?.string();
        InsnData::Immediate {
            code: $code(imm.parse().unwrap()),
        }
    }};
}

macro_rules! make_binary {
    ($parser:ident, $code:path) => {{
        let lhs = $parser.expect_value()?;
        let rhs = $parser.expect_value()?;
        InsnData::Binary {
            code: $code,
            args: [lhs, rhs],
        }
    }};
}

macro_rules! make_cast {
    ($parser:ident, $cast_to:expr, $code:path) => {{
        let arg = $parser.expect_value()?;
        InsnData::Cast {
            code: $code,
            args: [arg],
            ty: $cast_to,
        }
    }};
}

macro_rules! make_jump {
    ($parser:ident, $code:path) => {{
        let dest = $parser.expect_block()?;
        InsnData::Jump {
            code: $code,
            dests: [dest],
        }
    }};
}

impl Code {
    /// Read args and create insn data.
    fn parse_args(self, parser: &mut FuncParser, ret_ty: Option<Type>) -> Result<InsnData> {
        let insn_data = match self {
            Self::ImmI8 => make_immediate!(parser, i8, ImmediateOp::I8),
            Self::ImmI16 => make_immediate!(parser, i16, ImmediateOp::I16),
            Self::ImmI32 => make_immediate!(parser, i32, ImmediateOp::I32),
            Self::ImmI64 => make_immediate!(parser, i64, ImmediateOp::I64),
            Self::ImmI128 => make_immediate!(parser, i128, ImmediateOp::I128),
            Self::ImmU8 => make_immediate!(parser, u8, ImmediateOp::U8),
            Self::ImmU16 => make_immediate!(parser, u16, ImmediateOp::U16),
            Self::ImmU32 => make_immediate!(parser, u32, ImmediateOp::U32),
            Self::ImmU64 => make_immediate!(parser, u64, ImmediateOp::U64),
            Self::ImmU128 => make_immediate!(parser, u128, ImmediateOp::U128),
            Self::ImmU256 => make_immediate!(parser, u256, ImmediateOp::U256),
            Self::Add => make_binary!(parser, BinaryOp::Add),
            Self::Sub => make_binary!(parser, BinaryOp::Sub),
            Self::Mul => make_binary!(parser, BinaryOp::Mul),
            Self::UDiv => make_binary!(parser, BinaryOp::UDiv),
            Self::SDiv => make_binary!(parser, BinaryOp::SDiv),
            Self::Lt => make_binary!(parser, BinaryOp::Lt),
            Self::Gt => make_binary!(parser, BinaryOp::Gt),
            Self::Slt => make_binary!(parser, BinaryOp::Slt),
            Self::Sgt => make_binary!(parser, BinaryOp::Sgt),
            Self::Eq => make_binary!(parser, BinaryOp::Eq),
            Self::And => make_binary!(parser, BinaryOp::And),
            Self::Or => make_binary!(parser, BinaryOp::Or),
            Self::Sext => make_cast!(parser, ret_ty.unwrap(), CastOp::Sext),
            Self::Zext => make_cast!(parser, ret_ty.unwrap(), CastOp::Zext),
            Self::Trunc => make_cast!(parser, ret_ty.unwrap(), CastOp::Trunc),
            Self::Load => {
                let arg = parser.expect_value()?;
                let ty = expect_token!(parser, Token::Ty(..), "type")?.ty().clone();
                InsnData::Load { args: [arg], ty }
            }
            Self::Store => {
                let lhs = parser.expect_value()?;
                let rhs = parser.expect_value()?;
                InsnData::Store { args: [lhs, rhs] }
            }
            Self::Jump => make_jump!(parser, JumpOp::Jump),
            Self::FallThrough => make_jump!(parser, JumpOp::FallThrough),
            Self::Br => {
                let cond = parser.expect_value()?;
                let then = parser.expect_block()?;
                let else_ = parser.expect_block()?;
                InsnData::Branch {
                    args: [cond],
                    dests: [then, else_],
                }
            }
            Self::Return => {
                let mut args = vec![];
                while let Some(value) = eat_token!(parser, Token::Value(..))? {
                    args.push(Value(value.id()));
                }
                InsnData::Return { args }
            }
            Self::Phi => {
                let mut values = vec![];
                let mut blocks = vec![];
                while eat_token!(parser, Token::LParen)?.is_some() {
                    let value = parser.expect_value()?;
                    values.push(value);
                    let block = parser.expect_block()?;
                    blocks.push(block);
                    expect_token!(parser, Token::RParen, ")")?;
                }
                InsnData::Phi {
                    values,
                    blocks,
                    ty: ret_ty.unwrap(),
                }
            }
        };

        expect_token!(parser, Token::SemiColon, ";")?;
        Ok(insn_data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use sonatina_codegen::ir::ir_writer::FuncWriter;

    fn test_parser(input: &str) -> bool {
        let module = Parser::parse(input).unwrap();
        let mut writer = FuncWriter::new(&module.funcs[0].func);

        println!("{}", writer.dump_string().unwrap());
        input.trim() == writer.dump_string().unwrap().trim()
    }

    #[test]
    fn parser_with_return() {
        assert!(test_parser(
            "func %test_func() -> i32, i64:
    block0:
        v0.i32 = imm_i32 311;
        v1.i64 = imm_i64 120;
        return v0 v1;"
        ));
    }

    #[test]
    fn test_with_arg() {
        assert!(test_parser(
            "func %test_func(v0.i32, v1.i64):
    block0:
        v2.i64 = sext v0;
        v3.i64 = mul v2 v1;
        return;
"
        ));
    }

    #[test]
    fn parser_with_non_continuous_value() {
        assert!(test_parser(
            "func %test_func() -> i32, i64:
    block64:
        v32.i32 = imm_i32 311;
        v120.i64 = imm_i64 120;
        jump block1;

    block1:
        return v32 v120;"
        ));
    }

    #[test]
    fn parser_with_phi() {
        assert!(test_parser(
            "func %test_func():
    block0:
        v0.i32 = imm_i32 1;
        jump block1;

    block1:
        v4.i32 = phi (v0 block0) (v5 block5);
        br v0 block6 block2;

    block2:
        br v0 block4 block3;

    block3:
        v1.i32 = imm_i32 2;
        jump block5;

    block4:
        jump block5;

    block5:
        v5.i32 = phi (v1 block3) (v4 block4);
        jump block1;

    block6:
        v3.i32 = add v4 v4;
        return;
        "
        ));
    }

    #[test]
    fn test_with_module_comment() {
        let input = "
            #! Module comment 1
            #! Module comment 2

            # f1 start 1
            # f1 start 2
            func %f1() -> i32, i64:
                block0:
                    v0.i32 = imm_i32 311;
                    v1.i64 = imm_i64 120;
                    return v0 v1;

            # f2 start 1
            # f2 start 2
            func %f2() -> i32, i64:
                block0:
                    v0.i32 = imm_i32 311;
                    v1.i64 = imm_i64 120;
                    return v0 v1;
            ";

        let parsed_module = Parser::parse(input).unwrap();
        let module_comments = parsed_module.comments;
        assert_eq!(module_comments[0], " Module comment 1");
        assert_eq!(module_comments[1], " Module comment 2");

        let func1 = &parsed_module.funcs[0];
        assert_eq!(func1.comments[0], " f1 start 1");
        assert_eq!(func1.comments[1], " f1 start 2");

        let func2 = &parsed_module.funcs[1];
        assert_eq!(func2.comments[0], " f2 start 1");
        assert_eq!(func2.comments[1], " f2 start 2");
    }
}
