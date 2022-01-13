use std::collections::HashSet;

use smallvec::smallvec;
use sonatina_codegen::{
    ir::{
        func_cursor::{CursorLocation, FuncCursor},
        insn::{BinaryOp, CastOp, DataLocationKind, JumpOp, UnaryOp},
        Block, BlockData, Function, Immediate, Insn, InsnData, Signature, Type, Value, ValueData,
        I256, U256,
    },
    isa::{IsaBuilder, TargetIsa},
};
use sonatina_triple::TargetTriple;

use super::{
    lexer::{Code, Lexer, Token, WithLoc},
    Error, ErrorKind, Result,
};

pub struct Parser {}

macro_rules! eat_token {
    ($lexer:expr, $token:pat) => {
        if matches!($lexer.peek_token()?, Some(WithLoc { item: $token, .. })) {
            Ok(Some($lexer.next_token()?.unwrap().item))
        } else {
            Ok(None)
        }
    };
}

macro_rules! expect_token {
    ($lexer:expr, $token:pat, $expected:expr) => {
        if let Some(tok) = eat_token!($lexer, $token)? {
            Ok(tok)
        } else {
            let (tok, line) = match $lexer.next_token()? {
                Some(tok) => ((tok.item.to_string(), tok.line)),
                None => (("EOF".to_string(), $lexer.line())),
            };
            Err(Error::new(
                ErrorKind::SyntaxError(format!("expected `{}`, but got `{}`", $expected, tok)),
                line,
            ))
        }
    };
}

impl Parser {
    pub fn parse(input: &str) -> Result<ParsedModule> {
        let mut lexer = Lexer::new(input);

        // Parse comments.
        let mut comments = Vec::new();
        while let Some(WithLoc {
            item: Token::ModuleComment(comment),
            ..
        }) = lexer.peek_token()?
        {
            comments.push(comment.to_string());
            lexer.next_token()?;
        }

        // Parse target triple.
        let triple = Self::parse_target_triple(&mut lexer)?;
        let isa = IsaBuilder::new(triple).build();

        // Parse functions.
        let mut funcs = Vec::new();
        while let Some(func) = FuncParser::new(&mut lexer, &isa).parse()? {
            funcs.push(func);
        }

        Ok(ParsedModule {
            comments,
            funcs,
            isa,
        })
    }

    fn parse_target_triple(lexer: &mut Lexer) -> Result<TargetTriple> {
        expect_token!(lexer, Token::Target, "target")?;
        expect_token!(lexer, Token::Eq, "=")?;
        let triple = expect_token!(lexer, Token::String(..), "target triple")?.string();

        TargetTriple::parse(triple)
            .map_err(|e| Error::new(ErrorKind::SemanticError(format!("{}", e)), lexer.line()))
    }
}

// TODO: Reconsider module design when IR define module.
pub struct ParsedModule {
    pub comments: Vec<String>,
    pub funcs: Vec<ParsedFunction>,
    pub isa: TargetIsa,
}

pub struct ParsedFunction {
    pub comments: Vec<String>,
    pub func: Function,
}

struct FuncParser<'a, 'b> {
    lexer: &'b mut Lexer<'a>,
    isa: &'b TargetIsa,
}

impl<'a, 'b> FuncParser<'a, 'b> {
    fn new(lexer: &'b mut Lexer<'a>, isa: &'b TargetIsa) -> Self {
        Self { lexer, isa }
    }

    fn parse(&mut self) -> Result<Option<ParsedFunction>> {
        if self.lexer.peek_token()?.is_none() {
            return Ok(None);
        }

        let comments = self.parse_comment()?;
        expect_token!(self.lexer, Token::Func, "func")?;

        let fn_name = expect_token!(self.lexer, Token::Ident(..), "func name")?.string();

        expect_token!(self.lexer, Token::LParen, "(")?;
        let mut func = Function::new(fn_name.to_string(), Signature::default());
        let mut inserter = InsnInserter::new(&mut func);

        if let Some(value) = eat_token!(self.lexer, Token::Value(..))? {
            let value = Value(value.id());
            inserter.def_value(value, self.lexer.line())?;
            expect_token!(self.lexer, Token::Dot, "dot")?;
            let ty = self.expect_ty()?;
            inserter.append_arg_value(value, ty);

            while eat_token!(self.lexer, Token::Comma)?.is_some() {
                let value = Value(expect_token!(self.lexer, Token::Value(..), "value")?.id());
                inserter.def_value(value, self.lexer.line())?;
                expect_token!(self.lexer, Token::Dot, "dot")?;
                let ty = self.expect_ty()?;
                inserter.append_arg_value(value, ty);
            }
        }
        expect_token!(self.lexer, Token::RParen, ")")?;

        if eat_token!(self.lexer, Token::RArrow)?.is_some() {
            let ty = self.expect_ty()?;
            inserter.func.sig.append_return(ty);
            while eat_token!(self.lexer, Token::Comma)?.is_some() {
                let ty = self.expect_ty()?;
                inserter.func.sig.append_return(ty);
            }
        }
        expect_token!(self.lexer, Token::Colon, ":")?;

        self.parse_body(&mut inserter)?;

        Ok(Some(ParsedFunction { comments, func }))
    }

    fn parse_body(&mut self, inserter: &mut InsnInserter) -> Result<()> {
        while let Some(id) = eat_token!(self.lexer, Token::Block(..))? {
            expect_token!(self.lexer, Token::Colon, ":")?;
            self.parse_block_body(inserter, Block(id.id()))?;
        }

        Ok(())
    }

    fn parse_block_body(&mut self, inserter: &mut InsnInserter, block: Block) -> Result<()> {
        inserter.def_block(block, self.lexer.line(), BlockData::default())?;
        inserter.append_block(block);
        inserter.set_loc(CursorLocation::BlockTop(block));

        loop {
            if let Some(value) = eat_token!(self.lexer, Token::Value(..))? {
                expect_token!(self.lexer, Token::Dot, ".")?;
                let ty = self.expect_ty()?;
                expect_token!(self.lexer, Token::Eq, "=")?;
                let opcode = expect_token!(self.lexer, Token::OpCode(..), "opcode")?.opcode();
                let insn = opcode.make_insn(self, inserter, Some(ty))?;
                let value = Value(value.id());
                inserter.def_value(value, self.lexer.line())?;
                let result = inserter.func.dfg.make_result(self.isa, insn).unwrap();
                inserter.func.dfg.values[value] = result;
                inserter.func.dfg.attach_result(insn, value);
            } else if let Some(opcode) = eat_token!(self.lexer, Token::OpCode(..))? {
                opcode.opcode().make_insn(self, inserter, None)?;
            } else {
                break;
            }
        }

        Ok(())
    }

    fn expect_insn_arg(
        &mut self,
        inserter: &mut InsnInserter,
        idx: usize,
        undefs: &mut Vec<usize>,
    ) -> Result<Value> {
        if let Some(value) = eat_token!(self.lexer, Token::Value(..))? {
            let value = Value(value.id());
            if !inserter.defined_values.contains(&value) {
                undefs.push(idx);
            }
            Ok(value)
        } else {
            let number =
                expect_token!(self.lexer, Token::Integer(..), "immediate or value")?.string();
            expect_token!(self.lexer, Token::Dot, "type annotation for immediate")?;
            let ty = self.expect_ty()?;
            let imm = build_imm_data(number, &ty, self.lexer.line())?;
            Ok(inserter.def_imm(imm))
        }
    }

    fn expect_block(&mut self) -> Result<Block> {
        let id = expect_token!(self.lexer, Token::Block(..), "block")?.id();
        Ok(Block(id))
    }

    fn expect_ty(&mut self) -> Result<Type> {
        if let Some(ty) = eat_token!(self.lexer, Token::BaseTy(..))?.map(|tok| tok.ty().clone()) {
            return Ok(ty);
        };

        // Try parse array type.
        expect_token!(self.lexer, Token::LBracket, "[")?;
        let elem_ty = self.expect_ty()?;
        expect_token!(self.lexer, Token::SemiColon, ";")?;
        let len = expect_token!(self.lexer, Token::Integer(..), " or value")?
            .string()
            .parse()
            .map_err(|err| {
                Error::new(
                    ErrorKind::SyntaxError(format!("{}", err)),
                    self.lexer.line(),
                )
            })?;
        expect_token!(self.lexer, Token::RBracket, "]")?;
        Ok(Type::make_array(elem_ty, len))
    }

    fn expect_data_loc_kind(&mut self) -> Result<DataLocationKind> {
        let token = expect_token!(self.lexer, Token::DataLocationKind(..), "data location")?;

        match token {
            Token::DataLocationKind(loc) => Ok(loc),
            _ => unreachable!(),
        }
    }

    fn parse_comment(&mut self) -> Result<Vec<String>> {
        let mut comments = Vec::new();
        while let Some(line) = eat_token!(self.lexer, Token::FuncComment(..))? {
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
    defined_imms: HashSet<Value>,
    undefs: HashSet<(Insn, usize)>,
}

impl<'a> InsnInserter<'a> {
    fn new(func: &'a mut Function) -> Self {
        Self {
            func,
            loc: CursorLocation::NoWhere,
            defined_values: HashSet::new(),
            defined_blocks: HashSet::new(),
            defined_imms: HashSet::new(),
            undefs: HashSet::new(),
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

        if self.defined_imms.contains(&value) {
            let imm_data = self.func.dfg.value_data(value).clone();
            let new_imm_value = self.func.dfg.make_value(imm_data);
            let mut must_replace = vec![];
            for &user in self.func.dfg.users(value) {
                for (idx, &arg) in self.func.dfg.insn_args(user).iter().enumerate() {
                    if arg == value && !self.undefs.contains(&(user, idx)) {
                        must_replace.push((user, idx));
                    }
                }
            }

            for (insn, idx) in must_replace {
                self.func.dfg.replace_insn_arg(insn, new_imm_value, idx);
            }

            let imm = self.func.dfg.value_imm(new_imm_value).unwrap();
            self.func.dfg.immediates.insert(imm, new_imm_value);
            self.defined_imms.remove(&value);
            self.defined_imms.insert(new_imm_value);
        }

        Ok(())
    }

    fn def_imm(&mut self, imm: Immediate) -> Value {
        let value = self.func.dfg.make_imm_value(imm);
        self.defined_imms.insert(value);
        value
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
        self.func
    }

    fn loc(&self) -> CursorLocation {
        self.loc
    }
}

macro_rules! make_unary {
    ($parser:ident, $inserter:ident, $code:path, $undefs:expr) => {{
        let lhs = $parser.expect_insn_arg($inserter, 0, $undefs)?;
        expect_token!($parser.lexer, Token::SemiColon, ";")?;
        InsnData::Unary {
            code: $code,
            args: [lhs],
        }
    }};
}

macro_rules! make_binary {
    ($parser:ident, $inserter:ident, $code:path, $undefs:expr) => {{
        let lhs = $parser.expect_insn_arg($inserter, 0, $undefs)?;
        let rhs = $parser.expect_insn_arg($inserter, 1, $undefs)?;
        expect_token!($parser.lexer, Token::SemiColon, ";")?;
        InsnData::Binary {
            code: $code,
            args: [lhs, rhs],
        }
    }};
}

macro_rules! make_cast {
    ($parser:ident, $inserter:ident, $cast_to:expr, $code:path, $undefs:expr) => {{
        let arg = $parser.expect_insn_arg($inserter, 0, $undefs)?;
        expect_token!($parser.lexer, Token::SemiColon, ";")?;
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
        expect_token!($parser.lexer, Token::SemiColon, ";")?;
        InsnData::Jump {
            code: $code,
            dests: [dest],
        }
    }};
}

impl Code {
    /// Read args and create insn data.
    fn make_insn(
        self,
        parser: &mut FuncParser,
        inserter: &mut InsnInserter,
        ret_ty: Option<Type>,
    ) -> Result<Insn> {
        let mut undefs = vec![];
        let insn_data = match self {
            Self::Not => make_unary!(parser, inserter, UnaryOp::Not, &mut undefs),
            Self::Neg => make_unary!(parser, inserter, UnaryOp::Neg, &mut undefs),
            Self::Add => make_binary!(parser, inserter, BinaryOp::Add, &mut undefs),
            Self::Sub => make_binary!(parser, inserter, BinaryOp::Sub, &mut undefs),
            Self::Mul => make_binary!(parser, inserter, BinaryOp::Mul, &mut undefs),
            Self::Udiv => make_binary!(parser, inserter, BinaryOp::Udiv, &mut undefs),
            Self::Sdiv => make_binary!(parser, inserter, BinaryOp::Sdiv, &mut undefs),
            Self::Lt => make_binary!(parser, inserter, BinaryOp::Lt, &mut undefs),
            Self::Gt => make_binary!(parser, inserter, BinaryOp::Gt, &mut undefs),
            Self::Slt => make_binary!(parser, inserter, BinaryOp::Slt, &mut undefs),
            Self::Sgt => make_binary!(parser, inserter, BinaryOp::Sgt, &mut undefs),
            Self::Le => make_binary!(parser, inserter, BinaryOp::Le, &mut undefs),
            Self::Ge => make_binary!(parser, inserter, BinaryOp::Ge, &mut undefs),
            Self::Sle => make_binary!(parser, inserter, BinaryOp::Sle, &mut undefs),
            Self::Sge => make_binary!(parser, inserter, BinaryOp::Sge, &mut undefs),
            Self::Eq => make_binary!(parser, inserter, BinaryOp::Eq, &mut undefs),
            Self::Ne => make_binary!(parser, inserter, BinaryOp::Ne, &mut undefs),
            Self::And => make_binary!(parser, inserter, BinaryOp::And, &mut undefs),
            Self::Or => make_binary!(parser, inserter, BinaryOp::Or, &mut undefs),
            Self::Xor => make_binary!(parser, inserter, BinaryOp::Xor, &mut undefs),
            Self::Sext => make_cast!(parser, inserter, ret_ty.unwrap(), CastOp::Sext, &mut undefs),
            Self::Zext => make_cast!(parser, inserter, ret_ty.unwrap(), CastOp::Zext, &mut undefs),
            Self::Trunc => make_cast!(
                parser,
                inserter,
                ret_ty.unwrap(),
                CastOp::Trunc,
                &mut undefs
            ),

            Self::Load => {
                let loc = parser.expect_data_loc_kind()?;
                let arg = parser.expect_insn_arg(inserter, 0, &mut undefs)?;
                let ty = parser.expect_ty()?;
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Load {
                    args: [arg],
                    ty,
                    loc,
                }
            }
            Self::Store => {
                let loc = parser.expect_data_loc_kind()?;
                let lhs = parser.expect_insn_arg(inserter, 0, &mut undefs)?;
                let rhs = parser.expect_insn_arg(inserter, 1, &mut undefs)?;
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Store {
                    args: [lhs, rhs],
                    loc,
                }
            }

            Self::Jump => make_jump!(parser, JumpOp::Jump),
            Self::FallThrough => make_jump!(parser, JumpOp::FallThrough),

            Self::Br => {
                let cond = parser.expect_insn_arg(inserter, 0, &mut undefs)?;
                let then = parser.expect_block()?;
                let else_ = parser.expect_block()?;
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Branch {
                    args: [cond],
                    dests: [then, else_],
                }
            }
            Self::BrTable => {
                let mut arg_idx = 0;
                let mut args = smallvec![];
                let cond = parser.expect_insn_arg(inserter, arg_idx, &mut undefs)?;
                args.push(cond);
                arg_idx += 1;

                let default = if eat_token!(parser.lexer, Token::Undef)?.is_some() {
                    None
                } else {
                    Some(parser.expect_block()?)
                };

                let mut table = smallvec![];
                while eat_token!(parser.lexer, Token::LParen)?.is_some() {
                    let value = parser.expect_insn_arg(inserter, arg_idx, &mut undefs)?;
                    args.push(value);
                    let block = parser.expect_block()?;
                    table.push(block);
                    expect_token!(parser.lexer, Token::RParen, ")")?;
                    arg_idx += 1;
                }
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::BrTable {
                    args,
                    default,
                    table,
                }
            }

            Self::Alloca => {
                let ty = parser.expect_ty()?;
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Alloca { ty }
            }

            Self::Return => {
                let mut args = smallvec![];
                let mut idx = 0;
                while eat_token!(parser.lexer, Token::SemiColon)?.is_none() {
                    let value = parser.expect_insn_arg(inserter, idx, &mut undefs)?;
                    args.push(value);
                    idx += 1;
                }
                InsnData::Return { args }
            }
            Self::Phi => {
                let mut values = smallvec![];
                let mut blocks = smallvec![];
                let mut idx = 0;
                while eat_token!(parser.lexer, Token::LParen)?.is_some() {
                    let value = parser.expect_insn_arg(inserter, idx, &mut undefs)?;
                    values.push(value);
                    let block = parser.expect_block()?;
                    blocks.push(block);
                    expect_token!(parser.lexer, Token::RParen, ")")?;
                    idx += 1;
                }
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Phi {
                    values,
                    blocks,
                    ty: ret_ty.unwrap(),
                }
            }
        };

        let insn = inserter.insert_insn_data(insn_data);
        for undef in undefs {
            inserter.undefs.insert((insn, undef));
        }

        Ok(insn)
    }
}

fn build_imm_data(number: &str, ty: &Type, line: u32) -> Result<Immediate> {
    match ty {
        Type::I1 => number
            .parse::<i8>()
            .map(|val| Immediate::I1(val != 0))
            .map_err(|err| parse_imm_error(err, line)),

        Type::I8 => number
            .parse::<i8>()
            .or_else(|_| number.parse::<u8>().map(|v| v as i8))
            .map(Into::into)
            .map_err(|err| parse_imm_error(err, line)),

        Type::I16 => number
            .parse::<i16>()
            .or_else(|_| number.parse::<u16>().map(|v| v as i16))
            .map(Into::into)
            .map_err(|err| parse_imm_error(err, line)),

        Type::I32 => number
            .parse::<i32>()
            .or_else(|_| number.parse::<u32>().map(|v| v as i32))
            .map(Into::into)
            .map_err(|err| parse_imm_error(err, line)),

        Type::I64 => number
            .parse::<i64>()
            .or_else(|_| number.parse::<u64>().map(|v| v as i64))
            .map(Into::into)
            .map_err(|err| parse_imm_error(err, line)),

        Type::I128 => number
            .parse::<i128>()
            .or_else(|_| number.parse::<u128>().map(|v| v as i128))
            .map(Into::into)
            .map_err(|err| parse_imm_error(err, line)),

        Type::I256 => {
            let number = number.to_string();
            let is_negative = number.as_bytes()[0] as char == '-';
            let number = if is_negative { &number[1..] } else { &number };
            let mut i256: I256 = U256::from_str_radix(number, 10)
                .map(Into::into)
                .map_err(|err| parse_imm_error(err, line))?;

            if is_negative {
                i256 = I256::zero().overflowing_sub(i256).0;
            }

            Ok(Immediate::I256(i256))
        }

        Type::Array { .. } => Err(Error::new(
            ErrorKind::SemanticError("can't use immediate for array type".into()),
            line,
        )),
    }
}

fn parse_imm_error(err: impl std::fmt::Display, line: u32) -> Error {
    Error::new(
        ErrorKind::SemanticError(format!("failed to parse immediate: {}", err)),
        line,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use sonatina_codegen::ir::ir_writer::FuncWriter;

    fn test_func_parser(input: &str) -> bool {
        let mut lexer = Lexer::new(input);
        let triple = TargetTriple::parse("evm-ethereum-london").unwrap();
        let isa = IsaBuilder::new(triple).build();
        let func = FuncParser::new(&mut lexer, &isa).parse().unwrap().unwrap();
        let mut writer = FuncWriter::new(&func.func);

        input.trim() == writer.dump_string().unwrap().trim()
    }

    #[test]
    fn parser_with_return() {
        assert!(test_func_parser(
            "func %test_func() -> i32, i64:
    block0:
        return 311.i32 -120.i64;"
        ));
    }

    #[test]
    fn test_with_arg() {
        assert!(test_func_parser(
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
        assert!(test_func_parser(
            "func %test_func() -> i32, i64:
    block64:
        jump block1;

    block1:
        return 311.i32 -120.i64;"
        ));
    }

    #[test]
    fn parser_with_phi() {
        assert!(test_func_parser(
            "func %test_func():
    block0:
        jump block1;

    block1:
        v4.i32 = phi (1.i32 block0) (v5 block5);
        br 1.i32 block6 block2;

    block2:
        br 1.i32 block4 block3;

    block3:
        jump block5;

    block4:
        jump block5;

    block5:
        v5.i32 = phi (2.i32 block3) (v4 block4);
        jump block1;

    block6:
        v3.i32 = add v4 v4;
        return;
        "
        ));
    }

    #[test]
    fn parser_with_immediate() {
        assert!(test_func_parser(
            "func %test_func() -> i8, i16:
    block64:
        v0.i8 = add -1.i8 127.i8;
        v1.i8 = add v0 3.i8;
        jump block1;

    block1:
        v2.i16 = zext -128.i8;
        return v1 v2;"
        ));
    }

    #[test]
    fn test_with_module_comment() {
        let input = "
            #! Module comment 1
            #! Module comment 2

            target = \"evm-ethereum-london\"

            # f1 start 1
            # f1 start 2
            func %f1() -> i32, i64:
                block0:
                    return 311.i32 -120.i64;

            # f2 start 1
            # f2 start 2
            func %f2() -> i32, i64:
                block0:
                    return 311.i32 -120.i64;
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
