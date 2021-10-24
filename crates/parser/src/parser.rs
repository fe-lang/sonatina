use sonatina_codegen::ir::{
    func_cursor::{CursorLocation, FuncCursor},
    insn::{BinaryOp, BranchOp, CastOp, ImmediateOp, JumpOp},
    Block, BlockData, Function, Insn, InsnData, Signature, Type, Value, ValueData,
};

use super::lexer::{Code, Lexer, Token};

pub struct Parser {}

impl Parser {
    pub fn parse<'a>(input: &'a str) -> Module {
        let mut lexer = Lexer::new(input);

        let mut funcs = Vec::new();
        while matches!(lexer.peek_token(), Some(Token::Func)) {
            let mut func_parser = FuncParser::new(&mut lexer);
            let func = func_parser.parse();
            funcs.push(func);
        }

        Module { funcs }
    }
}

// TODO: Reconsider module design when IR define module.
pub struct Module {
    pub funcs: Vec<Function>,
}

struct FuncParser<'a, 'b> {
    lexer: &'b mut Lexer<'a>,
}

impl<'a, 'b> FuncParser<'a, 'b> {
    fn new(lexer: &'b mut Lexer<'a>) -> Self {
        Self { lexer }
    }

    fn parse(&mut self) -> Function {
        self.lexer.next_func().unwrap();

        let fn_name = self.lexer.next_ident().unwrap();

        let mut sig = Signature::default();
        self.lexer.next_lparen().unwrap();
        if let Some(ty) = self.lexer.next_ty() {
            sig.append_arg(ty);
            while self.lexer.next_comma().is_some() {
                let ty = self.lexer.next_ty().unwrap();
                sig.append_arg(ty);
            }
        }
        self.lexer.next_rparen().unwrap();

        if self.lexer.next_right_arrow().is_some() {
            let ty = self.lexer.next_ty().unwrap();
            sig.append_return(ty);
            while self.lexer.next_comma().is_some() {
                let ty = self.lexer.next_ty().unwrap();
                sig.append_return(ty);
            }
        }
        self.lexer.next_colon().unwrap();

        let mut func = Function::new(fn_name.to_string(), sig);
        self.parse_body(&mut func);

        func
    }

    fn parse_body(&mut self, func: &mut Function) {
        let mut inserter = InsnInserter::new(func);
        while let Some(id) = self.lexer.next_block() {
            self.lexer.next_colon().unwrap();
            self.parse_block_body(&mut inserter, Block(id));
        }
    }

    fn parse_block_body(&mut self, inserter: &mut InsnInserter, block: Block) {
        inserter.def_block(block);
        inserter.append_block(block);
        inserter.set_loc(CursorLocation::BlockTop(block));

        loop {
            if let Some(value) = self.lexer.next_value() {
                self.lexer.next_eq().unwrap();
                let op_code = self.lexer.next_opcode().unwrap();
                let insn_data = op_code.parse_args(self, Some(value.ty));
                let insn = inserter.insert_insn_data(insn_data);
                inserter.def_value(Value(value.id), insn);
            } else if let Some(op_code) = self.lexer.next_opcode() {
                let insn_data = op_code.parse_args(self, None);
                inserter.insert_insn_data(insn_data);
            } else {
                break;
            }
        }
    }

    fn expect_value(&mut self) -> Value {
        Value(self.lexer.next_value().unwrap().id)
    }

    fn expect_block(&mut self) -> Block {
        Block(self.lexer.next_block().unwrap())
    }
}

struct InsnInserter<'a> {
    func: &'a mut Function,
    loc: CursorLocation,
}

impl<'a> InsnInserter<'a> {
    fn new(func: &'a mut Function) -> Self {
        Self {
            func,
            loc: CursorLocation::NoWhere,
        }
    }

    fn def_value(&mut self, value: Value, insn: Insn) {
        let result = self.func.dfg.make_result(insn).unwrap();
        let value_len = self.func.dfg.values.len();
        let value_id = value.0 as usize;

        if value_len <= value_id {
            self.func.dfg.values.reserve(value_id);
            for _ in 0..(value_id - value_len + 1) {
                // Make dummy value.
                self.func
                    .dfg
                    .values
                    .push(ValueData::Alias { value: Value(0) });
            }
        }

        self.func.dfg.values[value] = result;
        self.func.dfg.attach_result(insn, value);
    }

    fn insert_insn_data(&mut self, insn_data: InsnData) -> Insn {
        let insn = self.func.dfg.make_insn(insn_data);
        self.insert_insn(insn);
        self.set_loc(CursorLocation::At(insn));
        insn
    }

    fn def_block(&mut self, block: Block) {
        let block_id = block.0 as usize;
        let block_len = self.func.dfg.blocks.len();

        if block_len <= block_id {
            self.func.dfg.blocks.reserve(block_id);
            for _ in 0..(block_id - block_len + 1) {
                self.func.dfg.blocks.push(BlockData::default());
            }
        }
    }
}

impl<'a> FuncCursor for InsnInserter<'a> {
    fn set_loc(&mut self, loc: CursorLocation) {
        self.loc = loc;
    }

    fn func(&self) -> &Function {
        &self.func
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
        let imm = $parser.lexer.next_integer().unwrap();
        InsnData::Immediate {
            code: $code(imm.parse().unwrap()),
        }
    }};
}

macro_rules! make_binary {
    ($parser:ident, $code:path) => {{
        let lhs = $parser.expect_value();
        let rhs = $parser.expect_value();
        InsnData::Binary {
            code: $code,
            args: [lhs, rhs],
        }
    }};
}

macro_rules! make_cast {
    ($parser:ident, $cast_to:expr, $code:path) => {{
        let arg = $parser.expect_value();
        InsnData::Cast {
            code: $code,
            args: [arg],
            ty: $cast_to,
        }
    }};
}

macro_rules! make_jump {
    ($parser:ident, $code:path) => {{
        let dest = $parser.expect_block();
        InsnData::Jump { code: $code, dest }
    }};
}

macro_rules! make_branch {
    ($parser:ident, $code:path) => {{
        let arg = $parser.expect_value();
        let dest = $parser.expect_block();
        InsnData::Branch {
            code: $code,
            args: [arg],
            dest,
        }
    }};
}

impl Code {
    /// Read args and create insn data.
    fn parse_args(self, parser: &mut FuncParser, ret_ty: Option<Type>) -> InsnData {
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
            Self::Div => make_binary!(parser, BinaryOp::Div),
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
                let ty = ret_ty.unwrap();
                let arg = parser.expect_value();
                InsnData::Load { args: [arg], ty }
            }
            Self::Store => {
                let lhs = parser.expect_value();
                let rhs = parser.expect_value();
                InsnData::Store { args: [lhs, rhs] }
            }
            Self::Jump => make_jump!(parser, JumpOp::Jump),
            Self::FallThrough => make_jump!(parser, JumpOp::FallThrough),
            Self::Brz => make_branch!(parser, BranchOp::Brz),
            Self::Brnz => make_branch!(parser, BranchOp::Brnz),
            Self::Return => {
                let mut args = vec![];
                while let Some(value) = parser.lexer.next_value() {
                    args.push(Value(value.id));
                }
                InsnData::Return { args }
            }
            Self::Phi => {
                let mut args = vec![];
                while let Some(value) = parser.lexer.next_value() {
                    args.push(Value(value.id));
                }
                InsnData::Phi {
                    args,
                    ty: ret_ty.unwrap(),
                }
            }
        };

        debug_assert!(parser.lexer.next_semicolon().is_some());
        insn_data
    }
}
