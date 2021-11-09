use sonatina_codegen::ir::{
    func_cursor::{CursorLocation, FuncCursor},
    insn::{BinaryOp, CastOp, ImmediateOp, JumpOp},
    Block, BlockData, Function, Insn, InsnData, Signature, Type, Value, ValueData,
};

use super::lexer::{Code, Lexer};

pub struct Parser {}

impl Parser {
    pub fn parse(input: &str) -> ParsedModule {
        let mut lexer = Lexer::new(input);

        let mut comments = Vec::new();
        while let Some(line) = lexer.next_module_comment() {
            comments.push(line.to_string());
        }

        let mut funcs = Vec::new();
        while let Some(func) = FuncParser::new(&mut lexer).parse() {
            funcs.push(func);
        }

        ParsedModule { comments, funcs }
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

impl<'a, 'b> FuncParser<'a, 'b> {
    fn new(lexer: &'b mut Lexer<'a>) -> Self {
        Self { lexer }
    }

    fn parse(&mut self) -> Option<ParsedFunction> {
        self.lexer.peek_token()?;

        let comments = self.parse_comment();
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

        Some(ParsedFunction { comments, func })
    }

    fn parse_body(&mut self, func: &mut Function) {
        let mut inserter = InsnInserter::new(func);
        while let Some(id) = self.lexer.next_block() {
            self.lexer.next_colon().unwrap();
            self.parse_block_body(&mut inserter, Block(id));
        }
    }

    fn parse_block_body(&mut self, inserter: &mut InsnInserter, block: Block) {
        inserter.def_block(block, BlockData::default());
        inserter.append_block(block);
        inserter.set_loc(CursorLocation::BlockTop(block));

        loop {
            if let Some(value) = self.lexer.next_value() {
                self.lexer.next_dot().unwrap();
                let ty = self.lexer.next_ty().unwrap();
                self.lexer.next_eq().unwrap();
                let op_code = self.lexer.next_opcode().unwrap();
                let insn_data = op_code.parse_args(self, Some(ty));
                let insn = inserter.insert_insn_data(insn_data);
                inserter.def_value(Value(value), insn);
            } else if let Some(op_code) = self.lexer.next_opcode() {
                let insn_data = op_code.parse_args(self, None);
                inserter.insert_insn_data(insn_data);
            } else {
                break;
            }
        }
    }

    fn expect_value(&mut self) -> Value {
        Value(self.lexer.next_value().unwrap())
    }

    fn expect_block(&mut self) -> Block {
        Block(self.lexer.next_block().unwrap())
    }

    fn parse_comment(&mut self) -> Vec<String> {
        let mut comments = Vec::new();
        while let Some(line) = self.lexer.next_func_comment() {
            comments.push(line.to_string());
        }
        comments
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
                self.func.dfg.values.push(ValueData::Arg {
                    ty: Type::I8,
                    idx: usize::MAX,
                });
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

    fn def_block(&mut self, block: Block, block_data: BlockData) {
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
        InsnData::Jump {
            code: $code,
            dests: [dest],
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
            Self::Br => {
                let cond = parser.expect_value();
                let then = parser.expect_block();
                let else_ = parser.expect_block();
                InsnData::Branch {
                    args: [cond],
                    dests: [then, else_],
                }
            }
            Self::Return => {
                let mut args = vec![];
                while let Some(value) = parser.lexer.next_value() {
                    args.push(Value(value));
                }
                InsnData::Return { args }
            }
            Self::Phi => {
                let mut values = vec![];
                let mut blocks = vec![];
                while parser.lexer.next_lparen().is_some() {
                    let value = parser.lexer.next_value().unwrap();
                    values.push(Value(value));
                    let block = parser.lexer.next_block().unwrap();
                    blocks.push(Block(block));
                    parser.lexer.next_rparen().unwrap();
                }
                InsnData::Phi {
                    values,
                    blocks,
                    ty: ret_ty.unwrap(),
                }
            }
        };

        debug_assert!(parser.lexer.next_semicolon().is_some());
        insn_data
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use sonatina_codegen::ir::ir_writer::FuncWriter;

    fn test_parser(input: &str) -> bool {
        let module = Parser::parse(input);
        let mut writer = FuncWriter::new(&module.funcs[0].func);

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
            "func %test_func(i32, i64):
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

        let parsed_module = Parser::parse(input);
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
