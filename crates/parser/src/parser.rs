// TODO: Refactor and refactor and refactor!!!
use std::collections::HashSet;

use cranelift_entity::SecondaryMap;
use smallvec::smallvec;

use sonatina_ir::{
    builder::ModuleBuilder,
    func_cursor::{CursorLocation, FuncCursor},
    global_variable::ConstantValue,
    insn::{BinaryOp, CastOp, DataLocationKind, JumpOp, UnaryOp},
    isa::IsaBuilder,
    module::{FuncRef, ModuleCtx},
    Block, BlockData, Function, GlobalVariableData, Immediate, Insn, InsnData, Linkage, Module,
    Signature, Type, Value, ValueData, I256, U256,
};
use sonatina_triple::TargetTriple;

use super::{
    lexer::{Code, Lexer, Token, WithLoc},
    Error, ErrorKind, Result,
};

#[derive(Default)]
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
    pub fn parse(self, input: &str) -> Result<ParsedModule> {
        let mut lexer = Lexer::new(input);

        // Parse comments.
        let mut module_comments = Vec::new();
        while let Some(WithLoc {
            item: Token::ModuleComment(comment),
            ..
        }) = lexer.peek_token()?
        {
            module_comments.push(comment.to_string());
            lexer.next_token()?;
        }

        // Parse target triple.
        let triple = self.parse_target_triple(&mut lexer)?;
        let isa = IsaBuilder::new(triple).build();
        let ctx = ModuleCtx::new(isa);

        let mut module_builder = ModuleBuilder::new(ctx);

        // Parse declared struct types.
        while eat_token!(lexer, Token::Type)?.is_some() {
            let name = expect_token!(lexer, Token::Ident(_), "type name")?.string();
            expect_token!(lexer, Token::Eq, "=")?;
            let packed = eat_token!(lexer, Token::LAngleBracket)?.is_some();
            expect_token!(lexer, Token::LBrace, "{")?;

            let mut fields = vec![];
            if eat_token!(lexer, Token::RBrace)?.is_none() {
                loop {
                    let ty = expect_ty(&module_builder.ctx, &mut lexer)?;
                    fields.push(ty);
                    if eat_token!(lexer, Token::RBrace)?.is_some() {
                        break;
                    }
                    expect_token!(lexer, Token::Comma, ",")?;
                }
            }
            if packed {
                expect_token!(lexer, Token::RAngleBracket, ">")?;
            }
            expect_token!(lexer, Token::SemiColon, ";")?;

            module_builder.declare_struct_type(name, &fields, packed);
        }

        // Parse global variables.
        while eat_token!(lexer, Token::Gv)?.is_some() {
            let linkage = expect_linkage(&mut lexer)?;
            let is_const = eat_token!(lexer, Token::Const)?.is_some();
            let symbol = expect_token!(lexer, Token::Ident(_), "global variable name")?.string();
            expect_token!(lexer, Token::Colon, ":")?;
            let ty = expect_ty(&module_builder.ctx, &mut lexer)?;

            let init = eat_token!(lexer, Token::Eq)?
                .map(|_| {
                    let init = expect_constant(&module_builder.ctx, &mut lexer, ty)?;
                    Ok(init)
                })
                .transpose()?;

            expect_token!(lexer, Token::SemiColon, ";")?;
            let gv_data = GlobalVariableData::new(symbol.to_string(), ty, linkage, is_const, init);
            module_builder.make_global(gv_data);
        }

        // Parse declared functions.
        while eat_token!(lexer, Token::Declare)?.is_some() {
            let sig = self.parse_declared_func_sig(&module_builder.ctx, &mut lexer)?;
            expect_token!(lexer, Token::SemiColon, ";")?;
            module_builder.declare_function(sig);
        }

        // Parse functions.
        let mut func_comments = SecondaryMap::default();
        while let Some(parsed_func) = FuncParser::new(&mut lexer, &mut module_builder).parse()? {
            let func_ref = parsed_func.func_ref;
            func_comments[func_ref] = parsed_func.comments;
        }

        Ok(ParsedModule {
            module: module_builder.build(),
            module_comments,
            func_comments,
        })
    }

    fn parse_target_triple(&self, lexer: &mut Lexer) -> Result<TargetTriple> {
        expect_token!(lexer, Token::Target, "target")?;
        expect_token!(lexer, Token::Eq, "=")?;
        let triple = expect_token!(lexer, Token::String(..), "target triple")?.string();

        TargetTriple::parse(triple)
            .map_err(|e| Error::new(ErrorKind::SemanticError(format!("{}", e)), lexer.line()))
    }

    fn parse_declared_func_sig(&self, ctx: &ModuleCtx, lexer: &mut Lexer) -> Result<Signature> {
        let linkage = expect_linkage(lexer)?;
        let name = expect_token!(lexer, Token::Ident(..), "func name")?.string();

        // Parse argument types.
        expect_token!(lexer, Token::LParen, "(")?;
        let mut args = vec![];
        if eat_token!(lexer, Token::RParen)?.is_none() {
            let ty = expect_ty(ctx, lexer)?;
            args.push(ty);
            while eat_token!(lexer, Token::RParen)?.is_none() {
                expect_token!(lexer, Token::Comma, ",")?;
                let ty = expect_ty(ctx, lexer)?;
                args.push(ty);
            }
        }

        // Parse return type.
        expect_token!(lexer, Token::RArrow, "->")?;
        let ret_ty = expect_ty(ctx, lexer)?;

        Ok(Signature::new(name, linkage, &args, ret_ty))
    }
}

pub struct ParsedModule {
    pub module: Module,
    pub module_comments: Vec<String>,
    pub func_comments: SecondaryMap<FuncRef, Vec<String>>,
}

struct ParsedFunction {
    func_ref: FuncRef,
    comments: Vec<String>,
}

struct FuncParser<'a, 'b> {
    lexer: &'b mut Lexer<'a>,
    module_builder: &'b mut ModuleBuilder,
}

impl<'a, 'b> FuncParser<'a, 'b> {
    fn new(lexer: &'b mut Lexer<'a>, module_builder: &'b mut ModuleBuilder) -> Self {
        Self {
            lexer,
            module_builder,
        }
    }

    fn parse(&mut self) -> Result<Option<ParsedFunction>> {
        if self.lexer.peek_token()?.is_none() {
            return Ok(None);
        }

        let comments = self.parse_comment()?;
        expect_token!(self.lexer, Token::Func, "func")?;
        let linkage = expect_linkage(self.lexer)?;

        let fn_name = expect_token!(self.lexer, Token::Ident(..), "func name")?.string();

        expect_token!(self.lexer, Token::LParen, "(")?;
        // Use `Void` for dummy return type.
        let sig = Signature::new(fn_name, linkage, &[], Type::Void);
        let mut func = Function::new(&self.module_builder.ctx, sig);
        let mut inserter = InsnInserter::new(&mut func);

        if let Some(value) = eat_token!(self.lexer, Token::Value(..))? {
            let value = Value(value.id());
            inserter.def_value(value, self.lexer.line())?;
            expect_token!(self.lexer, Token::Dot, "dot")?;
            let ty = expect_ty(&self.module_builder.ctx, self.lexer)?;
            inserter.append_arg_value(value, ty);

            while eat_token!(self.lexer, Token::Comma)?.is_some() {
                let value = Value(expect_token!(self.lexer, Token::Value(..), "value")?.id());
                inserter.def_value(value, self.lexer.line())?;
                expect_token!(self.lexer, Token::Dot, "dot")?;
                let ty = expect_ty(&self.module_builder.ctx, self.lexer)?;
                inserter.append_arg_value(value, ty);
            }
        }
        expect_token!(self.lexer, Token::RParen, ")")?;

        // Parse return type.
        expect_token!(self.lexer, Token::RArrow, "->")?;
        let ret_ty = expect_ty(&self.module_builder.ctx, self.lexer)?;
        inserter.func.sig.set_ret_ty(ret_ty);
        expect_token!(self.lexer, Token::Colon, ":")?;

        self.parse_body(&mut inserter)?;

        let func_ref = self.module_builder.declare_function(func.sig.clone());
        std::mem::swap(&mut self.module_builder.funcs[func_ref], &mut func);
        Ok(Some(ParsedFunction { func_ref, comments }))
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
                let ty = expect_ty(&self.module_builder.ctx, self.lexer)?;
                expect_token!(self.lexer, Token::Eq, "=")?;
                let opcode = expect_token!(self.lexer, Token::OpCode(..), "opcode")?.opcode();
                let insn = opcode.make_insn(self, inserter, Some(ty))?;
                let value = Value(value.id());
                inserter.def_value(value, self.lexer.line())?;
                let result = inserter.func.dfg.make_result(insn).unwrap();
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
        } else if let Some(ident) = eat_token!(self.lexer, Token::Ident(..))? {
            let gv = inserter
                .func()
                .dfg
                .ctx
                .with_gv_store(|s| s.gv_by_symbol(ident.string()))
                .unwrap();
            Ok(inserter.func_mut().dfg.make_global_value(gv))
        } else {
            let number =
                expect_token!(self.lexer, Token::Integer(..), "immediate or value")?.string();
            expect_token!(self.lexer, Token::Dot, "type annotation for immediate")?;
            let ty = expect_ty(&self.module_builder.ctx, self.lexer)?;
            let imm = build_imm_data(number, &ty, self.lexer.line())?;
            Ok(inserter.def_imm(imm))
        }
    }

    fn expect_block(&mut self) -> Result<Block> {
        let id = expect_token!(self.lexer, Token::Block(..), "block")?.id();
        Ok(Block(id))
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

fn expect_ty(ctx: &ModuleCtx, lexer: &mut Lexer) -> Result<Type> {
    if let Some(ty) = eat_token!(lexer, Token::BaseTy(..))?.map(|tok| tok.ty()) {
        return Ok(ty);
    };

    if eat_token!(lexer, Token::LBracket)?.is_some() {
        // Try parse array element type.
        let elem_ty = expect_ty(ctx, lexer)?;
        expect_token!(lexer, Token::SemiColon, ";")?;
        // Try parse array length.
        let len = expect_token!(lexer, Token::Integer(..), " or value")?
            .string()
            .parse()
            .map_err(|err| Error::new(ErrorKind::SyntaxError(format!("{}", err)), lexer.line()))?;
        expect_token!(lexer, Token::RBracket, "]")?;
        Ok(ctx.with_ty_store_mut(|s| s.make_array(elem_ty, len)))
    } else if eat_token!(lexer, Token::Star)?.is_some() {
        // Try parse ptr base type.
        let elem_ty = expect_ty(ctx, lexer)?;
        Ok(ctx.with_ty_store_mut(|s| s.make_ptr(elem_ty)))
    } else if let Some(tok) = eat_token!(lexer, Token::Ident(..))? {
        let name = tok.string();
        ctx.with_ty_store(|s| s.struct_type_by_name(name))
            .ok_or_else(|| {
                Error::new(
                    ErrorKind::SemanticError(format!("type `{name}` is not declared")),
                    lexer.line(),
                )
            })
    } else {
        Err(Error::new(
            ErrorKind::SyntaxError("invalid type".into()),
            lexer.line(),
        ))
    }
}

fn expect_linkage(lexer: &mut Lexer) -> Result<Linkage> {
    let token = expect_token!(lexer, Token::Linkage { .. }, "linkage")?;
    match token {
        Token::Linkage(linkage) => Ok(linkage),
        _ => unreachable!(),
    }
}

fn expect_constant(ctx: &ModuleCtx, lexer: &mut Lexer, ty: Type) -> Result<ConstantValue> {
    if let Some(number) = eat_token!(lexer, Token::Integer(..))? {
        if !ty.is_integral() {
            return Err(Error::new(
                ErrorKind::SemanticError("expected integral type".to_string()),
                lexer.line(),
            ));
        }

        let data = build_imm_data(number.string(), &ty, lexer.line())?;
        Ok(ConstantValue::Immediate(data))
    } else if eat_token!(lexer, Token::LBracket)?.is_some() {
        let (elem_ty, mut len) = ctx.with_ty_store(|s| s.array_def(ty)).ok_or_else(|| {
            Error::new(
                ErrorKind::SemanticError("expcted array type".into()),
                lexer.line(),
            )
        })?;

        let mut data = Vec::with_capacity(len);
        while len > 0 {
            let elem = expect_constant(ctx, lexer, elem_ty)?;
            data.push(elem);
            if len > 1 {
                expect_token!(lexer, Token::Comma, ",")?;
            }
            len -= 1;
        }

        expect_token!(lexer, Token::RBracket, "]")?;
        Ok(ConstantValue::Array(data))
    } else if eat_token!(lexer, Token::LBrace)?.is_some() {
        let fields = ctx
            .with_ty_store(|s| s.struct_def(ty).map(|def| def.fields.clone()))
            .ok_or_else(|| {
                Error::new(
                    ErrorKind::SemanticError("expected struct type".into()),
                    lexer.line(),
                )
            })?;

        let mut data = Vec::with_capacity(fields.len());
        let field_len = fields.len();
        for (i, field_ty) in fields.into_iter().enumerate() {
            let field = expect_constant(ctx, lexer, field_ty)?;
            data.push(field);
            if i < field_len - 1 {
                expect_token!(lexer, Token::Comma, ",")?;
            }
        }
        expect_token!(lexer, Token::RBrace, "}")?;
        Ok(ConstantValue::Struct(data))
    } else {
        Err(Error::new(
            ErrorKind::SyntaxError("invalid constant".into()),
            lexer.line(),
        ))
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

        let value_data = self.func.dfg.make_arg_value(ty, idx);
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
            Self::BitCast => make_cast!(
                parser,
                inserter,
                ret_ty.unwrap(),
                CastOp::BitCast,
                &mut undefs
            ),
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
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Load { args: [arg], loc }
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

            Self::Call => {
                let func_name =
                    expect_token!(parser.lexer, Token::Ident(..), "func name")?.string();
                let mut args = smallvec![];
                let mut idx = 0;
                while eat_token!(parser.lexer, Token::SemiColon)?.is_none() {
                    let arg = parser.expect_insn_arg(inserter, idx, &mut undefs)?;
                    args.push(arg);
                    idx += 1;
                }

                let func = parser
                    .module_builder
                    .get_func_ref(func_name)
                    .ok_or_else(|| {
                        Error::new(
                            ErrorKind::SemanticError(format!("%{} is not declared", func_name)),
                            parser.lexer.line(),
                        )
                    })?;
                let sig = parser.module_builder.get_sig(func).clone();
                let ret_ty = sig.ret_ty();
                inserter.func_mut().callees.insert(func, sig);
                InsnData::Call { func, args, ret_ty }
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

            Self::Gep => {
                let mut args = smallvec![];
                let mut idx = 0;
                while eat_token!(parser.lexer, Token::SemiColon)?.is_none() {
                    let arg = parser.expect_insn_arg(inserter, idx, &mut undefs)?;
                    args.push(arg);
                    idx += 1;
                }

                InsnData::Gep { args }
            }

            Self::Alloca => {
                let ty = expect_ty(&parser.module_builder.ctx, parser.lexer)?;
                expect_token!(parser.lexer, Token::SemiColon, ";")?;
                InsnData::Alloca { ty }
            }

            Self::Return => {
                if eat_token!(parser.lexer, Token::SemiColon)?.is_some() {
                    InsnData::Return { args: None }
                } else {
                    let value = parser.expect_insn_arg(inserter, 0, &mut undefs)?;
                    expect_token!(parser.lexer, Token::SemiColon, ";")?;
                    InsnData::Return { args: Some(value) }
                }
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

        _ => Err(Error::new(
            ErrorKind::SemanticError("can't use non integral types for immediates".into()),
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

    use sonatina_ir::ir_writer::FuncWriter;

    fn test_func_parser(input: &str) -> bool {
        let mut lexer = Lexer::new(input);
        let triple = TargetTriple::parse("evm-ethereum-london").unwrap();
        let isa = IsaBuilder::new(triple).build();
        let mut module_builder = ModuleBuilder::new(ModuleCtx::new(isa));
        let parsed_func = FuncParser::new(&mut lexer, &mut module_builder)
            .parse()
            .unwrap()
            .unwrap();
        let module = module_builder.build();
        let mut writer = FuncWriter::new(&module.funcs[parsed_func.func_ref]);

        input.trim() == writer.dump_string().unwrap().trim()
    }

    #[test]
    fn parser_with_return() {
        assert!(test_func_parser(
            "func private %test_func() -> i32:
    block0:
        return 311.i32;"
        ));
    }

    #[test]
    fn test_with_arg() {
        assert!(test_func_parser(
            "func public %test_func(v0.i32, v1.i64) -> void:
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
            "func private %test_func() -> i32:
    block64:
        jump block1;

    block1:
        return 311.i32;"
        ));
    }

    #[test]
    fn test_gep() {
        assert!(test_func_parser(
            "func public %test(v0.**i32) -> **i32:
    block0:
        v1.*i32 = gep v0 10.i32;
        return v1;"
        ));
    }

    #[test]
    fn parser_with_phi() {
        assert!(test_func_parser(
            "func private %test_func() -> void:
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
            "func private %test_func() -> i8:
    block64:
        v0.i8 = add -1.i8 127.i8;
        v1.i8 = add v0 3.i8;
        jump block1;

    block1:
        v2.i16 = zext -128.i8;
        return v1;"
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
            func private %f1() -> i32:
                block0:
                    return 311.i32;

            # f2 start 1
            # f2 start 2
            func public %f2() -> i32:
                block0:
                    return 311.i32;
            ";

        let parser = Parser::default();
        let parsed_module = parser.parse(input).unwrap();
        let module_comments = parsed_module.module_comments;
        assert_eq!(module_comments[0], " Module comment 1");
        assert_eq!(module_comments[1], " Module comment 2");

        let module = parsed_module.module;
        let mut funcs = module.iter_functions();
        let func1 = funcs.next().unwrap();
        let func1_comment = &parsed_module.func_comments[func1];
        assert_eq!(func1_comment[0], " f1 start 1");
        assert_eq!(func1_comment[1], " f1 start 2");

        let func2 = funcs.next().unwrap();
        let func2_comment = &parsed_module.func_comments[func2];
        assert_eq!(func2_comment[0], " f2 start 1");
        assert_eq!(func2_comment[1], " f2 start 2");
    }

    #[test]
    fn test_with_struct_type() {
        let input = "
            target = \"evm-ethereum-london\"
            
            type %s1 = {i32, i64};
            type %s2_packed = <{i32, i64, *%s1}>;

            func public %test(v0.*%s1, v1.*%s2_packed) -> i32:
                block0:
                    return 311.i32;
            ";

        let parser = Parser::default();
        let module = parser.parse(input).unwrap().module;

        module.ctx.with_ty_store(|s| {
            let ty = s.struct_type_by_name("s1").unwrap();
            let def = s.struct_def(ty).unwrap();
            assert_eq!(def.fields.len(), 2);
            assert_eq!(def.fields[0], Type::I32);
            assert_eq!(def.fields[1], Type::I64);
            assert!(!def.packed);
        });

        let s1_ptr_ty = module.ctx.with_ty_store_mut(|s| {
            let ty = s.struct_type_by_name("s1").unwrap();
            s.make_ptr(ty)
        });
        module.ctx.with_ty_store(|s| {
            let ty = s.struct_type_by_name("s2_packed").unwrap();
            let def = s.struct_def(ty).unwrap();
            assert_eq!(def.fields.len(), 3);
            assert_eq!(def.fields[0], Type::I32);
            assert_eq!(def.fields[1], Type::I64);
            assert_eq!(def.fields[2], s1_ptr_ty);
            assert!(def.packed);
        });
    }

    #[test]
    fn test_with_gv() {
        let input = "
            target = \"evm-ethereum-london\"
            
            gv public const %CONST_PUBLIC: i32 = 1;
            gv external %GLOBAL_EXTERNAL: i32;

            func public %test() -> i32:
                block0:
                    v2.i32 =  add %CONST_PUBLIC %GLOBAL_EXTERNAL;
                    return v2;
            ";

        let parser = Parser::default();
        let module = parser.parse(input).unwrap().module;

        module.ctx.with_gv_store(|s| {
            let symbol = "CONST_PUBLIC";
            let gv = s.gv_by_symbol(symbol).unwrap();
            let data = s.gv_data(gv);
            assert_eq!(data.symbol, symbol);
            assert_eq!(data.ty, Type::I32);
            assert_eq!(data.linkage, Linkage::Public);
            assert!(data.is_const);
            assert_eq!(data.data, Some(ConstantValue::make_imm(1i32)));
        });

        module.ctx.with_gv_store(|s| {
            let symbol = "GLOBAL_EXTERNAL";
            let gv = s.gv_by_symbol(symbol).unwrap();
            let data = s.gv_data(gv);
            assert_eq!(data.symbol, symbol);
            assert_eq!(data.ty, Type::I32);
            assert_eq!(data.linkage, Linkage::External);
            assert!(!data.is_const);
            assert_eq!(data.data, None)
        });
    }
}
