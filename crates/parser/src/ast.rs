use std::str::FromStr;

// `Span`s aren't printed in the Debug output because the pest
// code locations differ on windows vs *nix, which breaks the ast tests.
use derive_more::Debug as Dbg;
use either::Either;
use hex::FromHex;
pub use ir::{Immediate, Linkage};
use ir::{I256, U256};
use pest::Parser as _;
use smol_str::SmolStr;
pub use sonatina_triple::{InvalidTriple, TargetTriple};

use super::{syntax::Node, Error};
use crate::{
    syntax::{FromSyntax, Parser, Rule},
    Span,
};

pub fn parse(input: &str) -> Result<Module, Vec<Error>> {
    match Parser::parse(Rule::module, input) {
        Err(err) => Err(vec![Error::SyntaxError(err)]),
        Ok(mut pairs) => {
            let pair = pairs.next().unwrap();
            debug_assert_eq!(pair.as_rule(), Rule::module);
            let mut node = Node::new(pair);

            let module = Module::from_syntax(&mut node);

            if node.errors.is_empty() {
                Ok(module)
            } else {
                Err(node.errors)
            }
        }
    }
}

#[derive(Debug)]
pub struct Module {
    pub target: Option<TargetTriple>,
    pub declared_functions: Vec<FuncDeclaration>,
    pub struct_types: Vec<Struct>,
    pub functions: Vec<Func>,
    pub comments: Vec<String>,
}

impl FromSyntax<Error> for Module {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let target = node.single(Rule::target_triple);

        let module_comments = node.map_while(|p| {
            if p.as_rule() == Rule::COMMENT && p.as_str().starts_with("#!") {
                Either::Right(p.as_str().into())
            } else {
                Either::Left(p)
            }
        });

        let mut struct_types = vec![];
        let mut declared_functions = vec![];
        let mut functions = vec![];

        loop {
            let comments = node.map_while(|p| {
                if p.as_rule() == Rule::COMMENT {
                    Either::Right(p.as_str().to_string())
                } else {
                    Either::Left(p)
                }
            });

            if let Some(struct_) = node.single_opt(Rule::struct_declaration) {
                struct_types.push(struct_);
            } else if let Some(func) = node.single_opt(Rule::function_declaration) {
                declared_functions.push(func);
            } else {
                match node.single_opt::<Func>(Rule::function) {
                    Some(mut func) => {
                        func.comments = comments;
                        functions.push(func);
                    }
                    None => break,
                }
            }
        }
        Module {
            target,
            declared_functions,
            struct_types,
            functions,
            comments: module_comments,
        }
    }
}

impl FromSyntax<Error> for Option<TargetTriple> {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        match TargetTriple::parse(node.txt) {
            Ok(t) => Some(t),
            Err(e) => {
                node.error(Error::InvalidTarget(e, node.span));
                None
            }
        }
    }
}

impl FromSyntax<Error> for SmolStr {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        node.txt.into()
    }
}

#[derive(Debug)]
pub struct FuncDeclaration {
    pub linkage: Linkage,
    pub name: FunctionName,
    pub params: Vec<Type>,
    pub ret_type: Option<Type>,
}

impl FromSyntax<Error> for FuncDeclaration {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let linkage = node
            .parse_str_opt(Rule::function_linkage)
            .unwrap_or(Linkage::Private);

        FuncDeclaration {
            linkage,
            name: node.single(Rule::function_identifier),
            params: node.descend_into(Rule::function_param_type_list, |n| n.multi(Rule::type_name)),
            ret_type: node.descend_into_opt(Rule::function_ret_type, |n| n.single(Rule::type_name)),
        }
    }
}

#[derive(Debug)]
pub struct Struct {
    pub name: StructName,
    pub fields: Vec<Type>,
    pub packed: bool,
}

impl FromSyntax<Error> for Struct {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let name = node.single(Rule::struct_identifier);
        node.descend();
        let (fields, packed) = match node.rule {
            Rule::normal_field_list => (node.multi(Rule::type_name), false),
            Rule::packed_field_list => (node.multi(Rule::type_name), true),
            _ => unreachable!(),
        };

        Self {
            name,
            fields,
            packed,
        }
    }
}

#[derive(Debug)]
pub struct StructName(pub SmolStr);

impl FromSyntax<Error> for StructName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self(node.single(Rule::struct_name))
    }
}

#[derive(Debug)]
pub struct Func {
    pub signature: FuncSignature,
    pub blocks: Vec<Block>,
    pub comments: Vec<String>,
}

impl FromSyntax<Error> for Func {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Func {
            signature: node.single(Rule::function_signature),
            blocks: node.multi(Rule::block),
            comments: vec![],
        }
    }
}

#[derive(Debug)]
pub struct FuncSignature {
    pub linkage: Linkage,
    pub name: FunctionName,
    pub params: Vec<ValueDeclaration>,
    pub ret_type: Option<Type>,
}

impl FromSyntax<Error> for FuncSignature {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let linkage = node
            .parse_str_opt(Rule::function_linkage)
            .unwrap_or(Linkage::Private);

        FuncSignature {
            linkage,
            name: node.single(Rule::function_identifier),
            params: node.descend_into(Rule::function_params, |n| n.multi(Rule::value_declaration)),
            ret_type: node.descend_into_opt(Rule::function_ret_type, |n| n.single(Rule::type_name)),
        }
    }
}

/// Doesn't include `%` prefix.
#[derive(Debug)]
pub struct FunctionName {
    pub name: SmolStr,
    pub span: Span,
}

impl FromSyntax<Error> for FunctionName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        FunctionName {
            name: node.parse_str(Rule::function_name),
            span: node.span,
        }
    }
}

#[derive(Debug)]
pub struct Block {
    pub id: BlockId,
    pub stmts: Vec<Stmt>,
}

impl Block {
    pub fn id(&self) -> u32 {
        self.id.id.unwrap()
    }
}
impl FromSyntax<Error> for Block {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self {
            id: node.single(Rule::block_ident),
            stmts: node.multi(Rule::stmt),
        }
    }
}

#[derive(Dbg)]
pub struct BlockId {
    pub id: Option<u32>,
    #[debug(skip)]
    pub span: Span,
}

impl FromSyntax<Error> for BlockId {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let span = node.span;
        node.descend();
        debug_assert_eq!(node.rule, Rule::block_number);
        let id = node.txt.parse().ok();
        if id.is_none() {
            node.error(Error::NumberOutOfBounds(node.span));
        }
        BlockId { id, span }
    }
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

impl FromSyntax<Error> for Stmt {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        node.descend();
        let kind = match node.rule {
            Rule::assign_stmt => StmtKind::Assign(
                node.single(Rule::value_declaration),
                node.single(Rule::inst),
            ),
            Rule::inst_stmt => StmtKind::Inst(node.single(Rule::inst)),
            _ => unreachable!(),
        };

        Stmt {
            kind,
            span: node.span,
        }
    }
}

#[derive(Debug)]
pub enum StmtKind {
    Assign(ValueDeclaration, Inst),
    Inst(Inst),
}

#[derive(Debug)]
pub struct Inst {
    pub name: InstName,
    pub args: Vec<InstArg>,
    pub span: Span,
}

impl FromSyntax<Error> for Inst {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let name = node.single(Rule::inst_name);
        let args = node.multi(Rule::inst_arg);
        Self {
            name,
            args,
            span: node.span,
        }
    }
}

#[derive(Dbg)]
pub struct InstName {
    pub name: SmolStr,
    #[debug(skip)]
    pub span: Span,
}

impl FromSyntax<Error> for InstName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        InstName {
            name: node.parse_str(Rule::inst_identifier),
            span: node.span,
        }
    }
}

#[derive(Dbg)]
pub struct InstArg {
    pub kind: InstArgKind,
    #[debug(skip)]
    pub span: Span,
}

impl InstArg {
    pub fn expect_value(&self) -> Result<&Value, Box<Error>> {
        if let InstArgKind::Value(value) = &self.kind {
            Ok(value)
        } else {
            Err(Box::new(Error::InstArgKindMismatch {
                expected: "value".into(),
                actual: self.kind.discriminant_name().into(),
                span: self.span,
            }))
        }
    }
}

impl<'a> TryFrom<&'a InstArg> for &'a Value {
    type Error = Box<Error>;

    fn try_from(arg: &'a InstArg) -> Result<Self, Self::Error> {
        if let InstArgKind::Value(value) = &arg.kind {
            Ok(value)
        } else {
            Err(Box::new(Error::InstArgKindMismatch {
                expected: "value".into(),
                actual: arg.kind.discriminant_name().into(),
                span: arg.span,
            }))
        }
    }
}

impl<'a> TryFrom<&'a InstArg> for &'a Type {
    type Error = Box<Error>;

    fn try_from(arg: &'a InstArg) -> Result<Self, Self::Error> {
        if let InstArgKind::Ty(ty) = &arg.kind {
            Ok(ty)
        } else {
            Err(Box::new(Error::InstArgKindMismatch {
                expected: "type".into(),
                actual: arg.kind.discriminant_name().into(),
                span: arg.span,
            }))
        }
    }
}

impl<'a> TryFrom<&'a InstArg> for &'a BlockId {
    type Error = Box<Error>;

    fn try_from(arg: &'a InstArg) -> Result<Self, Self::Error> {
        if let InstArgKind::Block(block) = &arg.kind {
            Ok(block)
        } else {
            Err(Box::new(Error::InstArgKindMismatch {
                expected: "block".into(),
                actual: arg.kind.discriminant_name().into(),
                span: arg.span,
            }))
        }
    }
}

impl<'a> TryFrom<&'a InstArg> for (&'a Value, &'a BlockId) {
    type Error = Box<Error>;

    fn try_from(arg: &'a InstArg) -> Result<Self, Self::Error> {
        if let InstArgKind::ValueBlockMap(map) = &arg.kind {
            Ok((&map.0, &map.1))
        } else {
            Err(Box::new(Error::InstArgKindMismatch {
                expected: "(value, block)".into(),
                actual: arg.kind.discriminant_name().into(),
                span: arg.span,
            }))
        }
    }
}

impl<'a> TryFrom<&'a InstArg> for &'a FunctionName {
    type Error = Box<Error>;

    fn try_from(arg: &'a InstArg) -> Result<Self, Self::Error> {
        if let InstArgKind::FuncRef(name) = &arg.kind {
            Ok(name)
        } else {
            Err(Box::new(Error::InstArgKindMismatch {
                expected: "function name".into(),
                actual: arg.kind.discriminant_name().into(),
                span: arg.span,
            }))
        }
    }
}

impl FromSyntax<Error> for InstArg {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        let kind = if let Some(value) = node.single_opt(Rule::value) {
            InstArgKind::Value(value)
        } else if let Some(ty) = node.single_opt(Rule::type_name) {
            InstArgKind::Ty(ty)
        } else if let Some(block) = node.single_opt(Rule::block_ident) {
            InstArgKind::Block(block)
        } else if let Some(vb_map) = node.single_opt(Rule::value_block_map) {
            InstArgKind::ValueBlockMap(vb_map)
        } else if let Some(func) = node.single_opt(Rule::function_identifier) {
            InstArgKind::FuncRef(func)
        } else {
            unreachable!()
        };

        Self {
            kind,
            span: node.span,
        }
    }
}

#[derive(Debug)]
pub enum InstArgKind {
    Value(Value),
    Ty(Type),
    Block(BlockId),
    ValueBlockMap((Value, BlockId)),
    FuncRef(FunctionName),
}

impl InstArgKind {
    fn discriminant_name(&self) -> SmolStr {
        match self {
            Self::Value(_) => "value",
            Self::Ty(_) => "type",
            Self::Block(_) => "block",
            Self::ValueBlockMap(_) => "(value, block)",
            Self::FuncRef(_) => "function name",
        }
        .into()
    }
}

impl FromSyntax<Error> for (Value, BlockId) {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        (node.single(Rule::value), node.single(Rule::block_ident))
    }
}

#[derive(Dbg)]
pub struct Type {
    pub kind: TypeKind,
    #[debug(skip)]
    pub span: Span,
}

impl FromSyntax<Error> for Type {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        node.descend();
        let kind = match node.rule {
            Rule::primitive_type => TypeKind::Int(IntType::from_str(node.txt).unwrap()),
            Rule::ptr_type => TypeKind::Ptr(Box::new(node.single(Rule::type_name))),
            Rule::array_type => {
                let Ok(size) = usize::from_str(node.get(Rule::array_size).as_str()) else {
                    node.error(Error::NumberOutOfBounds(node.span));
                    return Type {
                        kind: TypeKind::Error,
                        span: node.span,
                    };
                };
                TypeKind::Array(Box::new(node.single(Rule::type_name)), size)
            }
            Rule::unit_type => TypeKind::Unit,
            Rule::struct_identifier => TypeKind::Struct(node.parse_str(Rule::struct_name)),
            _ => unreachable!(),
        };
        Type {
            kind,
            span: node.span,
        }
    }
}

#[derive(Debug)]
pub enum TypeKind {
    Int(IntType),
    Ptr(Box<Type>),
    Array(Box<Type>, usize),
    Struct(SmolStr),
    Unit,
    Error,
}

#[derive(Debug, Clone, Copy)]
pub enum IntType {
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
}

impl From<IntType> for ir::Type {
    fn from(value: IntType) -> Self {
        match value {
            IntType::I1 => ir::Type::I1,
            IntType::I8 => ir::Type::I8,
            IntType::I16 => ir::Type::I16,
            IntType::I32 => ir::Type::I32,
            IntType::I64 => ir::Type::I64,
            IntType::I128 => ir::Type::I128,
            IntType::I256 => ir::Type::I256,
        }
    }
}

#[derive(Dbg)]
pub struct ValueName {
    pub string: SmolStr,
    #[debug(skip)]
    pub span: Span,
}

impl FromSyntax<Error> for ValueName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self {
            string: node.txt.into(),
            span: node.span,
        }
    }
}

#[derive(Debug)]
pub struct ValueDeclaration(pub ValueName, pub Type);

impl FromSyntax<Error> for ValueDeclaration {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        ValueDeclaration(node.single(Rule::value_name), node.single(Rule::type_name))
    }
}

#[derive(Dbg)]
pub struct Value {
    pub kind: ValueKind,
    #[debug(skip)]
    pub span: Span,
}

#[derive(Debug)]
pub enum ValueKind {
    Immediate(Immediate),
    Named(ValueName),
    Error,
}

macro_rules! parse_dec {
    ($node:ident, $imm:expr, $ity:ty, $uty:ty) => {
        match $node
            .txt
            .parse::<$ity>()
            .or_else(|_| $node.txt.parse::<$uty>().map(|v| v as $ity))
        {
            Ok(v) => ValueKind::Immediate($imm(v)),
            Err(_) => {
                $node.error(Error::NumberOutOfBounds($node.span));
                ValueKind::Error
            }
        }
    };
}

macro_rules! parse_hex {
    ($node:ident, $imm:expr, $ity:ty) => {
        if let Some(bytes) = hex_bytes($node.txt) {
            ValueKind::Immediate($imm(<$ity>::from_be_bytes(bytes)))
        } else {
            ValueKind::Error
        }
    };
}

impl FromSyntax<Error> for Value {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        node.descend();
        let kind = match node.rule {
            Rule::value_name => ValueKind::Named(ValueName::from_syntax(node)),
            Rule::imm_number => {
                let ty: IntType = node.parse_str(Rule::primitive_type);
                node.descend();
                let mut txt = node.txt;
                match node.rule {
                    Rule::decimal => match ty {
                        IntType::I1 => imm_or_err(node, || {
                            let b = match u8::from_str(txt).ok()? {
                                0 => false,
                                1 => true,
                                _ => return None,
                            };
                            Some(Immediate::I1(b))
                        }),
                        IntType::I8 => parse_dec!(node, Immediate::I8, i8, u8),
                        IntType::I16 => parse_dec!(node, Immediate::I16, i16, u16),
                        IntType::I32 => parse_dec!(node, Immediate::I32, i32, u32),
                        IntType::I64 => parse_dec!(node, Immediate::I64, i64, u64),
                        IntType::I128 => parse_dec!(node, Immediate::I128, i128, u128),

                        IntType::I256 => {
                            let s = txt.strip_prefix('-');
                            let is_negative = s.is_some();
                            txt = s.unwrap_or(txt);

                            imm_or_err(node, || {
                                let mut i256 = U256::from_dec_str(txt).ok()?.into();
                                if is_negative {
                                    i256 = I256::zero().overflowing_sub(i256).0;
                                }
                                Some(Immediate::I256(i256))
                            })
                        }
                    },

                    Rule::hex => match ty {
                        IntType::I1 => {
                            node.error(Error::NumberOutOfBounds(node.span));
                            ValueKind::Error
                        }
                        IntType::I8 => parse_hex!(node, Immediate::I8, i8),
                        IntType::I16 => parse_hex!(node, Immediate::I16, i16),
                        IntType::I32 => parse_hex!(node, Immediate::I32, i32),
                        IntType::I64 => parse_hex!(node, Immediate::I64, i64),
                        IntType::I128 => parse_hex!(node, Immediate::I128, i128),
                        IntType::I256 => {
                            let s = txt.strip_prefix('-');
                            let is_negative = s.is_some();
                            txt = s.unwrap_or(txt);

                            if let Some(bytes) = hex_bytes::<32>(txt) {
                                let mut i256 = U256::from_big_endian(&bytes).into();
                                if is_negative {
                                    i256 = I256::zero().overflowing_sub(i256).0;
                                }
                                ValueKind::Immediate(Immediate::I256(i256))
                            } else {
                                node.error(Error::NumberOutOfBounds(node.span));
                                ValueKind::Error
                            }
                        }
                    },
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        };
        Value {
            kind,
            span: node.span,
        }
    }
}

impl FromStr for IntType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i1" => Ok(Self::I1),
            "i8" => Ok(Self::I8),
            "i16" => Ok(Self::I16),
            "i32" => Ok(Self::I32),
            "i64" => Ok(Self::I64),
            "i128" => Ok(Self::I128),
            "i256" => Ok(Self::I256),
            _ => Err(()),
        }
    }
}

fn imm_or_err<F>(node: &mut Node<Error>, f: F) -> ValueKind
where
    F: Fn() -> Option<Immediate>,
{
    let Some(imm) = f() else {
        let span = node.span;
        node.error(Error::NumberOutOfBounds(span));
        return ValueKind::Error;
    };
    ValueKind::Immediate(imm)
}

fn hex_bytes<const N: usize>(mut s: &str) -> Option<[u8; N]> {
    s = s.strip_prefix("0x").unwrap();
    let bytes = Vec::<u8>::from_hex(s).unwrap();

    if bytes.len() > N {
        return None;
    }

    let mut out = [0; N];
    out[N - bytes.len()..].copy_from_slice(&bytes);
    Some(out)
}
