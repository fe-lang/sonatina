use ast::{StmtKind, ValueDeclaration};
use cranelift_entity::SecondaryMap;
use ir::{
    self,
    builder::{FunctionBuilder, ModuleBuilder},
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    ir_writer::DebugProvider,
    isa::IsaBuilder,
    module::{FuncRef, ModuleCtx},
    InsnData, Module, Signature,
};
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use smallvec::SmallVec;
use smol_str::SmolStr;
use std::hash::BuildHasherDefault;
use syntax::Spanned;

pub mod ast;
mod error;
pub mod syntax;
pub use error::{Error, UndefinedKind};
pub use syntax::Span;

type Bimap<K, V> = bimap::BiHashMap<K, V, BuildHasherDefault<FxHasher>>;

pub struct ParsedModule {
    pub module: Module,
    pub debug: DebugInfo,
}

pub fn parse_module(input: &str) -> Result<ParsedModule, Vec<Error>> {
    let ast = ast::parse(input)?;

    let isa = IsaBuilder::new(ast.target.unwrap()).build();
    let mut builder = ModuleBuilder::new(ModuleCtx::new(isa));

    let mut ctx = BuildCtx::default();

    for st in ast.struct_types {
        let fields = st
            .fields
            .iter()
            .map(|t| ctx.type_(&mut builder, t))
            .collect::<Vec<_>>();
        builder.declare_struct_type(&st.name.0, &fields, false);
    }

    for func in ast.declared_functions {
        let params = func
            .params
            .iter()
            .map(|t| ctx.type_(&mut builder, t))
            .collect::<Vec<_>>();
        let ret_ty = func
            .ret_type
            .as_ref()
            .map(|t| ctx.type_(&mut builder, t))
            .unwrap_or(ir::Type::Void);

        let sig = Signature::new(&func.name.0, func.linkage, &params, ret_ty);
        builder.declare_function(sig);
    }

    for func in ast.functions.iter() {
        let sig = &func.signature;
        let args = sig
            .params
            .iter()
            .map(|decl| ctx.type_(&mut builder, &decl.1))
            .collect::<Vec<_>>();

        let ret_ty = sig
            .ret_type
            .as_ref()
            .map(|t| ctx.type_(&mut builder, t))
            .unwrap_or(ir::Type::Void);
        let sig = Signature::new(&sig.name.0, sig.linkage, &args, ret_ty);

        builder.declare_function(sig);
    }

    let mut func_comments = SecondaryMap::default();

    for func in ast.functions {
        let id = builder.get_func_ref(&func.signature.name.0).unwrap();
        builder = ctx.build_func(builder.build_function(id), id, &func);

        func_comments[id] = func.comments;
    }

    if ctx.errors.is_empty() {
        let module = builder.build();
        Ok(ParsedModule {
            module,
            debug: DebugInfo {
                module_comments: ast.comments,
                func_comments,
                value_names: ctx.value_names,
            },
        })
    } else {
        Err(ctx.errors)
    }
}

pub struct DebugInfo {
    pub module_comments: Vec<String>,
    pub func_comments: SecondaryMap<FuncRef, Vec<String>>,
    pub value_names: FxHashMap<FuncRef, Bimap<ir::ValueId, SmolStr>>,
}

impl DebugProvider for DebugInfo {
    fn value_name(&self, func: FuncRef, value: ir::ValueId) -> Option<&str> {
        let names = self.value_names.get(&func)?;
        names.get_by_left(&value).map(|s| s.as_str())
    }
}

#[derive(Default)]
struct BuildCtx {
    errors: Vec<Error>,
    blocks: FxHashSet<ir::Block>,
    value_names: FxHashMap<FuncRef, Bimap<ir::ValueId, SmolStr>>,
    func_value_names: Bimap<ir::ValueId, SmolStr>,
}

impl BuildCtx {
    fn build_func(
        &mut self,
        mut fb: FunctionBuilder<InsnInserter>,
        func_ref: FuncRef,
        func: &ast::Func,
    ) -> ModuleBuilder {
        self.blocks.clear();

        for (i, ValueDeclaration(name, _ty)) in func.signature.params.iter().enumerate() {
            let value = fb.func.arg_values[i];
            self.name_value(value, name);
        }

        for stmt in func.blocks.iter().flat_map(|b| b.stmts.iter()) {
            if let StmtKind::Define(ValueDeclaration(name, ty), _) = &stmt.kind {
                let ty = self.type_(&mut fb.module_builder, ty);
                self.declare_value(&mut fb.func, name, ty);
            }
        }

        // collect all defined block ids
        self.blocks
            .extend(func.blocks.iter().map(|b| ir::Block(b.id())));
        if let Some(max) = self.blocks.iter().max() {
            while fb.func.dfg.blocks.len() <= max.0 as usize {
                fb.cursor.make_block(&mut fb.func);
            }
        }

        for block in &func.blocks {
            let block_id = ir::Block(block.id());
            fb.cursor.append_block(&mut fb.func, block_id);
            fb.cursor.set_location(CursorLocation::BlockTop(block_id));

            for stmt in &block.stmts {
                match &stmt.kind {
                    ast::StmtKind::Define(ValueDeclaration(name, type_), expr) => {
                        let ty = self.type_(&mut fb.module_builder, type_);
                        let err_count = self.errors.len();

                        let insn_data = match expr {
                            ast::Expr::Binary(op, lhs, rhs) => {
                                let lhs = self.value(&mut fb, lhs);
                                let rhs = self.value(&mut fb, rhs);
                                InsnData::Binary {
                                    code: *op,
                                    args: [lhs, rhs],
                                }
                            }
                            ast::Expr::Unary(op, val) => {
                                let val = self.value(&mut fb, val);
                                InsnData::Unary {
                                    code: *op,
                                    args: [val],
                                }
                            }
                            ast::Expr::Cast(op, val) => {
                                let val = self.value(&mut fb, val);
                                InsnData::Cast {
                                    code: *op,
                                    args: [val],
                                    ty,
                                }
                            }
                            ast::Expr::Load(location, addr) => {
                                let addr = self.value(&mut fb, addr);
                                InsnData::Load {
                                    args: [addr],
                                    loc: *location,
                                }
                            }
                            ast::Expr::Alloca(ty) => {
                                let ty = self.type_(&mut fb.module_builder, ty);
                                InsnData::Alloca { ty }
                            }
                            ast::Expr::Call(ast::Call(name, args)) => {
                                let func = self.func_ref(&mut fb.module_builder, name);

                                let args: smallvec::SmallVec<[ir::ValueId; 8]> =
                                    args.iter().map(|val| self.value(&mut fb, val)).collect();

                                let sig = fb.module_builder.get_sig(func).clone();
                                let ret_ty = sig.ret_ty();
                                fb.func.callees.insert(func, sig);

                                InsnData::Call { func, args, ret_ty }
                            }
                            ast::Expr::Gep(vals) => {
                                let args: SmallVec<[ir::ValueId; 8]> =
                                    vals.iter().map(|val| self.value(&mut fb, val)).collect();
                                InsnData::Gep { args }
                            }
                            ast::Expr::Phi(vals) => InsnData::Phi {
                                values: vals
                                    .iter()
                                    .map(|(val, _)| self.value(&mut fb, val))
                                    .collect(),
                                blocks: vals.iter().map(|(_, block)| self.block(block)).collect(),
                                ty,
                            },
                        };

                        // Report declared type mismatch if no error has been reported for this stmt
                        let inferred_ty = insn_data.result_type(&fb.func.dfg).unwrap();
                        if self.errors.len() == err_count && ty != inferred_ty {
                            self.errors.push(Error::TypeMismatch {
                                specified: ty.to_string(&fb.func.dfg).into(),
                                inferred: inferred_ty.to_string(&fb.func.dfg).into(),
                                span: type_.span,
                            });
                        }

                        // xxx cleanup
                        let value = *self.func_value_names.get_by_right(&name.string).unwrap();
                        let insn = fb.cursor.insert_insn_data(&mut fb.func, insn_data);
                        fb.func.dfg.values[value] = ir::Value::Insn { insn, ty };
                        fb.cursor.attach_result(&mut fb.func, insn, value);
                        fb.cursor.set_location(CursorLocation::At(insn));
                    }
                    ast::StmtKind::Store(loc, addr, val) => {
                        let addr = self.value(&mut fb, addr);
                        let val = self.value(&mut fb, val);

                        match loc {
                            ir::DataLocationKind::Memory => fb.memory_store(addr, val),
                            ir::DataLocationKind::Storage => fb.storage_store(addr, val),
                        }
                    }
                    ast::StmtKind::Return(val) => {
                        let val = val.as_ref().map(|v| self.value(&mut fb, v));
                        fb.ret(val);
                    }
                    ast::StmtKind::Jump(block_id) => {
                        let block_id = self.block(block_id);
                        fb.jump(block_id);
                    }
                    ast::StmtKind::Branch(cond, true_block, false_block) => {
                        let cond = self.value(&mut fb, cond);
                        let true_block = self.block(true_block);
                        let false_block = self.block(false_block);
                        fb.br(cond, true_block, false_block);
                    }
                    ast::StmtKind::BranchTable(index, default_block, table) => {
                        let index = self.value(&mut fb, index);
                        let default_block = default_block.as_ref().map(|b| self.block(b));

                        let table = table
                            .iter()
                            .map(|(val, block)| {
                                let block = self.block(block);
                                (self.value(&mut fb, val), block)
                            })
                            .collect::<Vec<_>>();
                        fb.br_table(index, default_block, &table);
                    }
                    ast::StmtKind::Call(ast::Call(name, args)) => {
                        let func_ref = self.func_ref(&mut fb.module_builder, name);

                        let args = args
                            .iter()
                            .map(|val| self.value(&mut fb, val))
                            .collect::<Vec<_>>();
                        fb.call(func_ref, &args).unwrap();
                    }
                }
            }
        }

        let names = std::mem::take(&mut self.func_value_names);
        self.value_names.insert(func_ref, names);
        fb.seal_all();
        fb.finish()
    }

    fn func_ref(&mut self, mb: &mut ModuleBuilder, name: &Spanned<ast::FunctionName>) -> FuncRef {
        mb.get_func_ref(&name.inner.0).unwrap_or_else(|| {
            self.errors.push(Error::Undefined(
                UndefinedKind::Func(name.inner.0.clone()),
                name.span,
            ));
            FuncRef::from_u32(0)
        })
    }

    fn block(&mut self, b: &ast::BlockId) -> ir::Block {
        let block = ir::Block(b.id.unwrap());
        if !self.blocks.contains(&block) {
            self.errors
                .push(Error::Undefined(UndefinedKind::Block(block), b.span));
        }
        block
    }

    fn declare_value(&mut self, func: &mut ir::Function, name: &ast::ValueName, ty: ir::Type) {
        // Abusing Immediate here; we just need a dummy value with a given type.
        // The Value will be replaced when create the Insn that defines the value.
        let value = func.dfg.make_value(ir::Value::Immediate {
            imm: ir::Immediate::I128(424242),
            ty,
        });
        if self
            .func_value_names
            .insert_no_overwrite(value, name.string.clone())
            .is_err()
        {
            self.errors
                .push(Error::DuplicateValueName(name.string.clone(), name.span));
        }
    }

    fn name_value(&mut self, value: ir::ValueId, name: &ast::ValueName) {
        if self.func_value_names.contains_right(&name.string) {
            self.errors
                .push(Error::DuplicateValueName(name.string.clone(), name.span));
        }
        self.func_value_names.insert(value, name.string.clone());
    }

    fn value(&mut self, fb: &mut FunctionBuilder<InsnInserter>, val: &ast::Value) -> ir::ValueId {
        match &val.kind {
            ast::ValueKind::Immediate(imm) => fb.make_imm_value(*imm),
            ast::ValueKind::Named(name) => self
                .func_value_names
                .get_by_right(&name.string)
                .copied()
                .unwrap_or_else(|| {
                    self.errors.push(Error::Undefined(
                        UndefinedKind::Value(name.string.clone()),
                        name.span,
                    ));
                    ir::ValueId(0)
                }),
            ast::ValueKind::Error => unreachable!(),
        }
    }

    fn type_(&mut self, mb: &mut ModuleBuilder, t: &ast::Type) -> ir::Type {
        match &t.kind {
            ast::TypeKind::Int(i) => (*i).into(),
            ast::TypeKind::Ptr(t) => {
                let t = self.type_(mb, t);
                mb.ptr_type(t)
            }
            ast::TypeKind::Array(t, n) => {
                let elem = self.type_(mb, t);
                mb.declare_array_type(elem, *n)
            }
            ast::TypeKind::Void => ir::Type::Void,
            ast::TypeKind::Struct(name) => mb.get_struct_type(name).unwrap_or_else(|| {
                self.errors
                    .push(Error::Undefined(UndefinedKind::Type(name.clone()), t.span));
                ir::Type::Void
            }),
            ast::TypeKind::Error => unreachable!(),
        }
    }
}
