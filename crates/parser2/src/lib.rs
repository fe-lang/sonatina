use ast::{Error, ValueDeclaration};
use cranelift_entity::SecondaryMap;
use ir::{
    self,
    builder::{FunctionBuilder, ModuleBuilder},
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    isa::IsaBuilder,
    module::{FuncRef, ModuleCtx},
    Module, Signature,
};

pub mod ast;
pub mod syntax;

pub fn parse_module(input: &str) -> Result<ParsedModule, Vec<Error>> {
    let ast = ast::parse(input)?;

    let isa = IsaBuilder::new(ast.target.unwrap()).build(); // xxx
    let ctx = ModuleCtx::new(isa);
    let mut builder = ModuleBuilder::new(ctx);

    for st in ast.struct_types {
        let fields = st
            .fields
            .iter()
            .map(|t| build_type(&mut builder, t))
            .collect::<Vec<_>>();
        builder.declare_struct_type(&st.name.0, &fields, false);
    }

    for func in ast.declared_functions {
        let params = func
            .params
            .iter()
            .map(|t| build_type(&mut builder, t))
            .collect::<Vec<_>>();
        let ret_ty = func
            .ret_type
            .as_ref()
            .map(|t| build_type(&mut builder, t))
            .unwrap_or(ir::Type::Void);

        let sig = Signature::new(&func.name.0, func.linkage, &params, ret_ty);
        builder.declare_function(sig);
    }

    for func in ast.functions.iter() {
        let sig = &func.signature;
        let args = sig
            .params
            .iter()
            .map(|decl| build_type(&mut builder, &decl.1))
            .collect::<Vec<_>>();

        let ret_ty = sig
            .ret_type
            .as_ref()
            .map(|t| build_type(&mut builder, t))
            .unwrap_or(ir::Type::Void);
        let sig = Signature::new(&sig.name.0, sig.linkage, &args, ret_ty);

        builder.declare_function(sig);
    }

    let mut func_comments = SecondaryMap::default();

    for func in ast.functions {
        let id = builder.get_func_ref(&func.signature.name.0).unwrap();
        let mut fb = builder.build_function(id);
        build_func(&mut fb, &func);
        fb.seal_all();
        builder = fb.finish();

        func_comments[id] = func.comments;
    }

    let module = builder.build();
    Ok(ParsedModule {
        module,
        module_comments: ast.comments,
        func_comments,
    })
}

pub struct ParsedModule {
    pub module: Module,
    pub module_comments: Vec<String>,
    pub func_comments: SecondaryMap<FuncRef, Vec<String>>,
}

fn build_func(builder: &mut FunctionBuilder<InsnInserter>, func: &ast::Func) {
    for (i, ValueDeclaration(name, _ty)) in func.signature.params.iter().enumerate() {
        builder.name_value(builder.func.arg_values[i], &name.0);
    }

    // "forward declare" all block ids
    if let Some(max_block_id) = func.blocks.iter().map(|b| b.id.0.unwrap()).max() {
        while builder.func.dfg.blocks.len() <= max_block_id as usize {
            builder.cursor.make_block(&mut builder.func);
        }
    }

    for block in &func.blocks {
        let block_id = ir::Block(block.id.0.unwrap());
        builder.cursor.append_block(&mut builder.func, block_id);
        builder
            .cursor
            .set_location(CursorLocation::BlockTop(block_id));

        for stmt in &block.stmts {
            match &stmt.kind {
                ast::StmtKind::Define(ValueDeclaration(val, ty), expr) => {
                    let ty = build_type(&mut builder.module_builder, ty);

                    let result_val = match expr {
                        ast::Expr::Binary(op, lhs, rhs) => {
                            let lhs = build_value(builder, lhs);
                            let rhs = build_value(builder, rhs);
                            builder.binary_op(*op, lhs, rhs)
                        }
                        ast::Expr::Unary(op, val) => {
                            let val = build_value(builder, val);
                            builder.unary_op(*op, val)
                        }
                        ast::Expr::Cast(op, val) => {
                            let val = build_value(builder, val);
                            builder.cast_op(*op, val, ty)
                        }
                        ast::Expr::Load(location, addr) => {
                            let addr = build_value(builder, addr);
                            match location {
                                ir::DataLocationKind::Memory => builder.memory_load(addr),
                                ir::DataLocationKind::Storage => builder.storage_load(addr),
                            }
                        }
                        ast::Expr::Alloca(ty) => {
                            let ty = build_type(&mut builder.module_builder, ty);
                            builder.alloca(ty)
                        }
                        ast::Expr::Call(ast::Call(name, args)) => {
                            let func_ref = builder.module_builder.get_func_ref(&name.0).unwrap();
                            let args = args
                                .iter()
                                .map(|val| build_value(builder, val))
                                .collect::<Vec<_>>();
                            builder.call(func_ref, &args).unwrap()
                        }
                        ast::Expr::Gep(vals) => {
                            let vals = vals
                                .iter()
                                .map(|val| build_value(builder, val))
                                .collect::<Vec<_>>();
                            builder.gep(&vals).unwrap()
                        }
                        ast::Expr::Phi(vals) => {
                            let args = vals
                                .iter()
                                .map(|(val, block)| {
                                    // xxx declare block
                                    let b = ir::Block(block.0.unwrap());
                                    let v = build_value(builder, val);
                                    (v, b)
                                })
                                .collect::<Vec<_>>();
                            builder.phi(ty, &args)
                        }
                    };
                    builder.name_value(result_val, &val.0)
                }
                ast::StmtKind::Store(loc, addr, val) => {
                    let addr = build_value(builder, addr);
                    let val = build_value(builder, val);

                    match loc {
                        ir::DataLocationKind::Memory => builder.memory_store(addr, val),
                        ir::DataLocationKind::Storage => builder.storage_store(addr, val),
                    }
                }
                ast::StmtKind::Return(val) => {
                    let val = val.as_ref().map(|v| build_value(builder, v));
                    builder.ret(val);
                }
                ast::StmtKind::Jump(block_id) => {
                    let block_id = ir::Block(block_id.0.unwrap());
                    builder.jump(block_id);
                }
                ast::StmtKind::Branch(cond, true_block, false_block) => {
                    let cond = build_value(builder, cond);
                    let true_block = ir::Block(true_block.0.unwrap());
                    let false_block = ir::Block(false_block.0.unwrap());
                    builder.br(cond, true_block, false_block);
                }
                ast::StmtKind::BranchTable(index, default_block, table) => {
                    let index = build_value(builder, index);
                    let default_block = default_block.as_ref().map(|b| ir::Block(b.0.unwrap()));
                    let table = table
                        .iter()
                        .map(|(val, block)| {
                            (build_value(builder, val), ir::Block(block.0.unwrap()))
                        })
                        .collect::<Vec<_>>();
                    builder.br_table(index, default_block, &table);
                }
                ast::StmtKind::Call(ast::Call(name, args)) => {
                    let func_ref = builder.module_builder.get_func_ref(&name.0).unwrap();
                    let args = args
                        .iter()
                        .map(|val| build_value(builder, val))
                        .collect::<Vec<_>>();
                    builder.call(func_ref, &args).unwrap();
                }
            }
        }
    }
}

fn build_value(builder: &mut FunctionBuilder<InsnInserter>, val: &ast::Value) -> ir::Value {
    match val {
        ast::Value::Immediate(imm) => builder.make_imm_value(*imm),
        ast::Value::Named(v) => builder.get_named_value(&v.0),
        ast::Value::Error => unreachable!(),
    }
}

fn build_type(builder: &mut ModuleBuilder, t: &ast::Type) -> ir::Type {
    match t {
        ast::Type::Int(i) => (*i).into(),
        ast::Type::Ptr(t) => {
            let t = build_type(builder, t);
            builder.ptr_type(t)
        }
        ast::Type::Array(t, n) => {
            let elem = build_type(builder, t);
            builder.declare_array_type(elem, *n)
        }
        ast::Type::Void => ir::Type::Void,
        ast::Type::Struct(name) => builder.get_struct_type(name).unwrap_or_else(|| {
            // xxx error on undeclared struct
            eprintln!("struct type not found: {name}");
            ir::Type::Void
        }),
        ast::Type::Error => todo!(),
    }
}
