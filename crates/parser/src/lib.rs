use std::hash::BuildHasherDefault;

use ast::{StmtKind, ValueDeclaration};
use cranelift_entity::SecondaryMap;
use inst::InstBuild;
use ir::{
    self,
    builder::{FunctionBuilder, ModuleBuilder},
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    global_variable::GvInitializer,
    ir_writer::{DebugProvider, IrWrite},
    isa::evm::Evm,
    module::{FuncRef, Module, ModuleCtx},
    Function, GlobalVariableData, GlobalVariableRef, Immediate, Signature, Type,
};
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use smol_str::SmolStr;

pub mod ast;
pub mod syntax;
pub use error::{Error, UndefinedKind};
use sonatina_triple::{Architecture, TargetTriple};
pub use syntax::Span;

mod error;
mod inst;

type Bimap<K, V> = bimap::BiHashMap<K, V, BuildHasherDefault<FxHasher>>;
pub use pest::Parser as PestParser;

pub struct ParsedModule {
    pub module: Module,
    pub debug: DebugInfo,
}

pub fn parse_module(input: &str) -> Result<ParsedModule, Vec<Error>> {
    let ast = ast::parse(input)?;

    let module_ctx = module_ctx_from_triple(ast.target.unwrap());
    let builder = ModuleBuilder::new(module_ctx);

    let mut ctx = BuildCtx::default();

    for st in ast.struct_types {
        let fields = st
            .fields
            .iter()
            .map(|t| ctx.type_(&builder, t))
            .collect::<Vec<_>>();
        builder.declare_struct_type(&st.name.0, &fields, false);
    }

    for gv in ast.declared_gvs {
        ctx.declare_gv(&builder, &gv);
    }

    for func in ast.declared_functions {
        if !ctx.check_duplicated_func(&builder, &func.name) {
            continue;
        }

        let params = func
            .params
            .iter()
            .map(|t| ctx.type_(&builder, t))
            .collect::<Vec<_>>();
        let ret_ty = func
            .ret_type
            .as_ref()
            .map(|t| ctx.type_(&builder, t))
            .unwrap_or(ir::Type::Unit);

        let sig = Signature::new(&func.name.name, func.linkage, &params, ret_ty);
        builder.declare_function(sig);
    }

    for func in ast.functions.iter() {
        if !ctx.check_duplicated_func(&builder, &func.signature.name) {
            continue;
        }

        let sig = &func.signature;
        let args = sig
            .params
            .iter()
            .map(|decl| ctx.type_(&builder, &decl.1))
            .collect::<Vec<_>>();

        let ret_ty = sig
            .ret_type
            .as_ref()
            .map(|t| ctx.type_(&builder, t))
            .unwrap_or(ir::Type::Unit);
        let sig = Signature::new(&sig.name.name, sig.linkage, &args, ret_ty);

        builder.declare_function(sig);
    }

    let mut func_comments = SecondaryMap::default();

    for func in ast.functions {
        let id = builder.lookup_func(&func.signature.name.name).unwrap();
        ctx.build_func(builder.func_builder(id), id, &func);

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
    fn value_name(&self, _func: &Function, func_ref: FuncRef, value: ir::ValueId) -> Option<&str> {
        let names = self.value_names.get(&func_ref)?;
        names.get_by_left(&value).map(|s| s.as_str())
    }
}

#[derive(Default)]
struct BuildCtx {
    errors: Vec<Error>,
    blocks: FxHashSet<ir::BlockId>,
    value_names: FxHashMap<FuncRef, Bimap<ir::ValueId, SmolStr>>,
    func_value_names: Bimap<ir::ValueId, SmolStr>,
}

impl BuildCtx {
    fn build_func(
        &mut self,
        mut fb: FunctionBuilder<InstInserter>,
        func_ref: FuncRef,
        func: &ast::Func,
    ) {
        self.blocks.clear();

        for (i, ValueDeclaration(name, _ty)) in func.signature.params.iter().enumerate() {
            let value = fb.func.arg_values[i];
            self.name_value(value, name);
        }

        for stmt in func.blocks.iter().flat_map(|b| b.stmts.iter()) {
            if let StmtKind::Assign(ValueDeclaration(name, ty), _) = &stmt.kind {
                let ty = self.type_(&fb.module_builder, ty);
                self.declare_value(&mut fb.func, name, ty);
            }
        }

        // collect all defined block ids
        self.blocks
            .extend(func.blocks.iter().map(|b| ir::BlockId(b.id())));
        if let Some(max) = self.blocks.iter().max() {
            while fb.func.dfg.blocks.len() <= max.0 as usize {
                fb.cursor.make_block(&mut fb.func);
            }
        }

        for block in &func.blocks {
            let block_id = ir::BlockId(block.id());
            fb.cursor.append_block(&mut fb.func, block_id);
            fb.cursor.set_location(CursorLocation::BlockTop(block_id));

            for stmt in &block.stmts {
                let inst_id = match &stmt.kind {
                    ast::StmtKind::Assign(ValueDeclaration(name, type_), ast_inst) => {
                        let inst = match InstBuild::build(self, &mut fb, ast_inst) {
                            Ok(inst) => inst,
                            Err(err) => {
                                self.errors.push(*err);
                                continue;
                            }
                        };

                        // xxx cleanup
                        let ty = self.type_(&fb.module_builder, type_);
                        let value = *self.func_value_names.get_by_right(&name.string).unwrap();
                        let inst_id = fb.cursor.insert_inst_data_dyn(&mut fb.func, inst);
                        fb.func.dfg.values[value] = ir::Value::Inst { inst: inst_id, ty };
                        fb.cursor.attach_result(&mut fb.func, inst_id, value);
                        inst_id
                    }

                    ast::StmtKind::Inst(ast_inst) => {
                        let inst = match InstBuild::build(self, &mut fb, ast_inst) {
                            Ok(inst) => inst,
                            Err(err) => {
                                self.errors.push(*err);
                                continue;
                            }
                        };

                        fb.cursor.insert_inst_data_dyn(&mut fb.func, inst)
                    }
                };
                fb.cursor.set_location(CursorLocation::At(inst_id));
            }
        }

        let names = std::mem::take(&mut self.func_value_names);
        self.value_names.insert(func_ref, names);
        fb.seal_all();
        fb.finish();
    }

    fn func_ref(&mut self, mb: &mut ModuleBuilder, name: &ast::FunctionName) -> FuncRef {
        mb.lookup_func(&name.name).unwrap_or_else(|| {
            self.errors.push(Error::Undefined(
                UndefinedKind::Func(name.name.clone()),
                name.span,
            ));
            FuncRef::from_u32(0)
        })
    }

    fn block(&mut self, b: &ast::BlockId) -> ir::BlockId {
        let block = ir::BlockId(b.id.unwrap());
        if !self.blocks.contains(&block) {
            self.errors
                .push(Error::Undefined(UndefinedKind::Block(block), b.span));
        }
        block
    }

    fn declare_value(&mut self, func: &mut ir::Function, name: &ast::ValueName, ty: ir::Type) {
        // Abusing Immediate here; we just need a dummy value with a given type.
        // The Value will be replaced when create the Inst that defines the value.
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

    fn value(&mut self, fb: &mut FunctionBuilder<InstInserter>, val: &ast::Value) -> ir::ValueId {
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
            ast::ValueKind::Undef(ty) => {
                let ty = self.type_(&fb.module_builder, ty);
                fb.make_undef_value(ty)
            }
            ast::ValueKind::Global(name) => {
                let Some(gv) = fb.module_builder.lookup_gv(&name.string) else {
                    self.errors.push(Error::Undefined(
                        UndefinedKind::Value(name.string.clone()),
                        val.span,
                    ));
                    return ir::ValueId(0);
                };

                fb.make_global_value(gv)
            }

            ast::ValueKind::Error => unreachable!(),
        }
    }

    fn type_(&mut self, mb: &ModuleBuilder, t: &ast::Type) -> ir::Type {
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
            ast::TypeKind::Unit => ir::Type::Unit,
            ast::TypeKind::Struct(name) => mb
                .lookup_struct(name)
                .map(Type::Compound)
                .unwrap_or_else(|| {
                    self.errors
                        .push(Error::Undefined(UndefinedKind::Type(name.clone()), t.span));
                    ir::Type::Unit
                }),

            ast::TypeKind::Func { args, ret_ty } => {
                let args: Vec<_> = args.iter().map(|t| self.type_(mb, t)).collect();
                let ret_ty = self.type_(mb, ret_ty);
                mb.declare_func_type(&args, ret_ty)
            }

            ast::TypeKind::Error => unreachable!(),
        }
    }

    fn check_duplicated_func(&mut self, mb: &ModuleBuilder, name: &ast::FunctionName) -> bool {
        if mb.lookup_func(&name.name).is_some() {
            self.errors
                .push(Error::DuplicatedDeclaration(name.name.clone(), name.span));
            false
        } else {
            true
        }
    }

    fn declare_gv(
        &mut self,
        mb: &ModuleBuilder,
        ast_gv: &ast::GlobalVariable,
    ) -> GlobalVariableRef {
        let name = &ast_gv.name.string;
        if let Some(gv) = mb.lookup_gv(name) {
            self.errors
                .push(Error::DuplicatedDeclaration(name.clone(), ast_gv.name.span));
            return gv;
        }

        let ty = self.type_(mb, &ast_gv.ty);
        let linkage = ast_gv.linkage;
        let is_const = ast_gv.is_const;
        let init = ast_gv
            .init
            .as_ref()
            .and_then(|init| self.gv_initializer(mb, init, ty));
        let data = GlobalVariableData::new(name.to_string(), ty, linkage, is_const, init);
        mb.declare_gv(data)
    }

    fn gv_initializer(
        &mut self,
        mb: &ModuleBuilder,
        init: &ast::GvInitializer,
        ty: Type,
    ) -> Option<GvInitializer> {
        let mut type_error = |ty: Type| {
            let ty = ty.dump_string(&mb.ctx);
            self.errors.push(Error::TypeError {
                expected: ty,
                span: init.span,
            });
        };

        match &init.kind {
            ast::GvInitializerKind::Immediate(imm) => {
                let ty = if ty.is_integral() {
                    ty
                } else if ty.is_pointer(&mb.ctx) {
                    mb.ctx.type_layout.pointer_repl()
                } else {
                    type_error(ty);
                    return None;
                };

                // TODO: Integer range check.
                let inner = imm.as_i256();
                let imm = Immediate::from_i256(inner, ty);
                Some(GvInitializer::Immediate(imm))
            }

            ast::GvInitializerKind::Array(arr) => {
                let Some((ty, len)) = mb.ctx.with_ty_store(|s| s.array_def(ty)) else {
                    type_error(ty);
                    return None;
                };

                if arr.len() != len {
                    type_error(ty);
                    return None;
                }

                let elems = arr
                    .iter()
                    .map(|elem| self.gv_initializer(mb, elem, ty))
                    .collect::<Option<Vec<_>>>()?;
                Some(GvInitializer::make_array(elems))
            }

            ast::GvInitializerKind::Struct(fields) => {
                let Some(s_data) = mb.ctx.with_ty_store(|s| s.struct_def(ty).cloned()) else {
                    type_error(ty);
                    return None;
                };

                if fields.len() != s_data.fields.len() {
                    type_error(ty);
                    return None;
                }

                let elems = fields
                    .iter()
                    .zip(s_data.fields)
                    .map(|(elem, field_ty)| self.gv_initializer(mb, elem, field_ty))
                    .collect::<Option<Vec<_>>>()?;
                Some(GvInitializer::make_struct(elems))
            }

            &ast::GvInitializerKind::Error => {
                unreachable!();
            }
        }
    }
}

// TODO: Temporary stopgap solution.
// We need to have a proper ISA builder in the near future.
fn module_ctx_from_triple(triple: TargetTriple) -> ModuleCtx {
    match triple.architecture {
        Architecture::Evm => {
            let isa = Evm::new(triple);
            ModuleCtx::new(&isa)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn foo() {
        let s = "     
target = \"evm-ethereum-london\"

# sameln: func public %simple(v0.i8) -> i8 {
# nextln:     block0:
# nextln:         return 2.i8;
func public %simple(v0.i8) -> i8 {
    block0:
        v1.i8 = sub v0 1.i8;
        v2.i8 = evm_udiv v1 v0;
        return 2.i8;
}
";

        assert!(parse_module(s).is_ok());
    }
}
