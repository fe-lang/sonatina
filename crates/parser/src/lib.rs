use std::hash::BuildHasherDefault;

use ast::{StmtKind, ValueDeclaration};
use cranelift_entity::SecondaryMap;
use inst::InstBuild;
use ir::{
    self, Function, GlobalVariableData, GlobalVariableRef, Immediate, Signature, Type,
    builder::{FunctionBuilder, ModuleBuilder},
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    global_variable::GvInitializer,
    ir_writer::{DebugProvider, IrWrite},
    isa::evm::Evm,
    module::{FuncRef, Module, ModuleCtx},
};
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use smallvec::SmallVec;
use smol_str::SmolStr;
use tracing::{debug_span, info_span};

pub mod ast;
pub mod syntax;
pub use error::{Error, UndefinedKind};
pub use objects::parse_object_file;
use sonatina_triple::{Architecture, TargetTriple};
pub use syntax::Span;

mod error;
mod inst;
pub mod objects;

type Bimap<K, V> = bimap::BiHashMap<K, V, BuildHasherDefault<FxHasher>>;
pub use pest::Parser as PestParser;

pub struct ParsedModule {
    pub module: Module,
    pub debug: DebugInfo,
}

pub fn parse_module(input: &str) -> Result<ParsedModule, Vec<Error>> {
    let line_count = input.lines().count();
    let _parse_span = info_span!(
        "sonatina.parse_module",
        input_bytes = input.len(),
        line_count
    )
    .entered();
    let ast = {
        let _span = debug_span!("sonatina.parse.ast").entered();
        ast::parse(input)?
    };

    let module_ctx = module_ctx_from_triple(ast.target.unwrap());
    let mut builder = ModuleBuilder::new(module_ctx);

    let mut ctx = BuildCtx::default();

    {
        let _span = debug_span!("sonatina.parse.declare_structs").entered();
        for st in ast.struct_types {
            let name = &st.name.0;
            builder.declare_struct_type(name, &[], false);

            let fields = st
                .fields
                .iter()
                .map(|t| ctx.type_(&builder, t))
                .collect::<Vec<_>>();
            builder.update_struct_fields(name, &fields);
        }
    }

    {
        let _span = debug_span!("sonatina.parse.declare_globals").entered();
        for gv in ast.declared_gvs {
            ctx.declare_gv(&builder, &gv);
        }
    }

    {
        let _span = debug_span!("sonatina.parse.declare_declared_functions").entered();
        for func in ast.declared_functions {
            if !ctx.check_duplicated_func(&builder, &func.name) {
                continue;
            }

            let params = func
                .params
                .iter()
                .map(|t| ctx.type_(&builder, t))
                .collect::<Vec<_>>();
            let ret_tys = ctx.ret_tys(&builder, &func.ret_types);

            let sig = Signature::new(&func.name.name, func.linkage, &params, &ret_tys);

            // Safe to unwrap: function name checked for duplicate above
            builder.declare_function(sig).unwrap();
        }
    }

    let defined_func_ids = {
        let _span = debug_span!("sonatina.parse.declare_defined_functions").entered();
        ast.functions
            .iter()
            .map(|func| {
                if !ctx.check_duplicated_func(&builder, &func.signature.name) {
                    return None;
                }

                let sig = &func.signature;
                let args = sig
                    .params
                    .iter()
                    .map(|decl| ctx.type_(&builder, &decl.1))
                    .collect::<Vec<_>>();

                let ret_tys = ctx.ret_tys(&builder, &sig.ret_types);
                let sig = Signature::new(&sig.name.name, sig.linkage, &args, &ret_tys);

                // Safe to unwrap: function name checked for duplicate above
                Some(builder.declare_function(sig).unwrap())
            })
            .collect::<Vec<_>>()
    };
    let func_order = defined_func_ids.iter().flatten().copied().collect();

    let mut func_comments = SecondaryMap::default();

    {
        let _span = debug_span!("sonatina.parse.build_functions").entered();
        for (func, id) in ast.functions.into_iter().zip(defined_func_ids) {
            let Some(id) = id else {
                continue;
            };
            ctx.build_func(builder.func_builder(id), id, &func);

            func_comments[id] = func.comments;
        }
    }

    {
        let _span = debug_span!("sonatina.parse.lower_objects").entered();
        for obj_def in ast.objects {
            let name = obj_def.object.name.0.clone();

            if let Some(object) = ctx.lower_object(&builder, obj_def.object, obj_def.span)
                && builder.declare_object(object).is_err()
            {
                ctx.errors
                    .push(Error::DuplicatedDeclaration(name, obj_def.span));
            }
        }
    }

    if !ctx.errors.is_empty() {
        return Err(ctx.errors);
    }

    let module = {
        let _span = debug_span!("sonatina.parse.build_module").entered();
        builder.build()
    };
    Ok(ParsedModule {
        module,
        debug: DebugInfo {
            func_order,
            module_comments: ast.comments,
            func_comments,
            value_names: ctx.value_names,
        },
    })
}

pub struct DebugInfo {
    pub func_order: Vec<FuncRef>,
    pub module_comments: Vec<String>,
    pub func_comments: SecondaryMap<FuncRef, Vec<String>>,
    pub value_names: FxHashMap<FuncRef, Bimap<ir::ValueId, SmolStr>>,
}

impl DebugInfo {
    pub fn value(&self, func: FuncRef, name: &str) -> Option<ir::ValueId> {
        self.value_names.get(&func)?.get_by_right(name).copied()
    }
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
        let mut assign_result_values: Vec<SmallVec<[Option<ir::ValueId>; 2]>> = Vec::new();

        for (i, ValueDeclaration(name, _ty)) in func.signature.params.iter().enumerate() {
            let value = fb.func.arg_values[i];
            self.name_value(value, name);
        }

        for stmt in func.blocks.iter().flat_map(|b| b.stmts.iter()) {
            if let StmtKind::Assign(values, _) = &stmt.kind {
                let declared_values: SmallVec<[Option<ir::ValueId>; 2]> = values
                    .iter()
                    .map(|ValueDeclaration(name, ty)| {
                        let ty = self.type_(&fb.module_builder, ty);
                        self.declare_value(&mut fb.func, name, ty)
                    })
                    .collect();
                assign_result_values.push(declared_values);
            }
        }
        let mut assign_result_values = assign_result_values.into_iter();

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
                    ast::StmtKind::Assign(values, ast_inst) => {
                        let declared_values = assign_result_values
                            .next()
                            .expect("predeclared assignment values must exist");
                        let inst: Box<dyn ir::Inst> =
                            match InstBuild::build(self, &mut fb, ast_inst) {
                                Ok(inst) => inst,
                                Err(err) => {
                                    self.errors.push(*err);
                                    continue;
                                }
                            };

                        let inst_id = fb.cursor.insert_inst_data_dyn(&mut fb.func, inst);
                        let result_values: SmallVec<[ir::ValueId; 2]> = values
                            .iter()
                            .zip(declared_values)
                            .enumerate()
                            .filter_map(|(result_idx, (ValueDeclaration(_, type_), value))| {
                                let value = value?;
                                let ty = self.type_(&fb.module_builder, type_);
                                fb.func.dfg.values[value] = ir::Value::Inst {
                                    inst: inst_id,
                                    result_idx: result_idx
                                        .try_into()
                                        .expect("too many instruction results"),
                                    ty,
                                };
                                Some(value)
                            })
                            .collect();
                        fb.cursor
                            .attach_results(&mut fb.func, inst_id, &result_values);
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

    fn declare_value(
        &mut self,
        func: &mut ir::Function,
        name: &ast::ValueName,
        ty: ir::Type,
    ) -> Option<ir::ValueId> {
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
            None
        } else {
            Some(value)
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

            ast::TypeKind::Func { args, ret_tys } => {
                let args: Vec<_> = args.iter().map(|t| self.type_(mb, t)).collect();
                let ret_tys = self.ret_tys(mb, ret_tys);
                mb.declare_func_type(&args, &ret_tys)
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

    fn ret_tys(&mut self, mb: &ModuleBuilder, ret_tys: &[ast::Type]) -> Vec<ir::Type> {
        let ret_tys: Vec<_> = ret_tys.iter().map(|ty| self.type_(mb, ty)).collect();
        if ret_tys.as_slice() == [ir::Type::Unit] {
            vec![]
        } else {
            ret_tys
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

    fn lower_object(
        &mut self,
        mb: &ModuleBuilder,
        object: crate::objects::Object,
        span: Span,
    ) -> Option<ir::Object> {
        let mut has_error = false;

        let mut sections = Vec::with_capacity(object.sections.len());
        for section in object.sections {
            let mut directives = Vec::with_capacity(section.directives.len());
            for directive in section.directives {
                let lowered = match directive {
                    crate::objects::Directive::Entry(name) => {
                        match mb.lookup_func(name.0.as_str()) {
                            Some(func) => ir::object::Directive::Entry(func),
                            None => {
                                self.errors.push(Error::Undefined(
                                    UndefinedKind::Func(name.0.clone()),
                                    span,
                                ));
                                has_error = true;
                                ir::object::Directive::Entry(FuncRef::from_u32(0))
                            }
                        }
                    }
                    crate::objects::Directive::Include(name) => {
                        match mb.lookup_func(name.0.as_str()) {
                            Some(func) => ir::object::Directive::Include(func),
                            None => {
                                self.errors.push(Error::Undefined(
                                    UndefinedKind::Func(name.0.clone()),
                                    span,
                                ));
                                has_error = true;
                                ir::object::Directive::Include(FuncRef::from_u32(0))
                            }
                        }
                    }
                    crate::objects::Directive::Data(name) => match mb.lookup_gv(name.0.as_str()) {
                        Some(gv) => ir::object::Directive::Data(gv),
                        None => {
                            self.errors
                                .push(Error::Undefined(UndefinedKind::Value(name.0.clone()), span));
                            has_error = true;
                            ir::object::Directive::Data(GlobalVariableRef::from_u32(0))
                        }
                    },
                    crate::objects::Directive::Embed(embed) => ir::object::Directive::Embed(embed),
                };
                directives.push(lowered);
            }

            sections.push(ir::object::Section {
                name: section.name,
                directives,
            });
        }

        if has_error {
            return None;
        }

        Some(ir::object::Object {
            name: object.name,
            sections,
        })
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

    fn inst_arity_error(input: &str) -> (ir::InstArity, usize) {
        let errors = match parse_module(input) {
            Ok(_) => panic!("expected parser error"),
            Err(errors) => errors,
        };
        errors
            .into_iter()
            .find_map(|err| match err {
                Error::InstArgNumMismatch {
                    expected, actual, ..
                } => Some((expected, actual)),
                _ => None,
            })
            .expect("expected arity mismatch error")
    }

    fn has_unexpected_trailing_inst_arg(input: &str) -> bool {
        let errors = match parse_module(input) {
            Ok(_) => panic!("expected parser error"),
            Err(errors) => errors,
        };
        errors
            .into_iter()
            .any(|err| matches!(err, Error::UnexpectedTrailingInstArg(..)))
    }

    #[test]
    fn test_duplicate_name_identical_signature_should_fail() {
        let s = r#"
target = "evm-ethereum-london"

func public %foo() -> unit {
    block0:
        return;
}

func public %foo() -> unit {
    block 0:
        return;
}
"#;

        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_duplicate_name_diff_params_should_fail() {
        let s = r#"
target = "evm-ethereum-london"

func public %foo() -> unit {
    block0:
        return;
}

func public %foo(v0.i8) -> unit {
    block 0:
        return;
}
"#;

        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_duplicate_name_diff_args_constant_return_panic_order1() {
        let s = r#"
target = "evm-ethereum-london"

func public %foo() -> unit {
    block0:
        return;
}

func public %foo(v0.i8) -> i8 {
    block0:
        return 0.i8;
}
"#;

        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_duplicate_name_diff_args_constant_return_order2() {
        // Reversing the function declarations from the test above does not panic
        let s = r#"
target = "evm-ethereum-london"

func public %foo(v0.i8) -> i8 {
    block0:
        return 0.i8;
}

func public %foo() -> unit {
    block0:
        return;
}
"#;
        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_duplicate_tuple_result_names_should_fail_without_panicking() {
        let s = r#"
target = "evm-ethereum-london"

func public %foo(v0.i8, v1.i8) -> i8 {
    block0:
        (v2.i8, v2.i1) = uaddo v0, v1;
        return v0;
}
"#;

        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_duplicate_name_different_constant_returns_should_fail() {
        let s = r#"
target = "evm-ethereum-london"

func public %no_args() -> unit {
    block0:
        return 0.i8;
}

func public %no_args() -> i8 {
    block0:
        return 1.i8;
}
"#;

        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_duplicate_name_no_args_constant_return_should_fail() {
        let s = r#"
target = "evm-ethereum-london"

func public %no_args() -> unit {
    block0:
        return;
}

func public %no_args() -> i8 {
    block0:
        return 42.i8;
}
"#;

        assert!(parse_module(s).is_err());
    }

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

    #[test]
    fn test_sym_addr_sym_size_parse_and_write() {
        let s = r#"
target = "evm-ethereum-london"

global public i8 $foo = 0;

func public %main() {
    block0:
        v0.i256 = sym_addr %main;
        v1.i256 = sym_size %main;
        v2.i256 = sym_addr $foo;
        v3.i256 = sym_size $foo;
        v4.i256 = sym_addr &runtime;
        v5.i256 = sym_size &runtime;
        v6.i256 = sym_addr .;
        v7.i256 = sym_size .;
        return;
}
"#;

        let parsed = parse_module(s).unwrap();
        let mut w = ir::ir_writer::ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let printed = w.dump_string();
        assert!(printed.contains("sym_addr %main"));
        assert!(printed.contains("sym_size %main"));
        assert!(printed.contains("sym_addr $foo"));
        assert!(printed.contains("sym_size $foo"));
        assert!(printed.contains("sym_addr &runtime"));
        assert!(printed.contains("sym_size &runtime"));
        assert!(printed.contains("sym_addr ."));
        assert!(printed.contains("sym_size ."));
    }

    #[test]
    fn test_br_table_requires_at_least_one_destination() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        br_table 0.i32;
}
"#;

        assert!(parse_module(s).is_err());
    }

    #[test]
    fn test_call_requires_callee_argument() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        call;
        return;
}
"#;

        let (expected, actual) = inst_arity_error(s);
        assert_eq!(expected, ir::InstArity::AtLeast(1));
        assert_eq!(actual, 0);
    }

    #[test]
    fn test_return_rejects_multiple_arguments() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        return 0.i8 1.i8;
}
"#;

        assert!(has_unexpected_trailing_inst_arg(s));
    }

    #[test]
    fn test_multi_return_signatures_and_return_tuples_roundtrip() {
        let s = r#"
target = "evm-ethereum-london"

declare private %takes_cb(*(i32, i32) -> (i32, i1));

func private %pair_add(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        (v2.i32, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

func public %caller(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        (v2.i32, v3.i1) = call %pair_add v0 v1;
        return (v2, v3);
}
"#;

        let parsed = parse_module(s).unwrap();
        let pair_add = parsed
            .module
            .ctx
            .declared_funcs
            .iter()
            .find_map(|entry| (entry.value().name() == "pair_add").then(|| *entry.key()))
            .expect("pair_add should be declared");
        assert_eq!(
            parsed
                .module
                .ctx
                .func_sig(pair_add, |sig| sig.ret_tys().to_vec()),
            vec![ir::Type::I32, ir::Type::I1]
        );

        let mut w = ir::ir_writer::ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let printed = w.dump_string();
        assert!(printed.contains("declare private %takes_cb(*(i32, i32) -> (i32, i1));"));
        assert!(printed.contains("func private %pair_add(v0.i32, v1.i32) -> (i32, i1) {"));
        assert!(printed.contains("(v2.i32, v3.i1) = call %pair_add v0 v1;"));
        assert!(printed.contains("return (v2, v3);"));
    }

    #[test]
    fn test_parse_overflow_ops() {
        let s = r#"
target = "evm-ethereum-london"

func public %ops(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i1) = saddo v0 v1;
        (v4.i32, v5.i1) = usubo v0 v1;
        (v6.i32, v7.i1) = ssubo v0 v1;
        (v8.i32, v9.i1) = umulo v0 v1;
        (v10.i32, v11.i1) = smulo v0 v1;
        (v12.i32, v13.i1) = snego v0;
        (v14.i32, v15.i1) = evm_udivo v0 v1;
        (v16.i32, v17.i1) = evm_sdivo v0 v1;
        (v18.i32, v19.i1) = evm_umodo v0 v1;
        (v20.i32, v21.i1) = evm_smodo v0 v1;
        return;
}
"#;

        assert!(parse_module(s).is_ok());
    }

    #[test]
    fn test_parse_module_includes_objects() {
        let s = r#"
target = "evm-ethereum-london"

func public %factory() {
    block0:
        return;
}

object @Factory {
  section runtime { entry %factory; }
}
"#;

        let parsed = parse_module(s).unwrap();
        assert_eq!(parsed.module.objects.len(), 1);
        assert!(parsed.module.objects.contains_key("Factory"));
        let mut w = ir::ir_writer::ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
        let printed = w.dump_string();
        assert!(printed.contains("object @Factory"));
    }

    #[test]
    fn test_parse_module_duplicate_objects_should_fail() {
        let s = r#"
target = "evm-ethereum-london"

func public %factory() {
    block0:
        return;
}

object @Factory {
  section runtime { entry %factory; }
}

object @Factory {
  section runtime { entry %factory; }
}
"#;

        let errors = match parse_module(s) {
            Ok(_) => panic!("Expected duplicate object definition error"),
            Err(errors) => errors,
        };
        assert!(errors.iter().any(|e| matches!(
            e,
            Error::DuplicatedDeclaration(name, _) if name.as_str() == "Factory"
        )));
    }
}
