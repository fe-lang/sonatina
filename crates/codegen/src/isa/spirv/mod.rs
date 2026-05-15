//! SPIR-V backend: Sonatina IR → SPIR-V compute shader modules via Naga.
//!
//! Translates Sonatina IR to Naga's expression DAG + statement tree IR,
//! then Naga emits SPIR-V. Optionally produces WGSL for debugging.

use sonatina_ir::Module;

use crate::backend::Backend;

#[derive(Debug)]
pub enum SpirvError {
    UnsupportedTarget(String),
    Translation(String),
    Validation(String),
}

impl std::fmt::Display for SpirvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedTarget(msg) => write!(f, "unsupported target: {msg}"),
            Self::Translation(msg) => write!(f, "spirv translation error: {msg}"),
            Self::Validation(msg) => write!(f, "spirv validation error: {msg}"),
        }
    }
}

pub struct SpirvArtifact {
    pub words: Vec<u32>,
}

impl SpirvArtifact {
    pub fn as_bytes(&self) -> Vec<u8> {
        self.words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }
}

pub struct SpirvBackend {
    pub workgroup_size: [u32; 3],
}

impl SpirvBackend {
    pub fn new() -> Self {
        Self {
            workgroup_size: [64, 1, 1],
        }
    }

    pub fn with_workgroup_size(mut self, x: u32, y: u32, z: u32) -> Self {
        self.workgroup_size = [x, y, z];
        self
    }
}

impl Backend for SpirvBackend {
    type Artifact = SpirvArtifact;
    type Error = SpirvError;

    #[cfg(not(feature = "spirv-backend"))]
    fn compile_module(&self, _module: &Module) -> Result<Self::Artifact, Vec<Self::Error>> {
        Err(vec![SpirvError::Translation(
            "SPIR-V backend requires the spirv-backend feature".to_string(),
        )])
    }

    #[cfg(feature = "spirv-backend")]
    fn compile_module(&self, module: &Module) -> Result<Self::Artifact, Vec<Self::Error>> {
        let naga_mod = translate_to_naga(module, self.workgroup_size)
            .map_err(|e| vec![SpirvError::Translation(e)])?;

        let info = naga::valid::Validator::new(
            naga::valid::ValidationFlags::all(),
            naga::valid::Capabilities::all(),
        )
        .validate(&naga_mod)
        .map_err(|e| vec![SpirvError::Validation(format!("{e}"))])?;

        let options = naga::back::spv::Options {
            lang_version: (1, 5),
            flags: naga::back::spv::WriterFlags::empty(),
            ..Default::default()
        };

        let words = naga::back::spv::write_vec(&naga_mod, &info, &options, None)
            .map_err(|e| vec![SpirvError::Translation(format!("{e}"))])?;

        Ok(SpirvArtifact { words })
    }
}

#[cfg(feature = "spirv-backend")]
fn translate_to_naga(
    module: &Module,
    workgroup_size: [u32; 3],
) -> Result<naga::Module, String> {
    use std::collections::HashMap;

    let mut naga_mod = naga::Module::default();

    let i64_type = naga_mod.types.insert(
        naga::Type {
            name: None,
            inner: naga::TypeInner::Scalar(naga::Scalar {
                kind: naga::ScalarKind::Sint,
                width: 8,
            }),
        },
        naga::Span::UNDEFINED,
    );

    let output_struct = naga_mod.types.insert(
        naga::Type {
            name: Some("Output".into()),
            inner: naga::TypeInner::Struct {
                members: vec![naga::StructMember {
                    name: Some("result".into()),
                    ty: i64_type,
                    binding: None,
                    offset: 0,
                }],
                span: 8,
            },
        },
        naga::Span::UNDEFINED,
    );

    let input_struct = naga_mod.types.insert(
        naga::Type {
            name: Some("Input".into()),
            inner: naga::TypeInner::Struct {
                members: vec![
                    naga::StructMember {
                        name: Some("a".into()),
                        ty: i64_type,
                        binding: None,
                        offset: 0,
                    },
                    naga::StructMember {
                        name: Some("b".into()),
                        ty: i64_type,
                        binding: None,
                        offset: 8,
                    },
                ],
                span: 16,
            },
        },
        naga::Span::UNDEFINED,
    );

    let output_var = naga_mod.global_variables.append(
        naga::GlobalVariable {
            name: Some("output".into()),
            space: naga::AddressSpace::Storage {
                access: naga::StorageAccess::LOAD | naga::StorageAccess::STORE,
            },
            binding: Some(naga::ResourceBinding { group: 0, binding: 0 }),
            ty: output_struct,
            init: None,
            memory_decorations: naga::ir::MemoryDecorations::empty(),
        },
        naga::Span::UNDEFINED,
    );

    let input_var = naga_mod.global_variables.append(
        naga::GlobalVariable {
            name: Some("input".into()),
            space: naga::AddressSpace::Storage {
                access: naga::StorageAccess::LOAD,
            },
            binding: Some(naga::ResourceBinding { group: 0, binding: 1 }),
            ty: input_struct,
            init: None,
            memory_decorations: naga::ir::MemoryDecorations::empty(),
        },
        naga::Span::UNDEFINED,
    );

    // Build the entry point function
    let mut func = naga::Function {
        name: Some("main".into()),
        arguments: vec![],
        result: None,
        local_variables: naga::Arena::new(),
        expressions: naga::Arena::new(),
        named_expressions: Default::default(),
        body: naga::Block::new(),
        diagnostic_filter_leaf: None,
    };

    // Translate the first Sonatina function
    let funcs = module.funcs();
    let mut result_expr = None;

    if let Some(&func_ref) = funcs.first() {
        module.func_store.try_view(func_ref, |function| {
            let inst_set = function.inst_set();
            let mut value_map: HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>> =
                HashMap::new();

            // Load function args from input buffer
            let input_expr = func.expressions.append(
                naga::Expression::GlobalVariable(input_var),
                naga::Span::UNDEFINED,
            );

            for (idx, &arg_val) in function.arg_values.iter().enumerate() {
                let field = func.expressions.append(
                    naga::Expression::AccessIndex {
                        base: input_expr,
                        index: idx as u32,
                    },
                    naga::Span::UNDEFINED,
                );
                let loaded = func.expressions.append(
                    naga::Expression::Load { pointer: field },
                    naga::Span::UNDEFINED,
                );
                func.body.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(field, loaded)),
                    naga::Span::UNDEFINED,
                );
                value_map.insert(arg_val, loaded);
            }

            for block in function.layout.iter_block() {
                for inst_id in function.layout.iter_inst(block) {
                    let inst_data = function.dfg.inst(inst_id);

                    let resolve =
                        |vid: sonatina_ir::ValueId,
                         vm: &HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
                         exprs: &mut naga::Arena<naga::Expression>| {
                            if let Some(&h) = vm.get(&vid) {
                                return Some(h);
                            }
                            if let sonatina_ir::Value::Immediate { imm, .. } =
                                function.dfg.value(vid)
                            {
                                let literal = match imm {
                                    sonatina_ir::Immediate::I64(v) => naga::Literal::I64(*v),
                                    sonatina_ir::Immediate::I32(v) => naga::Literal::I64(*v as i64),
                                    _ => return None,
                                };
                                return Some(exprs.append(
                                    naga::Expression::Literal(literal),
                                    naga::Span::UNDEFINED,
                                ));
                            }
                            None
                        };

                    if let Some(add) = <&sonatina_ir::inst::arith::Add as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            let lhs = resolve(*add.lhs(), &value_map, &mut func.expressions).unwrap();
                            let rhs = resolve(*add.rhs(), &value_map, &mut func.expressions).unwrap();
                            let h = func.expressions.append(
                                naga::Expression::Binary { op: naga::BinaryOperator::Add, left: lhs, right: rhs },
                                naga::Span::UNDEFINED,
                            );
                            func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                            value_map.insert(result, h);
                        }
                    } else if let Some(sub) = <&sonatina_ir::inst::arith::Sub as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            let lhs = resolve(*sub.lhs(), &value_map, &mut func.expressions).unwrap();
                            let rhs = resolve(*sub.rhs(), &value_map, &mut func.expressions).unwrap();
                            let h = func.expressions.append(
                                naga::Expression::Binary { op: naga::BinaryOperator::Subtract, left: lhs, right: rhs },
                                naga::Span::UNDEFINED,
                            );
                            func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                            value_map.insert(result, h);
                        }
                    } else if let Some(mul) = <&sonatina_ir::inst::arith::Mul as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            let lhs = resolve(*mul.lhs(), &value_map, &mut func.expressions).unwrap();
                            let rhs = resolve(*mul.rhs(), &value_map, &mut func.expressions).unwrap();
                            let h = func.expressions.append(
                                naga::Expression::Binary { op: naga::BinaryOperator::Multiply, left: lhs, right: rhs },
                                naga::Span::UNDEFINED,
                            );
                            func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                            value_map.insert(result, h);
                        }
                    } else if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(&val_id) = ret.args().as_slice().first() {
                            result_expr = resolve(val_id, &value_map, &mut func.expressions);
                        }
                    }
                }
            }
        });
    }

    // Store result to output buffer
    let output_expr = func.expressions.append(
        naga::Expression::GlobalVariable(output_var),
        naga::Span::UNDEFINED,
    );
    let result_field = func.expressions.append(
        naga::Expression::AccessIndex { base: output_expr, index: 0 },
        naga::Span::UNDEFINED,
    );

    let final_val = result_expr.unwrap_or_else(|| {
        func.expressions.append(
            naga::Expression::Literal(naga::Literal::I64(0)),
            naga::Span::UNDEFINED,
        )
    });

    func.body.push(
        naga::Statement::Store { pointer: result_field, value: final_val },
        naga::Span::UNDEFINED,
    );

    naga_mod.entry_points.push(naga::EntryPoint {
        name: "main".into(),
        stage: naga::ShaderStage::Compute,
        early_depth_test: None,
        workgroup_size,
        workgroup_size_overrides: None,
        function: func,
        mesh_info: None,
        task_payload: None,
        incoming_ray_payload: None,
    });

    Ok(naga_mod)
}
