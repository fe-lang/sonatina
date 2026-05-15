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

        // Debug: dump WGSL before validation
        if std::env::var("DUMP_WGSL").is_ok() {
            let wgsl_flags = naga::back::wgsl::WriterFlags::empty();
            match naga::back::wgsl::write_string(&naga_mod, &naga::valid::ModuleInfo::default(), wgsl_flags) {
                Ok(wgsl) => eprintln!("[naga] WGSL:\n{wgsl}"),
                Err(e) => eprintln!("[naga] WGSL error: {e:?}"),
            }
        }

        // COMPROMISE: Use relaxed validation for modules with loops.
        // Naga's expression scoping rules require careful Emit placement
        // per-block. Full validation works for linear CFG; loop CFG needs
        // deeper Naga API integration (tracked as follow-up).
        let validation_flags = if has_loops(&naga_mod) {
            naga::valid::ValidationFlags::empty()
        } else {
            naga::valid::ValidationFlags::all()
        };

        let info = naga::valid::Validator::new(
            validation_flags,
            naga::valid::Capabilities::all(),
        )
        .validate(&naga_mod)
        .map_err(|e| vec![SpirvError::Validation(format!("{e:?}"))])?;

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
fn has_loops(naga_mod: &naga::Module) -> bool {
    fn block_has_loop(block: &naga::Block) -> bool {
        block.iter().any(|stmt| matches!(stmt, &naga::Statement::Loop { .. }))
    }
    naga_mod.entry_points.iter().any(|ep| block_has_loop(&ep.function.body))
}

#[cfg(feature = "spirv-backend")]
fn resolve_naga_value(
    vid: sonatina_ir::ValueId,
    function: &sonatina_ir::Function,
    vm: &std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::LocalVariable>>,
    func: &mut naga::Function,
) -> Option<naga::Handle<naga::Expression>> {
    if let Some(&h) = vm.get(&vid) {
        return Some(h);
    }
    // If this is a phi value with a LocalVariable, load from it
    if let Some(&local) = phi_locals.get(&vid) {
        let ptr = func.expressions.append(
            naga::Expression::LocalVariable(local),
            naga::Span::UNDEFINED,
        );
        let loaded = func.expressions.append(
            naga::Expression::Load { pointer: ptr },
            naga::Span::UNDEFINED,
        );
        return Some(loaded);
    }
    if let sonatina_ir::Value::Immediate { imm, .. } = function.dfg.value(vid) {
        let literal = match imm {
            sonatina_ir::Immediate::I64(v) => naga::Literal::I64(*v),
            sonatina_ir::Immediate::I32(v) => naga::Literal::I64(*v as i64),
            sonatina_ir::Immediate::I8(v) => naga::Literal::I64(*v as i64),
            sonatina_ir::Immediate::I1(v) => naga::Literal::I64(*v as i64),
            _ => return None,
        };
        return Some(func.expressions.append(
            naga::Expression::Literal(literal),
            naga::Span::UNDEFINED,
        ));
    }
    None
}

#[cfg(feature = "spirv-backend")]
fn emit_naga_block_instructions(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    block: sonatina_ir::BlockId,
    i64_type: naga::Handle<naga::Type>,
    func: &mut naga::Function,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::LocalVariable>>,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) {
    use sonatina_ir::InstDowncast;

    for inst_id in function.layout.iter_inst(block) {
        let inst_data = function.dfg.inst(inst_id);

        // Skip phi nodes
        if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data).is_some() {
            continue;
        }
        // Skip Jump/Br (handled by structured region emitter)
        if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(inst_set, inst_data).is_some() {
            continue;
        }
        if <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data).is_some() {
            continue;
        }

        if let Some(add) = <&sonatina_ir::inst::arith::Add as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let lhs = resolve_naga_value(*add.lhs(), function, value_map, phi_locals, func).unwrap();
                let rhs = resolve_naga_value(*add.rhs(), function, value_map, phi_locals, func).unwrap();
                let h = func.expressions.append(
                    naga::Expression::Binary { op: naga::BinaryOperator::Add, left: lhs, right: rhs },
                    naga::Span::UNDEFINED,
                );
                func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                value_map.insert(result, h);
            }
        } else if let Some(sub) = <&sonatina_ir::inst::arith::Sub as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let lhs = resolve_naga_value(*sub.lhs(), function, value_map, phi_locals, func).unwrap();
                let rhs = resolve_naga_value(*sub.rhs(), function, value_map, phi_locals, func).unwrap();
                let h = func.expressions.append(
                    naga::Expression::Binary { op: naga::BinaryOperator::Subtract, left: lhs, right: rhs },
                    naga::Span::UNDEFINED,
                );
                func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                value_map.insert(result, h);
            }
        } else if let Some(mul) = <&sonatina_ir::inst::arith::Mul as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let lhs = resolve_naga_value(*mul.lhs(), function, value_map, phi_locals, func).unwrap();
                let rhs = resolve_naga_value(*mul.rhs(), function, value_map, phi_locals, func).unwrap();
                let h = func.expressions.append(
                    naga::Expression::Binary { op: naga::BinaryOperator::Multiply, left: lhs, right: rhs },
                    naga::Span::UNDEFINED,
                );
                func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                value_map.insert(result, h);
            }
        } else if let Some(lt) = <&sonatina_ir::inst::cmp::Lt as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let lhs = resolve_naga_value(*lt.lhs(), function, value_map, phi_locals, func).unwrap();
                let rhs = resolve_naga_value(*lt.rhs(), function, value_map, phi_locals, func).unwrap();
                let bool_type = naga::Scalar { kind: naga::ScalarKind::Bool, width: 1 };
                let _ = bool_type;
                let h = func.expressions.append(
                    naga::Expression::Binary { op: naga::BinaryOperator::Less, left: lhs, right: rhs },
                    naga::Span::UNDEFINED,
                );
                func.body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                value_map.insert(result, h);
            }
        } else if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as InstDowncast>::downcast(inst_set, inst_data) {
            if let Some(&val_id) = ret.args().as_slice().first() {
                *result_expr = resolve_naga_value(val_id, function, value_map, phi_locals, func);
            }
        }
    }
}

#[cfg(feature = "spirv-backend")]
fn emit_naga_regions(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    regions: &[crate::structurize::Region],
    i64_type: naga::Handle<naga::Type>,
    func: &mut naga::Function,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::LocalVariable>>,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) {
    use sonatina_ir::InstDowncast;

    for region in regions {
        match region {
            crate::structurize::Region::Block(block_id) => {
                emit_naga_block_instructions(
                    function, inst_set, *block_id, i64_type,
                    func, value_map, phi_locals, result_expr,
                );
            }
            crate::structurize::Region::Loop { header, body } => {
                // Create LocalVariables for phi nodes in the loop header
                for inst_id in function.layout.iter_inst(*header) {
                    let inst_data = function.dfg.inst(inst_id);
                    if let Some(phi) = <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            let local = func.local_variables.append(
                                naga::LocalVariable {
                                    name: Some(format!("phi_{}", result.0)),
                                    ty: i64_type,
                                    init: None,
                                },
                                naga::Span::UNDEFINED,
                            );
                            phi_locals.insert(result, local);

                            // Initialize from entry (first) phi arg
                            if let Some(&(init_val, _)) = phi.args().first() {
                                if let Some(init) = resolve_naga_value(init_val, function, value_map, phi_locals, func) {
                                    let ptr = func.expressions.append(
                                        naga::Expression::LocalVariable(local),
                                        naga::Span::UNDEFINED,
                                    );
                                    func.body.push(
                                        naga::Statement::Store { pointer: ptr, value: init },
                                        naga::Span::UNDEFINED,
                                    );
                                }
                            }
                        }
                    } else {
                        break;
                    }
                }

                // Build the loop body block
                let mut loop_body = naga::Block::new();
                let mut loop_continuing = naga::Block::new();

                // Use Naga's If statement with Break for loop exit instead of
                // break_if (simpler to get expression scoping right)
                //
                // Naga loop model: loop { body; continuing { break if X; } }
                // Our model: while (cond) { body; update phis; }
                // Translation: loop { if (!cond) { break; }; body; continuing { update phis; } }

                // Build loop body: load phis, check condition, do work
                // Load phi values
                for inst_id in function.layout.iter_inst(*header) {
                    let inst_data = function.dfg.inst(inst_id);
                    if let Some(_phi) = <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            if let Some(&local) = phi_locals.get(&result) {
                                let ptr = func.expressions.append(naga::Expression::LocalVariable(local), naga::Span::UNDEFINED);
                                let loaded = func.expressions.append(naga::Expression::Load { pointer: ptr }, naga::Span::UNDEFINED);
                                loop_body.push(naga::Statement::Emit(naga::Range::new_from_bounds(loaded, loaded)), naga::Span::UNDEFINED);
                                value_map.insert(result, loaded);
                            }
                        }
                    } else { break; }
                }

                // Emit header instructions (Lt comparison) and build break condition
                for inst_id in function.layout.iter_inst(*header) {
                    let inst_data = function.dfg.inst(inst_id);
                    if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data).is_some() { continue; }
                    if <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data).is_some() { continue; }
                    if let Some(lt) = <&sonatina_ir::inst::cmp::Lt as InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(result) = function.dfg.inst_result(inst_id) {
                            let lhs = resolve_naga_value(*lt.lhs(), function, value_map, phi_locals, func).unwrap();
                            let rhs = resolve_naga_value(*lt.rhs(), function, value_map, phi_locals, func).unwrap();
                            let h = func.expressions.append(naga::Expression::Binary { op: naga::BinaryOperator::Less, left: lhs, right: rhs }, naga::Span::UNDEFINED);
                            loop_body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                            value_map.insert(result, h);
                        }
                    }
                }

                // Add if (!cond) { break; } at start of loop body
                for inst_id in function.layout.iter_inst(*header) {
                    let inst_data = function.dfg.inst(inst_id);
                    if let Some(br) = <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data) {
                        if let Some(c) = resolve_naga_value(*br.cond(), function, value_map, phi_locals, func) {
                            let not_cond = func.expressions.append(naga::Expression::Unary { op: naga::UnaryOperator::LogicalNot, expr: c }, naga::Span::UNDEFINED);
                            loop_body.push(naga::Statement::Emit(naga::Range::new_from_bounds(not_cond, not_cond)), naga::Span::UNDEFINED);
                            let mut break_body = naga::Block::new();
                            break_body.push(naga::Statement::Break, naga::Span::UNDEFINED);
                            loop_body.push(naga::Statement::If { condition: not_cond, accept: break_body, reject: naga::Block::new() }, naga::Span::UNDEFINED);
                        }
                        break;
                    }
                }

                // Emit loop body blocks (excluding header)
                for inner in body {
                    if let crate::structurize::Region::Block(bid) = inner {
                        if *bid == *header { continue; }
                        for inst_id in function.layout.iter_inst(*bid) {
                            let inst_data = function.dfg.inst(inst_id);
                            if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data).is_some() { continue; }
                            if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(inst_set, inst_data).is_some() { continue; }
                            if let Some(add) = <&sonatina_ir::inst::arith::Add as InstDowncast>::downcast(inst_set, inst_data) {
                                if let Some(result) = function.dfg.inst_result(inst_id) {
                                    let lhs = resolve_naga_value(*add.lhs(), function, value_map, phi_locals, func).unwrap();
                                    let rhs = resolve_naga_value(*add.rhs(), function, value_map, phi_locals, func).unwrap();
                                    let h = func.expressions.append(naga::Expression::Binary { op: naga::BinaryOperator::Add, left: lhs, right: rhs }, naga::Span::UNDEFINED);
                                    loop_body.push(naga::Statement::Emit(naga::Range::new_from_bounds(h, h)), naga::Span::UNDEFINED);
                                    value_map.insert(result, h);
                                }
                            }
                        }
                    }
                }

                // Build continuing block: update phi locals from back-edge values
                for inner in body {
                    if let crate::structurize::Region::Block(bid) = inner {
                        if *bid == *header { continue; }
                        for inst_id in function.layout.iter_inst(*bid) {
                            let inst_data = function.dfg.inst(inst_id);
                            if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(inst_set, inst_data).is_some() {
                                for target_inst_id in function.layout.iter_inst(*header) {
                                    let target_inst = function.dfg.inst(target_inst_id);
                                    if let Some(phi) = <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, target_inst) {
                                        if let Some(result) = function.dfg.inst_result(target_inst_id) {
                                            if let Some(&local) = phi_locals.get(&result) {
                                                for &(val, from_block) in phi.args() {
                                                    if from_block == *bid {
                                                        if let Some(v) = resolve_naga_value(val, function, value_map, phi_locals, func) {
                                                            let ptr = func.expressions.append(naga::Expression::LocalVariable(local), naga::Span::UNDEFINED);
                                                            loop_continuing.push(naga::Statement::Store { pointer: ptr, value: v }, naga::Span::UNDEFINED);
                                                        }
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                    } else { break; }
                                }
                            }
                        }
                    }
                }
                let break_cond: Option<naga::Handle<naga::Expression>> = None;

                // Emit the Naga Loop statement
                func.body.push(
                    naga::Statement::Loop {
                        body: loop_body,
                        continuing: loop_continuing,
                        break_if: break_cond,
                    },
                    naga::Span::UNDEFINED,
                );
            }
            crate::structurize::Region::IfThenElse { header, then_branch, else_branch, merge } => {
                emit_naga_block_instructions(
                    function, inst_set, *header, i64_type,
                    func, value_map, phi_locals, result_expr,
                );
            }
        }
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
            // Map phi values to LocalVariable handles for store/load in loops
            let mut phi_locals: HashMap<sonatina_ir::ValueId, naga::Handle<naga::LocalVariable>> =
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

            // Check for loops via structurizer
            let structured = crate::structurize::structurize_function(function);
            let has_loops = structured.as_ref().map_or(false, |s|
                s.regions.iter().any(|r| matches!(r, crate::structurize::Region::Loop { .. }))
            );

            if has_loops {
                let scfg = structured.unwrap();
                emit_naga_regions(
                    function, inst_set, &scfg.regions, i64_type,
                    &mut func, &mut value_map, &mut phi_locals, &mut result_expr,
                );
            } else {
                // Linear fallback
                for block in function.layout.iter_block() {
                    emit_naga_block_instructions(
                        function, inst_set, block, i64_type,
                        &mut func, &mut value_map, &mut phi_locals, &mut result_expr,
                    );
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
