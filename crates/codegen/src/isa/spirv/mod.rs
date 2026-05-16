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
    /// WGSL source for wgpu execution (available when spirv-backend feature is on)
    pub wgsl: Option<String>,
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
        .map_err(|e| vec![SpirvError::Validation(format!("{e:?}"))])?;

        let options = naga::back::spv::Options {
            lang_version: (1, 5),
            flags: naga::back::spv::WriterFlags::empty(),
            ..Default::default()
        };

        let words = naga::back::spv::write_vec(&naga_mod, &info, &options, None)
            .map_err(|e| vec![SpirvError::Translation(format!("{e}"))])?;

        // Also emit WGSL for wgpu execution
        let wgsl = naga::back::wgsl::write_string(
            &naga_mod,
            &info,
            naga::back::wgsl::WriterFlags::empty(),
        )
        .ok();

        Ok(SpirvArtifact { words, wgsl })
    }
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
        return Some(
            func.expressions
                .append(naga::Expression::Literal(literal), naga::Span::UNDEFINED),
        );
    }
    None
}

/// Emit a single arithmetic/cmp instruction into the given target block.
/// Returns the expression handle if an instruction was emitted, None otherwise.
/// Skips Phi, Jump, Br, and Return instructions.
#[cfg(feature = "spirv-backend")]
fn emit_single_inst(
    inst_id: sonatina_ir::InstId,
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    func: &mut naga::Function,
    target: &mut naga::Block,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<
        sonatina_ir::ValueId,
        naga::Handle<naga::LocalVariable>,
    >,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) -> bool {
    use sonatina_ir::InstDowncast;
    let inst_data = function.dfg.inst(inst_id);

    // Skip phi/jump/br
    if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data)
        .is_some()
    {
        return false;
    }
    if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(inst_set, inst_data)
        .is_some()
    {
        return false;
    }
    if <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data)
        .is_some()
    {
        return false;
    }

    if let Some(add) =
        <&sonatina_ir::inst::arith::Add as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let lhs =
                resolve_naga_value(*add.lhs(), function, value_map, phi_locals, func).unwrap();
            let rhs =
                resolve_naga_value(*add.rhs(), function, value_map, phi_locals, func).unwrap();
            let h = func.expressions.append(
                naga::Expression::Binary {
                    op: naga::BinaryOperator::Add,
                    left: lhs,
                    right: rhs,
                },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if let Some(sub) =
        <&sonatina_ir::inst::arith::Sub as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let lhs =
                resolve_naga_value(*sub.lhs(), function, value_map, phi_locals, func).unwrap();
            let rhs =
                resolve_naga_value(*sub.rhs(), function, value_map, phi_locals, func).unwrap();
            let h = func.expressions.append(
                naga::Expression::Binary {
                    op: naga::BinaryOperator::Subtract,
                    left: lhs,
                    right: rhs,
                },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if let Some(mul) =
        <&sonatina_ir::inst::arith::Mul as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let lhs =
                resolve_naga_value(*mul.lhs(), function, value_map, phi_locals, func).unwrap();
            let rhs =
                resolve_naga_value(*mul.rhs(), function, value_map, phi_locals, func).unwrap();
            let h = func.expressions.append(
                naga::Expression::Binary {
                    op: naga::BinaryOperator::Multiply,
                    left: lhs,
                    right: rhs,
                },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if let Some(sar) =
        <&sonatina_ir::inst::arith::Sar as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let val =
                resolve_naga_value(*sar.value(), function, value_map, phi_locals, func).unwrap();
            let shift_amount = if let Some(imm) = function.dfg.value_imm(*sar.bits()) {
                match imm {
                    sonatina_ir::Immediate::I64(v) => v as u32,
                    sonatina_ir::Immediate::I32(v) => v as u32,
                    sonatina_ir::Immediate::I8(v) => v as u32,
                    _ => 0,
                }
            } else {
                0
            };
            let bits_u32 = func.expressions.append(
                naga::Expression::Literal(naga::Literal::U32(shift_amount)),
                naga::Span::UNDEFINED,
            );
            let h = func.expressions.append(
                naga::Expression::Binary {
                    op: naga::BinaryOperator::ShiftRight,
                    left: val,
                    right: bits_u32,
                },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if let Some(lt) =
        <&sonatina_ir::inst::cmp::Lt as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let lhs = resolve_naga_value(*lt.lhs(), function, value_map, phi_locals, func).unwrap();
            let rhs = resolve_naga_value(*lt.rhs(), function, value_map, phi_locals, func).unwrap();
            let h = func.expressions.append(
                naga::Expression::Binary {
                    op: naga::BinaryOperator::Less,
                    left: lhs,
                    right: rhs,
                },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if <&sonatina_ir::inst::data::ObjAlloc as InstDowncast>::downcast(inst_set, inst_data)
        .is_some()
    {
        // ObjAlloc in SPIR-V: the output storage buffer IS the allocation.
        // Map the result to the output buffer global variable expression.
        if let Some(result) = function.dfg.inst_result(inst_id) {
            if let Some(&buf_expr) = value_map.get(&sonatina_ir::ValueId(u32::MAX)) {
                value_map.insert(result, buf_expr);
                return true;
            }
        }
    } else if let Some(obj_store) =
        <&sonatina_ir::inst::data::ObjStore as InstDowncast>::downcast(inst_set, inst_data)
    {
        // ObjStore: store value at the pointer (which is an Access expression into the buffer)
        let dest =
            resolve_naga_value(*obj_store.object(), function, value_map, phi_locals, func).unwrap();
        let val =
            resolve_naga_value(*obj_store.value(), function, value_map, phi_locals, func).unwrap();
        target.push(
            naga::Statement::Store {
                pointer: dest,
                value: val,
            },
            naga::Span::UNDEFINED,
        );
        return true;
    } else if let Some(obj_load) =
        <&sonatina_ir::inst::data::ObjLoad as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let ptr = resolve_naga_value(*obj_load.object(), function, value_map, phi_locals, func)
                .unwrap();
            let h = func.expressions.append(
                naga::Expression::Load { pointer: ptr },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if let Some(obj_index) =
        <&sonatina_ir::inst::data::ObjIndex as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(result) = function.dfg.inst_result(inst_id) {
            let base =
                resolve_naga_value(*obj_index.object(), function, value_map, phi_locals, func)
                    .unwrap();
            let index =
                resolve_naga_value(*obj_index.index(), function, value_map, phi_locals, func)
                    .unwrap();
            // Cast i64 index to i32 for array access
            let i32_idx = func.expressions.append(
                naga::Expression::As {
                    expr: index,
                    kind: naga::ScalarKind::Sint,
                    convert: Some(4),
                },
                naga::Span::UNDEFINED,
            );
            target.push(
                naga::Statement::Emit(naga::Range::new_from_bounds(i32_idx, i32_idx)),
                naga::Span::UNDEFINED,
            );
            // Access returns a pointer — no Emit needed (like LocalVariable/GlobalVariable)
            let h = func.expressions.append(
                naga::Expression::Access {
                    base,
                    index: i32_idx,
                },
                naga::Span::UNDEFINED,
            );
            value_map.insert(result, h);
            return true;
        }
    } else if let Some(ret) =
        <&sonatina_ir::inst::control_flow::Return as InstDowncast>::downcast(inst_set, inst_data)
    {
        if let Some(&val_id) = ret.args().as_slice().first() {
            let resolved = resolve_naga_value(val_id, function, value_map, phi_locals, func);
            if let Some(h) = resolved {
                if matches!(func.expressions[h], naga::Expression::Load { .. }) {
                    target.push(
                        naga::Statement::Emit(naga::Range::new_from_bounds(h, h)),
                        naga::Span::UNDEFINED,
                    );
                }
            }
            *result_expr = resolved;
            return true;
        }
    }
    false
}

/// Emit all non-control-flow instructions from a block into the target naga::Block.
#[cfg(feature = "spirv-backend")]
fn emit_block_to_target(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    block: sonatina_ir::BlockId,
    func: &mut naga::Function,
    target: &mut naga::Block,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<
        sonatina_ir::ValueId,
        naga::Handle<naga::LocalVariable>,
    >,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) {
    for inst_id in function.layout.iter_inst(block) {
        emit_single_inst(
            inst_id,
            function,
            inst_set,
            func,
            target,
            value_map,
            phi_locals,
            result_expr,
        );
    }
}

#[cfg(feature = "spirv-backend")]
fn emit_naga_block_instructions(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    block: sonatina_ir::BlockId,
    _i64_type: naga::Handle<naga::Type>,
    func: &mut naga::Function,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<
        sonatina_ir::ValueId,
        naga::Handle<naga::LocalVariable>,
    >,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) {
    let mut target = naga::Block::new();
    emit_block_to_target(
        function,
        inst_set,
        block,
        func,
        &mut target,
        value_map,
        phi_locals,
        result_expr,
    );
    func.body.extend_block(target);
}

#[cfg(feature = "spirv-backend")]
fn emit_naga_regions(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    regions: &[crate::structurize::Region],
    i64_type: naga::Handle<naga::Type>,
    func: &mut naga::Function,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<
        sonatina_ir::ValueId,
        naga::Handle<naga::LocalVariable>,
    >,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) {
    let mut region_idx = 0;
    while region_idx < regions.len() {
        let region = &regions[region_idx];
        match region {
            crate::structurize::Region::Block(block_id) => {
                emit_naga_block_instructions(
                    function,
                    inst_set,
                    *block_id,
                    i64_type,
                    func,
                    value_map,
                    phi_locals,
                    result_expr,
                );
                region_idx += 1;
            }
            crate::structurize::Region::Loop { header, body } => {
                region_idx += 1;
                emit_loop_region(
                    function,
                    inst_set,
                    *header,
                    body,
                    &regions[region_idx..],
                    &mut region_idx,
                    i64_type,
                    func,
                    value_map,
                    phi_locals,
                    result_expr,
                );
            }
            crate::structurize::Region::IfThenElse {
                header,
                then_branch: _,
                else_branch: _,
                merge: _,
            } => {
                emit_naga_block_instructions(
                    function,
                    inst_set,
                    *header,
                    i64_type,
                    func,
                    value_map,
                    phi_locals,
                    result_expr,
                );
                region_idx += 1;
            }
        }
    }
}

/// Emit a Loop region, handling inner conditional branches and post-loop exit blocks.
#[cfg(feature = "spirv-backend")]
fn emit_loop_region(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    header: sonatina_ir::BlockId,
    body: &[crate::structurize::Region],
    remaining_regions: &[crate::structurize::Region],
    region_idx: &mut usize,
    i64_type: naga::Handle<naga::Type>,
    func: &mut naga::Function,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<
        sonatina_ir::ValueId,
        naga::Handle<naga::LocalVariable>,
    >,
    result_expr: &mut Option<naga::Handle<naga::Expression>>,
) {
    use sonatina_ir::InstDowncast;

    // Create LocalVariables for phi nodes in the loop header
    for inst_id in function.layout.iter_inst(header) {
        let inst_data = function.dfg.inst(inst_id);
        if let Some(phi) =
            <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data)
        {
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
                    if let Some(init) =
                        resolve_naga_value(init_val, function, value_map, phi_locals, func)
                    {
                        let ptr = func.expressions.append(
                            naga::Expression::LocalVariable(local),
                            naga::Span::UNDEFINED,
                        );
                        func.body.push(
                            naga::Statement::Store {
                                pointer: ptr,
                                value: init,
                            },
                            naga::Span::UNDEFINED,
                        );
                    }
                }
            }
        } else {
            break;
        }
    }

    // Detect if any non-header body block has a Br (inner conditional)
    let has_inner_br = body.iter().any(|inner| {
        if let crate::structurize::Region::Block(bid) = inner {
            if *bid == header {
                return false;
            }
            for inst_id in function.layout.iter_inst(*bid) {
                let inst_data = function.dfg.inst(inst_id);
                if <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(
                    inst_set, inst_data,
                )
                .is_some()
                {
                    return true;
                }
            }
        }
        false
    });

    // If there's an inner Br, create a result_local for the function result.
    // Both exit paths (header exit, inner escape) store their return value here.
    let result_local = if has_inner_br {
        Some(func.local_variables.append(
            naga::LocalVariable {
                name: Some("loop_result".into()),
                ty: i64_type,
                init: None,
            },
            naga::Span::UNDEFINED,
        ))
    } else {
        None
    };

    // Build the loop body
    let mut loop_body = naga::Block::new();
    let loop_continuing = naga::Block::new();

    // Load phi values at top of each iteration
    for inst_id in function.layout.iter_inst(header) {
        let inst_data = function.dfg.inst(inst_id);
        if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data)
            .is_some()
        {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                if let Some(&local) = phi_locals.get(&result) {
                    let ptr = func.expressions.append(
                        naga::Expression::LocalVariable(local),
                        naga::Span::UNDEFINED,
                    );
                    let loaded = func.expressions.append(
                        naga::Expression::Load { pointer: ptr },
                        naga::Span::UNDEFINED,
                    );
                    // Only emit Load; LocalVariable is a const expression (always in scope)
                    loop_body.push(
                        naga::Statement::Emit(naga::Range::new_from_bounds(loaded, loaded)),
                        naga::Span::UNDEFINED,
                    );
                    value_map.insert(result, loaded);
                }
            }
        } else {
            break;
        }
    }

    // Header comparison (non-phi, non-Br instructions)
    for inst_id in function.layout.iter_inst(header) {
        let inst_data = function.dfg.inst(inst_id);
        if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data)
            .is_some()
        {
            continue;
        }
        if <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data)
            .is_some()
        {
            continue;
        }
        emit_single_inst(
            inst_id,
            function,
            inst_set,
            func,
            &mut loop_body,
            value_map,
            phi_locals,
            result_expr,
        );
    }

    // Header Br: find exit block and its return value, then emit if NOT(cond) { store exit result; break; }
    let mut header_exit_block = None;
    for inst_id in function.layout.iter_inst(header) {
        let inst_data = function.dfg.inst(inst_id);
        if let Some(br) =
            <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(inst_set, inst_data)
        {
            header_exit_block = Some(*br.z_dest());
            if let Some(c) = resolve_naga_value(*br.cond(), function, value_map, phi_locals, func) {
                let not_c = func.expressions.append(
                    naga::Expression::Unary {
                        op: naga::UnaryOperator::LogicalNot,
                        expr: c,
                    },
                    naga::Span::UNDEFINED,
                );
                loop_body.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(not_c, not_c)),
                    naga::Span::UNDEFINED,
                );
                let mut break_block = naga::Block::new();
                // Emit side effects (ObjStore etc.) from exit block before break
                emit_obj_ops_from_block(
                    function,
                    inst_set,
                    *br.z_dest(),
                    func,
                    &mut break_block,
                    value_map,
                    phi_locals,
                );
                if let Some(res_local) = result_local {
                    if let Some(ret_val) = find_block_return_value(*br.z_dest(), function, inst_set)
                    {
                        let expr_count_before = func.expressions.len();
                        if let Some(v) =
                            resolve_naga_value(ret_val, function, value_map, phi_locals, func)
                        {
                            if v.index() >= expr_count_before {
                                if matches!(
                                    func.expressions[v],
                                    naga::Expression::Load { .. }
                                        | naga::Expression::Binary { .. }
                                        | naga::Expression::Unary { .. }
                                ) {
                                    break_block.push(
                                        naga::Statement::Emit(naga::Range::new_from_bounds(v, v)),
                                        naga::Span::UNDEFINED,
                                    );
                                }
                            }
                            let ptr = func.expressions.append(
                                naga::Expression::LocalVariable(res_local),
                                naga::Span::UNDEFINED,
                            );
                            break_block.push(
                                naga::Statement::Store {
                                    pointer: ptr,
                                    value: v,
                                },
                                naga::Span::UNDEFINED,
                            );
                        }
                    }
                }
                break_block.push(naga::Statement::Break, naga::Span::UNDEFINED);
                loop_body.push(
                    naga::Statement::If {
                        condition: not_c,
                        accept: break_block,
                        reject: naga::Block::new(),
                    },
                    naga::Span::UNDEFINED,
                );
            }
            break;
        }
    }

    // Collect non-header body blocks
    let non_header_blocks: Vec<sonatina_ir::BlockId> = body
        .iter()
        .filter_map(|inner| {
            if let crate::structurize::Region::Block(bid) = inner {
                if *bid != header {
                    return Some(*bid);
                }
            }
            None
        })
        .collect();

    if has_inner_br {
        // Find the block with the inner Br
        let mut br_block_idx = None;
        for (idx, &bid) in non_header_blocks.iter().enumerate() {
            for inst_id in function.layout.iter_inst(bid) {
                let inst_data = function.dfg.inst(inst_id);
                if <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(
                    inst_set, inst_data,
                )
                .is_some()
                {
                    br_block_idx = Some(idx);
                    break;
                }
            }
            if br_block_idx.is_some() {
                break;
            }
        }

        if let Some(br_idx) = br_block_idx {
            let br_bid = non_header_blocks[br_idx];

            // Emit compute instructions from the Br block into loop_body
            let mut inner_cond_handle = None;
            let mut inner_escape_block = None;
            for inst_id in function.layout.iter_inst(br_bid) {
                let inst_data = function.dfg.inst(inst_id);
                if let Some(br) = <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(
                    inst_set, inst_data,
                ) {
                    inner_cond_handle =
                        resolve_naga_value(*br.cond(), function, value_map, phi_locals, func);
                    inner_escape_block = Some(*br.z_dest());
                    continue;
                }
                emit_single_inst(
                    inst_id,
                    function,
                    inst_set,
                    func,
                    &mut loop_body,
                    value_map,
                    phi_locals,
                    result_expr,
                );
            }

            if let Some(cond) = inner_cond_handle {
                // Accept branch (condition true): continue blocks + phi updates
                let mut accept_block = naga::Block::new();
                for &bid in &non_header_blocks[br_idx + 1..] {
                    emit_block_to_target(
                        function,
                        inst_set,
                        bid,
                        func,
                        &mut accept_block,
                        value_map,
                        phi_locals,
                        result_expr,
                    );

                    // Phi updates for blocks that jump back to header
                    for inst_id in function.layout.iter_inst(bid) {
                        let inst_data = function.dfg.inst(inst_id);
                        if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(
                            inst_set, inst_data,
                        )
                        .is_some()
                        {
                            for target_inst_id in function.layout.iter_inst(header) {
                                let target_inst = function.dfg.inst(target_inst_id);
                                if let Some(phi) = <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, target_inst) {
                                    if let Some(phi_result) = function.dfg.inst_result(target_inst_id) {
                                        if let Some(&local) = phi_locals.get(&phi_result) {
                                            for &(val, from_block) in phi.args() {
                                                if from_block == bid {
                                                    if let Some(v) = resolve_naga_value(val, function, value_map, phi_locals, func) {
                                                        let ptr = func.expressions.append(naga::Expression::LocalVariable(local), naga::Span::UNDEFINED);
                                                        accept_block.push(naga::Statement::Store { pointer: ptr, value: v }, naga::Span::UNDEFINED);
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

                // Reject branch (condition false, escape): emit side effects, store result, break
                let mut reject_block = naga::Block::new();
                if let Some(esc_bid) = inner_escape_block {
                    emit_obj_ops_from_block(
                        function,
                        inst_set,
                        esc_bid,
                        func,
                        &mut reject_block,
                        value_map,
                        phi_locals,
                    );
                    if let Some(res_local) = result_local {
                        if let Some(ret_val) = find_block_return_value(esc_bid, function, inst_set)
                        {
                            let expr_count_before = func.expressions.len();
                            if let Some(v) =
                                resolve_naga_value(ret_val, function, value_map, phi_locals, func)
                            {
                                if v.index() >= expr_count_before {
                                    if matches!(
                                        func.expressions[v],
                                        naga::Expression::Load { .. }
                                            | naga::Expression::Binary { .. }
                                            | naga::Expression::Unary { .. }
                                    ) {
                                        reject_block.push(
                                            naga::Statement::Emit(naga::Range::new_from_bounds(
                                                v, v,
                                            )),
                                            naga::Span::UNDEFINED,
                                        );
                                    }
                                }
                                let ptr = func.expressions.append(
                                    naga::Expression::LocalVariable(res_local),
                                    naga::Span::UNDEFINED,
                                );
                                reject_block.push(
                                    naga::Statement::Store {
                                        pointer: ptr,
                                        value: v,
                                    },
                                    naga::Span::UNDEFINED,
                                );
                            }
                        }
                    }
                }
                reject_block.push(naga::Statement::Break, naga::Span::UNDEFINED);

                loop_body.push(
                    naga::Statement::If {
                        condition: cond,
                        accept: accept_block,
                        reject: reject_block,
                    },
                    naga::Span::UNDEFINED,
                );
            }
        }
    } else {
        // Simple loop body (no inner Br)
        for &bid in &non_header_blocks {
            emit_block_to_target(
                function,
                inst_set,
                bid,
                func,
                &mut loop_body,
                value_map,
                phi_locals,
                result_expr,
            );

            // Phi updates
            for inst_id in function.layout.iter_inst(bid) {
                let inst_data = function.dfg.inst(inst_id);
                if <&sonatina_ir::inst::control_flow::Jump as InstDowncast>::downcast(
                    inst_set, inst_data,
                )
                .is_some()
                {
                    for target_inst_id in function.layout.iter_inst(header) {
                        let target_inst = function.dfg.inst(target_inst_id);
                        if let Some(phi) =
                            <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(
                                inst_set,
                                target_inst,
                            )
                        {
                            if let Some(phi_result) = function.dfg.inst_result(target_inst_id) {
                                if let Some(&local) = phi_locals.get(&phi_result) {
                                    for &(val, from_block) in phi.args() {
                                        if from_block == bid {
                                            if let Some(v) = resolve_naga_value(
                                                val, function, value_map, phi_locals, func,
                                            ) {
                                                let ptr = func.expressions.append(
                                                    naga::Expression::LocalVariable(local),
                                                    naga::Span::UNDEFINED,
                                                );
                                                loop_body.push(
                                                    naga::Statement::Store {
                                                        pointer: ptr,
                                                        value: v,
                                                    },
                                                    naga::Span::UNDEFINED,
                                                );
                                            }
                                            break;
                                        }
                                    }
                                }
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
        }
    }

    // Emit the Naga Loop statement
    func.body.push(
        naga::Statement::Loop {
            body: loop_body,
            continuing: loop_continuing,
            break_if: None,
        },
        naga::Span::UNDEFINED,
    );

    // After the loop, phi values from the loop body are out of scope.
    for inst_id in function.layout.iter_inst(header) {
        let inst_data = function.dfg.inst(inst_id);
        if <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(inst_set, inst_data)
            .is_some()
        {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                value_map.remove(&result);
            }
        } else {
            break;
        }
    }

    // If we used a result_local, load from it and set result_expr,
    // then skip the post-loop return blocks
    if let Some(res_local) = result_local {
        let ptr = func.expressions.append(
            naga::Expression::LocalVariable(res_local),
            naga::Span::UNDEFINED,
        );
        let loaded = func.expressions.append(
            naga::Expression::Load { pointer: ptr },
            naga::Span::UNDEFINED,
        );
        func.body.push(
            naga::Statement::Emit(naga::Range::new_from_bounds(loaded, loaded)),
            naga::Span::UNDEFINED,
        );
        *result_expr = Some(loaded);

        // Skip the post-loop return blocks (they are the exit targets
        // whose values we already captured into result_local)
        let mut post_blocks_to_skip = std::collections::HashSet::new();
        if let Some(exit_bid) = header_exit_block {
            post_blocks_to_skip.insert(exit_bid);
        }
        // Also find the inner escape block
        for inner in body {
            if let crate::structurize::Region::Block(bid) = inner {
                if *bid == header {
                    continue;
                }
                for inst_id in function.layout.iter_inst(*bid) {
                    let inst_data = function.dfg.inst(inst_id);
                    if let Some(br) =
                        <&sonatina_ir::inst::control_flow::Br as InstDowncast>::downcast(
                            inst_set, inst_data,
                        )
                    {
                        post_blocks_to_skip.insert(*br.z_dest());
                    }
                }
            }
        }

        // Skip remaining regions that are post-loop return blocks
        // we've already captured. remaining_regions starts at the
        // current region_idx position, so offset 0 = next unprocessed region.
        let mut skip_offset = 0;
        while skip_offset < remaining_regions.len() {
            if let crate::structurize::Region::Block(bid) = &remaining_regions[skip_offset] {
                if post_blocks_to_skip.contains(bid) {
                    *region_idx += 1;
                    skip_offset += 1;
                    continue;
                }
            }
            break;
        }
    }
}

/// Emit only ObjIndex/ObjStore instructions from a block, creating fresh expressions.
/// Used in break/escape paths inside loops where the full block can't be re-emitted.
#[cfg(feature = "spirv-backend")]
fn emit_obj_ops_from_block(
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
    block: sonatina_ir::BlockId,
    func: &mut naga::Function,
    target: &mut naga::Block,
    value_map: &mut std::collections::HashMap<sonatina_ir::ValueId, naga::Handle<naga::Expression>>,
    phi_locals: &mut std::collections::HashMap<
        sonatina_ir::ValueId,
        naga::Handle<naga::LocalVariable>,
    >,
) {
    use sonatina_ir::InstDowncast;
    for inst_id in function.layout.iter_inst(block) {
        let inst_data = function.dfg.inst(inst_id);

        if let Some(obj_index) =
            <&sonatina_ir::inst::data::ObjIndex as InstDowncast>::downcast(inst_set, inst_data)
        {
            if let Some(result) = function.dfg.inst_result(inst_id) {
                let base =
                    resolve_naga_value(*obj_index.object(), function, value_map, phi_locals, func)
                        .unwrap();
                let index =
                    resolve_naga_value(*obj_index.index(), function, value_map, phi_locals, func)
                        .unwrap();
                let i32_idx = func.expressions.append(
                    naga::Expression::As {
                        expr: index,
                        kind: naga::ScalarKind::Sint,
                        convert: Some(4),
                    },
                    naga::Span::UNDEFINED,
                );
                target.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(i32_idx, i32_idx)),
                    naga::Span::UNDEFINED,
                );
                let h = func.expressions.append(
                    naga::Expression::Access {
                        base,
                        index: i32_idx,
                    },
                    naga::Span::UNDEFINED,
                );
                value_map.insert(result, h);
            }
        } else if let Some(obj_store) =
            <&sonatina_ir::inst::data::ObjStore as InstDowncast>::downcast(inst_set, inst_data)
        {
            let dest =
                resolve_naga_value(*obj_store.object(), function, value_map, phi_locals, func)
                    .unwrap();
            let val = resolve_naga_value(*obj_store.value(), function, value_map, phi_locals, func)
                .unwrap();
            target.push(
                naga::Statement::Store {
                    pointer: dest,
                    value: val,
                },
                naga::Span::UNDEFINED,
            );
        }
    }
}

/// Find the return value (ValueId) of a block that contains a Return instruction.
#[cfg(feature = "spirv-backend")]
fn find_block_return_value(
    block: sonatina_ir::BlockId,
    function: &sonatina_ir::Function,
    inst_set: &dyn sonatina_ir::InstSetBase,
) -> Option<sonatina_ir::ValueId> {
    use sonatina_ir::InstDowncast;
    for inst_id in function.layout.iter_inst(block) {
        let inst_data = function.dfg.inst(inst_id);
        if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as InstDowncast>::downcast(
            inst_set, inst_data,
        ) {
            return ret.args().as_slice().first().copied();
        }
    }
    None
}

#[cfg(feature = "spirv-backend")]
fn translate_to_naga(module: &Module, workgroup_size: [u32; 3]) -> Result<naga::Module, String> {
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

    // Scan first function for ObjAlloc to determine output mode
    let funcs_peek = module.funcs();
    let (param_count, has_obj_alloc) = funcs_peek
        .first()
        .map(|&fr| {
            module
                .func_store
                .try_view(fr, |f| {
                    let pc = f.arg_values.len();
                    let has_alloc = f.layout.iter_block().any(|bid| {
                        f.layout.iter_inst(bid).any(|iid| {
                    let inst_data = f.dfg.inst(iid);
                    <&sonatina_ir::inst::data::ObjAlloc as sonatina_ir::InstDowncast>::downcast(
                        f.inst_set(), inst_data
                    ).is_some()
                })
                    });
                    (pc, has_alloc)
                })
                .unwrap_or((0, false))
        })
        .unwrap_or((2, false));

    // Output type: dynamic array for batch (ObjAlloc) or single-value struct for scalar
    let output_type = if has_obj_alloc {
        naga_mod.types.insert(
            naga::Type {
                name: Some("OutputArray".into()),
                inner: naga::TypeInner::Array {
                    base: i64_type,
                    size: naga::ArraySize::Dynamic,
                    stride: 8,
                },
            },
            naga::Span::UNDEFINED,
        )
    } else {
        naga_mod.types.insert(
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
        )
    };

    let effective_params = param_count.max(1);
    let input_members: Vec<naga::StructMember> = (0..effective_params)
        .map(|i| naga::StructMember {
            name: Some(format!("p{i}")),
            ty: i64_type,
            binding: None,
            offset: (i * 8) as u32,
        })
        .collect();
    let input_span = (effective_params * 8) as u32;

    let input_struct = naga_mod.types.insert(
        naga::Type {
            name: Some("Input".into()),
            inner: naga::TypeInner::Struct {
                members: input_members,
                span: input_span,
            },
        },
        naga::Span::UNDEFINED,
    );

    // For batch mode: input is an array of structs, one per invocation
    let input_type = if has_obj_alloc {
        naga_mod.types.insert(
            naga::Type {
                name: Some("InputArray".into()),
                inner: naga::TypeInner::Array {
                    base: input_struct,
                    size: naga::ArraySize::Dynamic,
                    stride: input_span,
                },
            },
            naga::Span::UNDEFINED,
        )
    } else {
        input_struct
    };

    let output_var = naga_mod.global_variables.append(
        naga::GlobalVariable {
            name: Some("output".into()),
            space: naga::AddressSpace::Storage {
                access: naga::StorageAccess::LOAD | naga::StorageAccess::STORE,
            },
            binding: Some(naga::ResourceBinding {
                group: 0,
                binding: 0,
            }),
            ty: output_type,
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
            binding: Some(naga::ResourceBinding {
                group: 0,
                binding: 1,
            }),
            ty: input_type,
            init: None,
            memory_decorations: naga::ir::MemoryDecorations::empty(),
        },
        naga::Span::UNDEFINED,
    );

    // u32 vec3 type for global_invocation_id
    let u32_type = naga_mod.types.insert(
        naga::Type {
            name: None,
            inner: naga::TypeInner::Scalar(naga::Scalar {
                kind: naga::ScalarKind::Uint,
                width: 4,
            }),
        },
        naga::Span::UNDEFINED,
    );
    let vec3_u32_type = naga_mod.types.insert(
        naga::Type {
            name: None,
            inner: naga::TypeInner::Vector {
                size: naga::VectorSize::Tri,
                scalar: naga::Scalar {
                    kind: naga::ScalarKind::Uint,
                    width: 4,
                },
            },
        },
        naga::Span::UNDEFINED,
    );

    // Build the entry point function
    let arguments = if has_obj_alloc {
        vec![naga::FunctionArgument {
            name: Some("global_id".into()),
            ty: vec3_u32_type,
            binding: Some(naga::Binding::BuiltIn(naga::BuiltIn::GlobalInvocationId)),
        }]
    } else {
        vec![]
    };

    let mut func = naga::Function {
        name: Some("main".into()),
        arguments,
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

            // For batch mode (ObjAlloc), inject the output buffer into the value_map
            if has_obj_alloc {
                let output_expr = func.expressions.append(
                    naga::Expression::GlobalVariable(output_var),
                    naga::Span::UNDEFINED,
                );
                value_map.insert(sonatina_ir::ValueId(u32::MAX), output_expr);
            }

            // Load function args from input buffer
            let input_global = func.expressions.append(
                naga::Expression::GlobalVariable(input_var),
                naga::Span::UNDEFINED,
            );

            // In batch mode, index into the input array with global_invocation_id.x
            let input_expr = if has_obj_alloc {
                let gid_u32 = func
                    .expressions
                    .append(naga::Expression::FunctionArgument(0), naga::Span::UNDEFINED);
                let gid_x = func.expressions.append(
                    naga::Expression::AccessIndex {
                        base: gid_u32,
                        index: 0,
                    },
                    naga::Span::UNDEFINED,
                );
                func.body.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(gid_x, gid_x)),
                    naga::Span::UNDEFINED,
                );
                // Cast u32 to i32 for Access index
                let gid_i32 = func.expressions.append(
                    naga::Expression::As {
                        expr: gid_x,
                        kind: naga::ScalarKind::Sint,
                        convert: Some(4),
                    },
                    naga::Span::UNDEFINED,
                );
                func.body.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(gid_i32, gid_i32)),
                    naga::Span::UNDEFINED,
                );
                // input[gid.x] -> pointer to InputStruct for this invocation
                func.expressions.append(
                    naga::Expression::Access {
                        base: input_global,
                        index: gid_i32,
                    },
                    naga::Span::UNDEFINED,
                )
            } else {
                input_global
            };

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
                // Emit AccessIndex and Load individually to avoid range
                // overlap issues when there are 3+ parameters
                func.body.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(field, field)),
                    naga::Span::UNDEFINED,
                );
                func.body.push(
                    naga::Statement::Emit(naga::Range::new_from_bounds(loaded, loaded)),
                    naga::Span::UNDEFINED,
                );
                value_map.insert(arg_val, loaded);
            }

            // Check for loops via structurizer
            let structured = crate::structurize::structurize_function(function);
            let has_loops = structured.as_ref().map_or(false, |s| {
                s.regions
                    .iter()
                    .any(|r| matches!(r, crate::structurize::Region::Loop { .. }))
            });

            if has_loops {
                let scfg = structured.unwrap();
                emit_naga_regions(
                    function,
                    inst_set,
                    &scfg.regions,
                    i64_type,
                    &mut func,
                    &mut value_map,
                    &mut phi_locals,
                    &mut result_expr,
                );
            } else {
                // Linear fallback
                for block in function.layout.iter_block() {
                    emit_naga_block_instructions(
                        function,
                        inst_set,
                        block,
                        i64_type,
                        &mut func,
                        &mut value_map,
                        &mut phi_locals,
                        &mut result_expr,
                    );
                }
            }
        });
    }

    // For scalar output, store result to output buffer struct.
    // For batch mode (ObjAlloc), ObjStore already wrote to the buffer.
    if !has_obj_alloc {
        let output_expr = func.expressions.append(
            naga::Expression::GlobalVariable(output_var),
            naga::Span::UNDEFINED,
        );
        let result_field = func.expressions.append(
            naga::Expression::AccessIndex {
                base: output_expr,
                index: 0,
            },
            naga::Span::UNDEFINED,
        );

        let final_val = result_expr.unwrap_or_else(|| {
            func.expressions.append(
                naga::Expression::Literal(naga::Literal::I64(0)),
                naga::Span::UNDEFINED,
            )
        });

        func.body.push(
            naga::Statement::Store {
                pointer: result_field,
                value: final_val,
            },
            naga::Span::UNDEFINED,
        );
    }

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
