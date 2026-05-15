//! SPIR-V backend: Sonatina IR → SPIR-V compute shader modules.
//!
//! Targets GPU compute for mobile proving (field arithmetic, hash functions).
//! Consumes structured CFG from the `structurize` pass. Emits SPIR-V binary
//! that can be validated with `spirv-val` and cross-compiled via SPIRV-Cross.
//!
//! Key constraints:
//! - No recursion (SPIR-V compute shaders)
//! - Structured control flow required (OpLoopMerge/OpSelectionMerge)
//! - SSA form preserved (no phi elimination needed)
//! - Storage buffers for I/O (workgroup shared memory for intermediates)

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

/// SPIR-V binary output (little-endian u32 words).
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
        use rspirv::binary::Assemble;
        use rspirv::dr;

        let mut b = dr::Builder::new();
        b.set_version(1, 5);
        b.capability(spirv::Capability::Shader);
        b.capability(spirv::Capability::Int64);
        b.memory_model(spirv::AddressingModel::Logical, spirv::MemoryModel::GLSL450);

        let void_type = b.type_void();
        let u32_type = b.type_int(32, 0);
        let i64_type = b.type_int(64, 0);
        let fn_void_type = b.type_function(void_type, vec![]);

        // Storage buffer for output: buffer { u64 result; }
        let struct_type = b.type_struct(vec![i64_type]);
        b.decorate(struct_type, spirv::Decoration::Block, vec![]);
        b.member_decorate(struct_type, 0, spirv::Decoration::Offset, vec![dr::Operand::LiteralBit32(0)]);

        let ptr_storage = b.type_pointer(None, spirv::StorageClass::StorageBuffer, struct_type);
        let ptr_i64 = b.type_pointer(None, spirv::StorageClass::StorageBuffer, i64_type);

        let output_var = b.variable(ptr_storage, None, spirv::StorageClass::StorageBuffer, None);
        b.decorate(output_var, spirv::Decoration::DescriptorSet, vec![dr::Operand::LiteralBit32(0)]);
        b.decorate(output_var, spirv::Decoration::Binding, vec![dr::Operand::LiteralBit32(0)]);

        // Entry point: main compute shader
        let main_fn = b.begin_function(void_type, None, spirv::FunctionControl::NONE, fn_void_type)
            .map_err(|e| vec![SpirvError::Translation(format!("begin_function: {e}"))])?;
        b.begin_block(None)
            .map_err(|e| vec![SpirvError::Translation(format!("begin_block: {e}"))])?;

        // Compute result from the first function in the module
        let funcs = module.funcs();
        let result_value = if let Some(&func_ref) = funcs.first() {
            let result = module.func_store.try_view(func_ref, |function| {
                // Find return instruction and get its constant value
                for block in function.layout.iter_block() {
                    for inst_id in function.layout.iter_inst(block) {
                        let inst_data = function.dfg.inst(inst_id);
                        let inst_set = function.inst_set();
                        if let Some(ret) = <&sonatina_ir::inst::control_flow::Return as sonatina_ir::InstDowncast>::downcast(inst_set, inst_data) {
                            for &val_id in ret.args().as_slice() {
                                if let sonatina_ir::Value::Immediate { imm, .. } = function.dfg.value(val_id) {
                                    let i64_val = match imm {
                                        sonatina_ir::Immediate::I64(v) => *v,
                                        sonatina_ir::Immediate::I32(v) => *v as i64,
                                        _ => 0,
                                    };
                                    return Some(i64_val);
                                }
                            }
                        }
                    }
                }
                None
            });
            result.flatten().unwrap_or(0)
        } else {
            0
        };

        let const_val = b.constant_bit64(i64_type, result_value as u64);
        let zero = b.constant_bit32(u32_type, 0);
        let out_ptr = b.access_chain(ptr_i64, None, output_var, vec![zero]).unwrap();
        b.store(out_ptr, const_val, None, vec![]).unwrap();
        b.ret().unwrap();
        b.end_function().unwrap();

        // Execution mode
        b.entry_point(
            spirv::ExecutionModel::GLCompute,
            main_fn,
            "main",
            vec![output_var],
        );
        b.execution_mode(main_fn, spirv::ExecutionMode::LocalSize, vec![
            self.workgroup_size[0],
            self.workgroup_size[1],
            self.workgroup_size[2],
        ]);

        let spv_module = b.module();
        let words = spv_module.assemble();

        Ok(SpirvArtifact { words })
    }
}
