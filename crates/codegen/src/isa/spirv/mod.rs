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

    fn compile_module(&self, _module: &Module) -> Result<Self::Artifact, Vec<Self::Error>> {
        Err(vec![SpirvError::Translation(
            "SPIR-V backend not yet implemented — requires structurize pass integration and \
             rspirv or manual SPIR-V binary emission"
                .to_string(),
        )])
    }
}
