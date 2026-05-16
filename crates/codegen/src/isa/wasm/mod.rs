//! WASM backend: Sonatina IR → WebAssembly module via WAFFLE.
//!
//! Translates Sonatina IR to WAFFLE's SSA IR (block params, operators),
//! then WAFFLE handles control flow recovery (Ramsey's algorithm) and
//! WASM emission automatically.

mod translate;

use sonatina_ir::Module;

use crate::backend::Backend;

#[derive(Debug)]
pub enum WasmError {
    UnsupportedTarget(String),
    Translation(String),
    UnsupportedType(String),
    UnsupportedInstruction(String),
}

impl std::fmt::Display for WasmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedTarget(msg) => write!(f, "unsupported target: {msg}"),
            Self::Translation(msg) => write!(f, "wasm translation error: {msg}"),
            Self::UnsupportedType(msg) => write!(f, "unsupported type for wasm: {msg}"),
            Self::UnsupportedInstruction(msg) => write!(f, "unsupported wasm instruction: {msg}"),
        }
    }
}

pub struct WasmArtifact {
    pub bytes: Vec<u8>,
    pub func_names: Vec<String>,
}

pub struct WasmBackend;

impl WasmBackend {
    pub fn new() -> Self {
        Self
    }
}

impl Backend for WasmBackend {
    type Artifact = WasmArtifact;
    type Error = WasmError;

    fn compile_module(&self, module: &Module) -> Result<Self::Artifact, Vec<Self::Error>> {
        let (wasm_module, func_names) =
            translate::translate_module(module).map_err(|e| vec![WasmError::Translation(e)])?;

        let bytes = wasm_module
            .to_wasm_bytes()
            .map_err(|e| vec![WasmError::Translation(format!("WAFFLE emission: {e}"))])?;

        Ok(WasmArtifact { bytes, func_names })
    }
}
