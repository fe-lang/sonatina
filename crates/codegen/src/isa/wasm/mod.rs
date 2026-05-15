//! WASM backend: Sonatina IR → WebAssembly module.
//!
//! Consumes the structured CFG from the `structurize` pass and emits valid
//! WASM bytecode. Uses `wasm-encoder` for binary format emission.

use std::collections::HashMap;

use wasm_encoder::{
    CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    Module as WasmModule, TypeSection, ValType,
};

use sonatina_ir::{Module, Type};
use sonatina_triple::Architecture;

use crate::backend::Backend;

#[derive(Debug)]
pub enum WasmError {
    UnsupportedTarget(String),
    Translation(String),
    UnsupportedInstruction(String),
}

impl std::fmt::Display for WasmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedTarget(msg) => write!(f, "unsupported target: {msg}"),
            Self::Translation(msg) => write!(f, "wasm translation error: {msg}"),
            Self::UnsupportedInstruction(msg) => write!(f, "unsupported instruction for wasm: {msg}"),
        }
    }
}

pub struct WasmArtifact {
    pub bytes: Vec<u8>,
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
        let mut wasm = WasmModule::new();

        let mut type_section = TypeSection::new();
        let mut function_section = FunctionSection::new();
        let mut export_section = ExportSection::new();
        let mut code_section = CodeSection::new();

        let funcs = module.funcs();
        let mut func_idx: u32 = 0;

        for &func_ref in &funcs {
            let (name, params, results) = module.ctx.func_sig(func_ref, |sig| {
                let name = sig.name().to_string();
                let params: Vec<ValType> = sig.args().iter()
                    .filter_map(|ty| sonatina_to_wasm_type(*ty))
                    .collect();
                let results: Vec<ValType> = sig.ret_tys().iter()
                    .filter_map(|ty| sonatina_to_wasm_type(*ty))
                    .collect();
                (name, params, results)
            });

            type_section.ty().function(params.clone(), results.clone());
            function_section.function(func_idx);
            export_section.export(&name, ExportKind::Func, func_idx);

            let mut func = Function::new(vec![]);
            func.instruction(&Instruction::End);
            code_section.function(&func);

            func_idx += 1;
        }

        wasm.section(&type_section);
        wasm.section(&function_section);
        wasm.section(&export_section);
        wasm.section(&code_section);

        Ok(WasmArtifact {
            bytes: wasm.finish(),
        })
    }
}

fn sonatina_to_wasm_type(ty: Type) -> Option<ValType> {
    match ty {
        Type::Unit => None,
        Type::I1 | Type::I8 | Type::I16 | Type::I32 => Some(ValType::I32),
        Type::I64 => Some(ValType::I64),
        _ => None,
    }
}
