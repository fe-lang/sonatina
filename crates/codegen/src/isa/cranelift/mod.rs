mod translate;
pub mod u256_runtime;

use std::{collections::HashMap, sync::Arc};

use cranelift_codegen::{
    isa as clif_isa,
    settings::{self, Configurable},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Module as ClifModule};

use sonatina_ir::Module;
use sonatina_triple::Architecture;

use crate::backend::Backend;

#[derive(Debug)]
pub enum CraneliftError {
    UnsupportedTarget(String),
    Translation(String),
    Compilation(String),
}

impl std::fmt::Display for CraneliftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedTarget(msg) => write!(f, "unsupported target: {msg}"),
            Self::Translation(msg) => write!(f, "translation error: {msg}"),
            Self::Compilation(msg) => write!(f, "compilation error: {msg}"),
        }
    }
}

pub struct CraneliftArtifact {
    jit: JITModule,
    func_map: HashMap<String, FuncId>,
}

impl CraneliftArtifact {
    /// Look up a compiled function by name and return a callable pointer.
    ///
    /// # Safety
    /// The caller must ensure the function signature matches the actual
    /// compiled signature.
    pub unsafe fn get_func_ptr<F>(&self, name: &str) -> Option<*const F> {
        let func_id = self.func_map.get(name)?;
        let ptr = self.jit.get_finalized_function(*func_id);
        Some(ptr as *const F)
    }
}

pub struct CraneliftBackend {
    opt_level: settings::OptLevel,
}

impl CraneliftBackend {
    pub fn new() -> Self {
        Self {
            opt_level: settings::OptLevel::None,
        }
    }

    pub fn with_opt_level(mut self, level: settings::OptLevel) -> Self {
        self.opt_level = level;
        self
    }

    fn build_isa(&self) -> Result<Arc<dyn clif_isa::TargetIsa>, CraneliftError> {
        let mut flag_builder = settings::builder();
        flag_builder
            .set(
                "opt_level",
                match self.opt_level {
                    settings::OptLevel::None => "none",
                    settings::OptLevel::Speed => "speed",
                    settings::OptLevel::SpeedAndSize => "speed_and_size",
                },
            )
            .map_err(|e| CraneliftError::Compilation(e.to_string()))?;
        let flags = settings::Flags::new(flag_builder);
        let isa = cranelift_native::builder()
            .map_err(|e| CraneliftError::UnsupportedTarget(e.to_string()))?
            .finish(flags)
            .map_err(|e| CraneliftError::Compilation(e.to_string()))?;
        Ok(isa.into())
    }
}

impl Backend for CraneliftBackend {
    type Artifact = CraneliftArtifact;
    type Error = CraneliftError;

    fn compile_module(&self, module: &Module) -> Result<Self::Artifact, Vec<Self::Error>> {
        let triple = module.ctx.triple;
        if !matches!(
            triple.architecture,
            Architecture::X86_64 | Architecture::Aarch64
        ) {
            return Err(vec![CraneliftError::UnsupportedTarget(format!(
                "CraneliftBackend requires x86_64 or aarch64 target, got {triple}"
            ))]);
        }

        let isa = self.build_isa().map_err(|e| vec![e])?;
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // Register u256 runtime intrinsics
        builder.symbol("__u256_add", u256_runtime::__u256_add as *const u8);
        builder.symbol("__u256_sub", u256_runtime::__u256_sub as *const u8);
        builder.symbol("__u256_mul", u256_runtime::__u256_mul as *const u8);
        builder.symbol("__u256_eq", u256_runtime::__u256_eq as *const u8);
        builder.symbol("__u256_lt", u256_runtime::__u256_lt as *const u8);
        builder.symbol("__u256_is_zero", u256_runtime::__u256_is_zero as *const u8);
        builder.symbol("__u256_addmod", u256_runtime::__u256_addmod as *const u8);
        builder.symbol("__u256_mulmod", u256_runtime::__u256_mulmod as *const u8);

        let mut jit = JITModule::new(builder);

        let func_map = translate::translate_module(module, &mut jit)
            .map_err(|e| vec![CraneliftError::Translation(e)])?;

        jit.finalize_definitions()
            .map_err(|e| vec![CraneliftError::Compilation(e.to_string())])?;

        Ok(CraneliftArtifact { jit, func_map })
    }
}
