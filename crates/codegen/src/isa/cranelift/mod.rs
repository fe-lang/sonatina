#![doc = include_str!("../../../docs/native.md")]

mod translate;

use std::sync::Arc;

#[cfg(feature = "cranelift-jit")]
use std::collections::HashMap;

use cranelift_codegen::{
    isa as clif_isa,
    settings::{self, Configurable},
};
#[cfg(feature = "cranelift-jit")]
use cranelift_jit::{JITBuilder, JITModule};
#[cfg(feature = "cranelift-jit")]
use cranelift_module::FuncId;
use cranelift_object::{ObjectBuilder, ObjectModule};
use sonatina_ir::Module;
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerifierConfig, verify_function_signature};

use crate::{
    backend::{Backend, BackendOptions},
    compile::OptLevel,
    transform::aggregate::{EnumLowerToProduct, object_abi::legalize_native_object_returns},
};

#[derive(Debug)]
pub enum CraneliftError {
    UnsupportedTarget(String),
    Translation(String),
    Compilation(String),
}

impl std::fmt::Display for CraneliftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedTarget(message) => write!(f, "unsupported target: {message}"),
            Self::Translation(message) => write!(f, "translation error: {message}"),
            Self::Compilation(message) => write!(f, "compilation error: {message}"),
        }
    }
}

impl std::error::Error for CraneliftError {}

#[derive(Debug)]
pub struct CraneliftObjectArtifact {
    bytes: Vec<u8>,
}

impl CraneliftObjectArtifact {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

#[derive(Debug, Default)]
pub struct CraneliftObjectBackend;

impl CraneliftObjectBackend {
    pub fn new() -> Self {
        Self
    }

    fn flags(options: &BackendOptions, is_pic: bool) -> Result<settings::Flags, CraneliftError> {
        let mut builder = settings::builder();
        builder
            .set("opt_level", cranelift_opt_level(options.opt_level))
            .map_err(|error| CraneliftError::Compilation(error.to_string()))?;
        builder
            .set("is_pic", if is_pic { "true" } else { "false" })
            .map_err(|error| CraneliftError::Compilation(error.to_string()))?;
        // The native ABI passes i128 scalars directly. Cranelift's x86_64
        // calling conventions require LLVM ABI extensions for these values.
        builder
            .set("enable_llvm_abi_extensions", "true")
            .map_err(|error| CraneliftError::Compilation(error.to_string()))?;
        Ok(settings::Flags::new(builder))
    }

    fn build_isa(
        triple: TargetTriple,
        options: &BackendOptions,
    ) -> Result<Arc<dyn clif_isa::TargetIsa>, CraneliftError> {
        ensure_host_native_target(triple)?;
        let flags = Self::flags(options, true)?;

        #[cfg(target_os = "macos")]
        {
            let name = match triple.architecture {
                Architecture::X86_64 => "x86_64-apple-macosx",
                Architecture::Aarch64 => "aarch64-apple-macosx",
                Architecture::Evm => unreachable!("target validation rejected EVM"),
            };
            let mut builder = clif_isa::lookup_by_name(name)
                .map_err(|error| CraneliftError::UnsupportedTarget(error.to_string()))?;
            cranelift_native::infer_native_flags(&mut builder)
                .map_err(|error| CraneliftError::UnsupportedTarget(error.to_string()))?;
            builder
                .finish(flags)
                .map_err(|error| CraneliftError::Compilation(error.to_string()))
        }

        #[cfg(not(target_os = "macos"))]
        build_native_isa(flags)
    }
}

#[cfg(feature = "cranelift-jit")]
pub struct CraneliftJitArtifact {
    module: JITModule,
    functions: HashMap<String, FuncId>,
}

#[cfg(feature = "cranelift-jit")]
impl CraneliftJitArtifact {
    /// Returns the address of a finalized function while this artifact lives.
    ///
    /// Calling the address is unsafe: the caller must use the exact native ABI
    /// corresponding to the Sonatina function signature, provide valid argument
    /// storage, and keep this artifact alive throughout the call. In particular,
    /// indirect results use a platform-specific hidden return buffer, not an
    /// ordinary C struct result. Prefer public scalar/pointer wrappers; see the
    /// [module's ABI contract](crate::isa::cranelift) for the supported C subset.
    pub fn function_address(&self, name: &str) -> Option<*const u8> {
        self.functions
            .get(name)
            .map(|function| self.module.get_finalized_function(*function))
    }
}

#[cfg(feature = "cranelift-jit")]
#[derive(Debug, Default)]
pub struct CraneliftJitBackend;

#[cfg(feature = "cranelift-jit")]
impl CraneliftJitBackend {
    pub fn new() -> Self {
        Self
    }
}

#[cfg(feature = "cranelift-jit")]
impl Backend for CraneliftJitBackend {
    type Artifact = CraneliftJitArtifact;
    type Error = CraneliftError;

    fn compile_module(
        &self,
        module: &Module,
        options: &BackendOptions,
    ) -> Result<Self::Artifact, Vec<Self::Error>> {
        ensure_host_native_target(module.ctx.triple).map_err(|error| vec![error])?;

        let module = module.clone_for_funcs(&module.funcs());
        legalize_module(&module).map_err(|error| vec![CraneliftError::Translation(error)])?;

        let flags = CraneliftObjectBackend::flags(options, false).map_err(|error| vec![error])?;
        let isa = build_native_isa(flags).map_err(|error| vec![error])?;
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut jit = JITModule::new(builder);
        let functions = translate::translate_module(&module, &mut jit)
            .map_err(|error| vec![CraneliftError::Translation(error)])?;
        jit.finalize_definitions()
            .map_err(|error| vec![CraneliftError::Compilation(error.to_string())])?;

        Ok(CraneliftJitArtifact {
            module: jit,
            functions,
        })
    }
}

#[cfg(any(feature = "cranelift-jit", not(target_os = "macos")))]
fn build_native_isa(
    flags: settings::Flags,
) -> Result<Arc<dyn clif_isa::TargetIsa>, CraneliftError> {
    cranelift_native::builder()
        .map_err(|error| CraneliftError::UnsupportedTarget(error.to_string()))?
        .finish(flags)
        .map_err(|error| CraneliftError::Compilation(error.to_string()))
}

impl Backend for CraneliftObjectBackend {
    type Artifact = CraneliftObjectArtifact;
    type Error = CraneliftError;

    fn compile_module(
        &self,
        module: &Module,
        options: &BackendOptions,
    ) -> Result<Self::Artifact, Vec<Self::Error>> {
        ensure_host_native_target(module.ctx.triple).map_err(|error| vec![error])?;

        let module = module.clone_for_funcs(&module.funcs());
        legalize_module(&module).map_err(|error| vec![CraneliftError::Translation(error)])?;

        let isa = Self::build_isa(module.ctx.triple, options).map_err(|error| vec![error])?;
        let builder =
            ObjectBuilder::new(isa, "sonatina", cranelift_module::default_libcall_names())
                .map_err(|error| vec![CraneliftError::Compilation(error.to_string())])?;
        let mut object = ObjectModule::new(builder);

        translate::translate_module(&module, &mut object)
            .map_err(|error| vec![CraneliftError::Translation(error)])?;
        let bytes = object
            .finish()
            .emit()
            .map_err(|error| vec![CraneliftError::Compilation(error.to_string())])?;

        Ok(CraneliftObjectArtifact { bytes })
    }
}

fn legalize_module(module: &Module) -> Result<(), String> {
    EnumLowerToProduct.run(module);
    for func in module.funcs() {
        let report = verify_function_signature(&module.ctx, func, &VerifierConfig::default());
        if report.has_errors() {
            return Err(report.to_string());
        }
    }
    legalize_native_object_returns(module)
}

fn cranelift_opt_level(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "none",
        OptLevel::O1 | OptLevel::O2 => "speed",
        OptLevel::Os => "speed_and_size",
    }
}

fn ensure_host_native_target(triple: TargetTriple) -> Result<(), CraneliftError> {
    let host = host_architecture().ok_or_else(|| {
        CraneliftError::UnsupportedTarget(
            "Cranelift requires an x86_64 or aarch64 host".to_string(),
        )
    })?;
    if triple.architecture == host
        && triple.vendor == Vendor::Unknown
        && triple.operating_system == OperatingSystem::Native
    {
        Ok(())
    } else {
        Err(CraneliftError::UnsupportedTarget(format!(
            "native target {triple} does not match the {host} host"
        )))
    }
}

fn host_architecture() -> Option<Architecture> {
    if cfg!(target_arch = "x86_64") {
        Some(Architecture::X86_64)
    } else if cfg!(target_arch = "aarch64") {
        Some(Architecture::Aarch64)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::{CraneliftObjectBackend, cranelift_opt_level};
    use crate::{backend::BackendOptions, compile::OptLevel};

    #[test]
    fn object_and_jit_flags_enable_direct_i128_signatures() {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for is_pic in [false, true] {
                let flags =
                    CraneliftObjectBackend::flags(&BackendOptions { opt_level }, is_pic).unwrap();
                assert!(flags.enable_llvm_abi_extensions());
            }
        }
    }

    #[test]
    fn sonatina_opt_levels_map_to_cranelift_opt_levels() {
        assert_eq!(cranelift_opt_level(OptLevel::O0), "none");
        assert_eq!(cranelift_opt_level(OptLevel::O1), "speed");
        assert_eq!(cranelift_opt_level(OptLevel::Os), "speed_and_size");
        assert_eq!(cranelift_opt_level(OptLevel::O2), "speed");
    }
}
