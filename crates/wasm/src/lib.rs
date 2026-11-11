#![doc = include_str!("../README.md")]

mod arith;
mod dce;
mod heap;
mod memory;
mod tail;
mod translate;
mod wide;

use sonatina_ir::Module;
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerifierConfig, verify_function_signature};

use sonatina_codegen::{
    backend::{Backend, BackendOptions},
    optim::Pipeline,
    transform::aggregate::{EnumTagLower, check_frame_lifetimes},
};

/// The import module used for `extern` functions unless
/// [`WasmBackend::with_import_module`] selects another.
pub const DEFAULT_IMPORT_MODULE: &str = "env";

/// The names under which [`WasmBackend::with_host_allocator`] exports the
/// allocator: `alloc(size) -> address`, `arena_mark() -> address` and
/// `arena_release(mark)`.
pub const HOST_ALLOCATOR_EXPORTS: [&str; 3] = ["alloc", "arena_mark", "arena_release"];

#[derive(Debug)]
pub enum WasmError {
    /// The module does not target `wasm32-unknown-native`.
    UnsupportedTarget(String),
    /// The module uses an instruction, type or declaration that this backend
    /// does not translate. The message names it.
    Unsupported(String),
    /// The module is malformed in a way that translation cannot repair, such
    /// as an operand of the wrong type or a call with the wrong arity.
    Invalid(String),
    /// WAFFLE failed to emit the module.
    Emission(String),
}

impl std::fmt::Display for WasmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedTarget(message) => write!(f, "unsupported target: {message}"),
            Self::Unsupported(message) => write!(f, "unsupported by the wasm backend: {message}"),
            Self::Invalid(message) => write!(f, "invalid input for the wasm backend: {message}"),
            Self::Emission(message) => write!(f, "wasm emission failed: {message}"),
        }
    }
}

impl std::error::Error for WasmError {}

/// An encoded WebAssembly module.
#[derive(Debug)]
pub struct WasmArtifact {
    bytes: Vec<u8>,
    exports: Vec<String>,
}

impl WasmArtifact {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Names of the exported functions, in module order. The linear memory is
    /// also exported, as `memory`.
    pub fn exported_functions(&self) -> &[String] {
        &self.exports
    }
}

#[derive(Debug, Clone)]
pub struct WasmBackend {
    import_module: String,
    stack_bytes: u32,
    host_allocator: bool,
    heap_poison: bool,
}

impl Default for WasmBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl WasmBackend {
    pub fn new() -> Self {
        Self {
            import_module: DEFAULT_IMPORT_MODULE.to_string(),
            stack_bytes: memory::DEFAULT_STACK_BYTES,
            host_allocator: false,
            heap_poison: false,
        }
    }

    /// Select the import module under which every `extern` function is
    /// imported. The import field name is the function's symbol.
    pub fn with_import_module(mut self, module: impl Into<String>) -> Self {
        self.import_module = module.into();
        self
    }

    /// Set the size of the stack, in bytes. The stack holds the frames of all
    /// active calls, and a call that does not fit traps. The default is
    /// [`DEFAULT_STACK_BYTES`]. A module that needs no frames, global data or
    /// arena has no stack and ignores the setting.
    pub fn with_stack_size(mut self, bytes: u32) -> Self {
        self.stack_bytes = bytes;
        self
    }

    /// Fill the payload of every block that `free` releases, except its first
    /// word (the link of the free list), with the byte `0xA5`. A program that
    /// reads a block after freeing it then sees that pattern, and a comparison
    /// with a build for another target turns the use after free into a wrong
    /// answer. It costs one `memory.fill` for each `free`, and is meant for tests.
    pub fn with_heap_poison(mut self) -> Self {
        self.heap_poison = true;
        self
    }

    /// Export the arena to the host, so that it can place data in linear
    /// memory before a call: `alloc(size) -> address`, `arena_mark() ->
    /// address` and `arena_release(mark)`, named by [`HOST_ALLOCATOR_EXPORTS`].
    /// The module then has a stack and an arena even if its code uses neither,
    /// and no function of the module may have one of these names. See the
    /// section "The host allocator" of the module documentation for the protocol.
    pub fn with_host_allocator(mut self) -> Self {
        self.host_allocator = true;
        self
    }
}

/// The default size of the stack, 1 MiB.
pub const DEFAULT_STACK_BYTES: u32 = memory::DEFAULT_STACK_BYTES;

/// Prepare a copy of the module for translation, as the native backend does:
/// enum tags become integers, enums keep the layout of the target, and objects
/// are checked against the frame rule of `obj.alloc`: no reference outlives
/// its frame.
fn legalize_module(module: &Module) -> Result<(), WasmError> {
    EnumTagLower.run(module);
    for func in module.funcs() {
        let report = verify_function_signature(&module.ctx, func, &VerifierConfig::default());
        if report.has_errors() {
            return Err(WasmError::Invalid(report.to_string()));
        }
    }
    check_frame_lifetimes(module).map_err(WasmError::Unsupported)
}

impl Backend for WasmBackend {
    type Artifact = WasmArtifact;
    type Error = WasmError;

    fn pipeline(&self, options: &BackendOptions) -> Pipeline {
        Pipeline::native(options.opt_level)
    }

    fn compile_module(
        &self,
        module: &Module,
        options: &BackendOptions,
    ) -> Result<Self::Artifact, Vec<Self::Error>> {
        ensure_wasm32_target(module.ctx.triple).map_err(|error| vec![error])?;

        let module = module.clone_for_funcs(&module.funcs());
        legalize_module(&module).map_err(|error| vec![error])?;
        let mut translated = translate::translate_module(
            &module,
            &self.import_module,
            self.stack_bytes,
            self.host_allocator,
            self.heap_poison,
            options.opt_level,
        )
        .map_err(|error| vec![error])?;
        dce::run(&mut translated.module);
        let imported = translated.module.imports.len() as u32;
        let bytes = translated
            .module
            .to_wasm_bytes()
            .map_err(|error| WasmError::Emission(error.to_string()))
            .and_then(|bytes| tail::rewrite(bytes, imported, &translated.tail_calls))
            .map_err(|error| vec![error])?;

        Ok(WasmArtifact {
            bytes,
            exports: translated.exports,
        })
    }
}

fn ensure_wasm32_target(triple: TargetTriple) -> Result<(), WasmError> {
    if triple.architecture == Architecture::Wasm32
        && triple.vendor == Vendor::Unknown
        && triple.operating_system == OperatingSystem::Native
    {
        Ok(())
    } else {
        Err(WasmError::UnsupportedTarget(format!(
            "the wasm backend requires wasm32-unknown-native, not {triple}"
        )))
    }
}
