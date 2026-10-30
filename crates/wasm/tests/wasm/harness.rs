//! Shared helpers: parsing, compiling, validating and executing modules.

use sonatina_codegen::{Backend, BackendOptions};
use sonatina_ir::Module;
use sonatina_wasm::WasmBackend;
use wasmtime::{Engine, Func, Instance, Linker, Store, Val};

pub const TARGET: &str = "wasm32-unknown-native";

pub fn parse(source: &str) -> Module {
    parse_with_target(TARGET, source)
}

pub fn parse_with_target(target: &str, source: &str) -> Module {
    sonatina_parser::parse_module(&format!("target = \"{target}\"\n{source}"))
        .unwrap_or_else(|errors| panic!("IR should parse: {errors:?}\n{source}"))
        .module
}

/// Compile with the backend's default options, without the optimizer.
pub fn compile(module: &Module) -> Vec<u8> {
    WasmBackend::new()
        .compile_module(module, &BackendOptions::default())
        .unwrap_or_else(|errors| panic!("wasm compilation failed: {errors:?}"))
        .into_bytes()
}

pub fn validate(bytes: &[u8]) {
    wasmparser::Validator::new()
        .validate_all(bytes)
        .unwrap_or_else(|error| panic!("emitted module is invalid: {error}"));
}

/// Compile a module, require that the bytes validate and that a second
/// compilation of the same module gives the same bytes.
pub fn compile_valid(module: &Module) -> Vec<u8> {
    let bytes = compile(module);
    validate(&bytes);
    assert_eq!(bytes, compile(module), "compilation is not deterministic");
    bytes
}

/// A running instance of an emitted module.
pub struct Machine {
    store: Store<()>,
    instance: Instance,
}

impl Machine {
    pub fn new(bytes: &[u8]) -> Self {
        Self::with_imports(bytes, |_| {})
    }

    pub fn with_imports(bytes: &[u8], define: impl FnOnce(&mut Linker<()>)) -> Self {
        let engine = Engine::default();
        let module = wasmtime::Module::new(&engine, bytes).expect("wasmtime accepts the module");
        let mut linker = Linker::new(&engine);
        define(&mut linker);
        let mut store = Store::new(&engine, ());
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("module instantiates");
        Self { store, instance }
    }

    pub fn func(&mut self, name: &str) -> Func {
        self.instance
            .get_func(&mut self.store, name)
            .unwrap_or_else(|| panic!("module does not export `{name}`"))
    }

    pub fn has_export(&mut self, name: &str) -> bool {
        self.instance.get_export(&mut self.store, name).is_some()
    }

    pub fn try_call(&mut self, func: &Func, args: &[Val]) -> Result<Vec<Val>, wasmtime::Error> {
        let mut results = vec![Val::I32(0); func.ty(&self.store).results().len()];
        func.call(&mut self.store, args, &mut results)?;
        Ok(results)
    }

    pub fn call(&mut self, func: &Func, args: &[Val]) -> Vec<Val> {
        self.try_call(func, args)
            .unwrap_or_else(|error| panic!("call trapped: {error:?} with {args:?}"))
    }

    pub fn memory(&mut self) -> wasmtime::Memory {
        self.instance
            .get_memory(&mut self.store, "memory")
            .expect("module exports its memory")
    }

    /// The size of the memory in bytes.
    pub fn memory_size(&mut self) -> usize {
        let memory = self.memory();
        memory.data_size(&self.store)
    }

    /// Grow the memory by `pages`, as the host may.
    pub fn grow_memory(&mut self, pages: u64) {
        let memory = self.memory();
        memory
            .grow(&mut self.store, pages)
            .expect("the host can grow the memory");
    }

    pub fn read(&mut self, address: usize, len: usize) -> Vec<u8> {
        let memory = self.memory();
        memory.data(&self.store)[address..address + len].to_vec()
    }

    pub fn write(&mut self, address: usize, bytes: &[u8]) {
        let memory = self.memory();
        memory.data_mut(&mut self.store)[address..address + bytes.len()].copy_from_slice(bytes);
    }
}

pub fn i32s(values: &[Val]) -> Vec<i32> {
    values.iter().map(|v| v.unwrap_i32()).collect()
}
