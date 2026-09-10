//! High-level compilation entrypoint that bundles the optimization pipeline
//! and EVM codegen into a single API.
//!
//! Frontends typically only need [`EvmCompile`]: hand it a lowered [`Module`]
//! plus an [`OptLevel`], optionally inspect the optimized IR via
//! [`EvmCompile::optimize`], then produce object artifacts via
//! [`EvmCompile::compile`].

use sonatina_ir::{InstId, Module, isa::evm::Evm, module::FuncRef};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use crate::{
    isa::evm::{EvmBackend, ImmediateMaterializationMode, LateCleanupProfile},
    object::{CompileOptions, ObjectArtifact, ObjectCompileError, compile_all_objects},
    optim::Pipeline,
    stackalloc::StackifySearchProfile,
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum OptLevel {
    #[default]
    O0,
    O1,
    Os,
    O2,
}

/// An optimized-IR instruction id, the namespace a frontend stamps provenance
/// against. Distinct from `MachineInstId` so a machine id cannot be handed to
/// the stamping door by mistake. Use `.raw()` to cross to a bare `InstId`. The
/// inner field is pub on purpose: crossing namespaces requires writing the wrap
/// explicitly, which is the reviewable act; the type does not try to prevent
/// deliberate reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct OptInstId(pub InstId);

impl OptInstId {
    pub fn raw(self) -> InstId {
        self.0
    }
}

pub struct EvmCompile {
    module: Module,
    opt_level: OptLevel,
    emit_symbol_table: bool,
    emit_observability: bool,
    optimized: bool,
}

impl EvmCompile {
    pub fn new(module: Module) -> Self {
        Self {
            module,
            opt_level: OptLevel::default(),
            emit_symbol_table: false,
            emit_observability: false,
            optimized: false,
        }
    }

    pub fn with_opt_level(mut self, level: OptLevel) -> Self {
        self.opt_level = level;
        self
    }

    pub fn with_observability(mut self, on: bool) -> Self {
        self.emit_observability = on;
        self
    }

    /// Include linker symbol tables in the compiled object artifacts.
    ///
    /// Symbol tables are diagnostic metadata only and do not affect emitted
    /// section bytes. They are omitted by default.
    pub fn with_symbol_table(mut self, on: bool) -> Self {
        self.emit_symbol_table = on;
        self
    }

    /// Run the optimization pipeline (idempotent) and return a reference to
    /// the optimized module for inspection or IR dumping.
    pub fn optimize(&mut self) -> &Module {
        if !self.optimized {
            match self.opt_level {
                OptLevel::O0 => {}
                OptLevel::O1 => Pipeline::speed().run(&mut self.module),
                OptLevel::Os => Pipeline::size().run(&mut self.module),
                OptLevel::O2 => Pipeline::speed().run(&mut self.module),
            }
            self.optimized = true;
        }
        &self.module
    }

    /// Stamp codegen-owned provenance after optimization. This is the sanctioned
    /// door and the easy path, but it does not revoke the module's interior
    /// mutability: `optimize()` still returns a `&Module` whose `pub func_store`
    /// can be mutated, so the door disincentivizes reaching around the stamping
    /// path, it does not close it. A read-only view return type is the real
    /// close, deferred to the next API window and tracked as the ModuleView
    /// follow-up so it does not calcify into a permanent excuse.
    pub fn stamp_post_opt_provenance(
        &mut self,
        func: FuncRef,
        inst: OptInstId,
        provenance: impl Into<String>,
    ) -> Result<(), String> {
        self.optimize();
        let inst = inst.raw();
        if !self.module.funcs().contains(&func) {
            return Err(format!("cannot stamp undefined function {func:?}"));
        }
        let valid = self
            .module
            .func_store
            .view(func, |function| function.dfg.has_inst(inst));
        if !valid {
            return Err(format!(
                "cannot stamp missing inst{} in function {func:?}",
                inst.0
            ));
        }
        self.module.func_store.modify(func, |function| {
            function.set_inst_provenance(inst, provenance.into());
        });
        Ok(())
    }

    /// Stamp post-optimization provenance across every function in one pass.
    ///
    /// The closure returns `Some(provenance)` to stamp a live instruction or
    /// `None` to leave it unstamped. Stamping many instructions this way runs
    /// one function-list scan instead of the per-call rescan that
    /// [`Self::stamp_post_opt_provenance`] pays.
    pub fn stamp_all_post_opt_provenance(
        &mut self,
        mut f: impl FnMut(FuncRef, OptInstId) -> Option<String>,
    ) {
        self.optimize();
        let funcs = self.module.funcs();
        for func in funcs {
            self.module.func_store.modify(func, |function| {
                let insts: Vec<_> = function.dfg.inst_ids().collect();
                for inst in insts {
                    if let Some(provenance) = f(func, OptInstId(inst)) {
                        function.set_inst_provenance(inst, provenance);
                    }
                }
            });
        }
    }

    /// Optimize (if not already) and compile every object in the module.
    pub fn compile(mut self) -> Result<Vec<ObjectArtifact>, Vec<ObjectCompileError>> {
        self.optimize();
        let backend = evm_backend_for_module(&self.module, self.opt_level)?;
        let opts = CompileOptions {
            emit_symtab: self.emit_symbol_table,
            emit_observability: self.emit_observability,
            ..CompileOptions::default()
        };
        compile_all_objects(&self.module, &backend, &opts)
    }
}

impl OptLevel {
    fn late_cleanup_profile(self) -> LateCleanupProfile {
        match self {
            OptLevel::O0 => LateCleanupProfile::Off,
            OptLevel::O1 => LateCleanupProfile::Speed,
            OptLevel::Os => LateCleanupProfile::Size,
            OptLevel::O2 => LateCleanupProfile::Speed,
        }
    }

    fn stackify_search_profile(self) -> StackifySearchProfile {
        match self {
            OptLevel::O0 => StackifySearchProfile::Fast,
            OptLevel::O1 => StackifySearchProfile::GreedyWide,
            OptLevel::Os | OptLevel::O2 => StackifySearchProfile::Exact,
        }
    }

    fn immediate_materialization_mode(self) -> ImmediateMaterializationMode {
        match self {
            OptLevel::Os => ImmediateMaterializationMode::Size,
            OptLevel::O2 => ImmediateMaterializationMode::Balanced,
            OptLevel::O0 | OptLevel::O1 => ImmediateMaterializationMode::Gas,
        }
    }
}

fn evm_backend_for_module(
    module: &Module,
    opt_level: OptLevel,
) -> Result<EvmBackend, Vec<ObjectCompileError>> {
    let target = module.ctx.triple;
    if target != evm_osaka_triple() {
        return Err(vec![ObjectCompileError::UnsupportedTarget {
            target,
            message: "EVM codegen currently requires evm-ethereum-osaka".to_string(),
        }]);
    }

    Ok(EvmBackend::new(Evm::new(target))
        .with_late_cleanup_profile(opt_level.late_cleanup_profile())
        .with_stackify_search_profile(opt_level.stackify_search_profile())
        .with_immediate_materialization_mode(opt_level.immediate_materialization_mode()))
}

fn evm_osaka_triple() -> TargetTriple {
    TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    )
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{InstId, Module, isa::evm::Evm, module::FuncRef};
    use sonatina_parser::parse_module;
    use sonatina_triple::{EvmVersion, OperatingSystem, TargetTriple};

    use super::{EvmCompile, ObjectCompileError, OptInstId, evm_osaka_triple};
    use crate::object::SymbolId;

    fn module_for_evm(version: EvmVersion) -> Module {
        let triple = evm_osaka_triple();
        Module::new(&Evm::new(TargetTriple {
            operating_system: OperatingSystem::Evm(version),
            ..triple
        }))
    }

    #[test]
    fn compile_uses_module_target() {
        let errors = EvmCompile::new(module_for_evm(EvmVersion::London))
            .compile()
            .expect_err("London modules should not be compiled as Osaka");
        let [ObjectCompileError::UnsupportedTarget { target, .. }] = errors.as_slice() else {
            panic!("expected unsupported target error, got {errors:?}");
        };
        assert_eq!(
            target.operating_system,
            OperatingSystem::Evm(EvmVersion::London)
        );
    }

    #[test]
    fn post_opt_provenance_stamping_is_metadata_only() {
        let mut compile = EvmCompile::new(module_for_evm(EvmVersion::Osaka));
        let error = compile
            .stamp_post_opt_provenance(FuncRef::from_u32(0), OptInstId(InstId(0)), "post-opt:test")
            .expect_err("undefined functions must be rejected");

        assert!(error.contains("undefined function"));
        assert_eq!(compile.optimize().ctx.triple, evm_osaka_triple());
    }

    #[test]
    fn symbol_table_option_populates_embed_symbols_without_changing_bytes() {
        let source = r#"
target = "evm-ethereum-osaka"

func public %runtime() {
    block0:
        evm_return 0.i256 0.i256;
}

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        mstore 0.i256 v0 i256;
        mstore 32.i256 v1 i256;
        evm_return 0.i256 64.i256;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
  }
}
"#;

        let compile = |emit_symbol_table| {
            EvmCompile::new(parse_module(source).expect("fixture parses").module)
                .with_symbol_table(emit_symbol_table)
                .with_observability(true)
                .compile()
                .expect("fixture compiles")
        };
        let without_symbols = compile(false);
        let with_symbols = compile(true);
        let without = &without_symbols[0];
        let with = &with_symbols[0];

        assert_eq!(without_symbols.len(), with_symbols.len());
        assert_eq!(without.sections.len(), with.sections.len());
        for ((without_name, without_section), (with_name, with_section)) in
            without.sections.iter().zip(with.sections.iter())
        {
            assert_eq!(without_name, with_name);
            assert_eq!(without_section.bytes, with_section.bytes);
            assert!(without_section.symtab.is_empty());
            assert!(with_section.observability.is_some());
        }
        let (_, init) = with
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "init")
            .expect("init section exists");
        assert!(
            init.symtab
                .keys()
                .any(|symbol| matches!(symbol, SymbolId::Embed(_))),
            "symbol table must contain the required runtime embed symbol"
        );
    }
}
