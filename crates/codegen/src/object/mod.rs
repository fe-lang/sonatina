pub mod artifact;
pub mod compile;
pub mod data;
pub mod error;
pub mod evm_backend;
pub mod link;
pub mod resolve;

pub use artifact::{ObjectArtifact, SectionArtifact, SymbolDef, SymbolId};
pub use compile::{compile_all_objects, compile_object};
pub use data::encode_gv_initializer_to_bytes;
pub use error::ObjectCompileError;
pub use evm_backend::EvmObjectBackend;
pub use link::{Atom, Fixup, FixupFormat, FixupKind};
pub use resolve::{
    ObjectId, ResolvedEmbed, ResolvedObject, ResolvedProgram, ResolvedSection, SectionId,
};

use sonatina_ir::{
    GlobalVariableRef, Module,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName},
};

#[derive(Debug, Clone)]
pub struct CompileOptions {
    pub push_width_policy: PushWidthPolicy,
    pub emit_symtab: bool,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            push_width_policy: PushWidthPolicy::Push4,
            emit_symtab: true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PushWidthPolicy {
    Push4,
    MinimalRelax,
}

pub struct SectionLoweringCtx<'a> {
    pub object: &'a ObjectName,
    pub section: &'a SectionName,
    pub embed_symbols: &'a [EmbedSymbol],
    pub push_width_policy: PushWidthPolicy,
}

#[derive(Debug, Clone)]
pub struct LoweredFunction {
    pub bytes: Vec<u8>,
    pub fixups: Vec<Fixup>,
}

pub trait EvmLoweringBackend {
    type Error: std::fmt::Display;

    fn lower_function(
        &self,
        module: &Module,
        func: FuncRef,
        section_ctx: &SectionLoweringCtx<'_>,
    ) -> Result<LoweredFunction, Self::Error>;

    fn compile_section(
        &self,
        module: &Module,
        funcs: &[FuncRef],
        data: &[(GlobalVariableRef, Vec<u8>)],
        embeds: &[(EmbedSymbol, Vec<u8>)],
        section_ctx: &SectionLoweringCtx<'_>,
        opts: &CompileOptions,
    ) -> Result<Option<SectionArtifact>, Self::Error> {
        let _ = (module, funcs, data, embeds, section_ctx, opts);
        Ok(None)
    }
}
