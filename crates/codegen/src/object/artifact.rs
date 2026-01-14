use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    GlobalVariableRef,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolId {
    Func(FuncRef),
    Global(GlobalVariableRef),
    Embed(EmbedSymbol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolDef {
    pub offset: u32,
    pub size: u32,
}

#[derive(Debug, Clone)]
pub struct SectionArtifact {
    pub bytes: Vec<u8>,
    pub symtab: FxHashMap<SymbolId, SymbolDef>,
}

#[derive(Debug, Clone)]
pub struct ObjectArtifact {
    pub object: ObjectName,
    pub sections: IndexMap<SectionName, SectionArtifact>,
}
