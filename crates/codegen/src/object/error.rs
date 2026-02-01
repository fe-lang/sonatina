use sonatina_ir::{
    GlobalVariableRef,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName, SectionRef},
};

#[derive(Debug, Clone)]
pub enum ObjectCompileError {
    ObjectNotFound {
        object: String,
    },

    DuplicateSectionName {
        object: ObjectName,
        section: SectionName,
    },
    MissingEntry {
        object: ObjectName,
        section: SectionName,
    },
    MultipleEntries {
        object: ObjectName,
        section: SectionName,
    },
    DuplicateEmbedSymbol {
        object: ObjectName,
        section: SectionName,
        symbol: EmbedSymbol,
    },

    InvalidFunctionRef {
        object: ObjectName,
        section: SectionName,
        func: FuncRef,
    },
    InvalidGlobalRef {
        object: ObjectName,
        section: SectionName,
        gv: GlobalVariableRef,
    },
    UndefinedSectionRef {
        object: ObjectName,
        section: SectionName,
        ref_: SectionRef,
    },

    EmbedCycle {
        cycle: Vec<(ObjectName, SectionName)>,
    },
    UndefinedEmbedSymbol {
        object: ObjectName,
        section: SectionName,
        symbol: EmbedSymbol,
    },

    InvalidGlobalForData {
        object: ObjectName,
        section: SectionName,
        gv: GlobalVariableRef,
        reason: String,
    },

    BackendError {
        object: ObjectName,
        section: SectionName,
        func: FuncRef,
        message: String,
    },

    LinkError {
        object: ObjectName,
        section: SectionName,
        message: String,
    },
}
