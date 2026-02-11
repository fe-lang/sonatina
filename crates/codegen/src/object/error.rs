use sonatina_ir::{
    GlobalVariableRef,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName},
};
use sonatina_verifier::VerificationReport;

#[derive(Debug, Clone)]
pub enum ObjectCompileError {
    ObjectNotFound {
        object: String,
    },

    VerifierFailed {
        report: VerificationReport,
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
