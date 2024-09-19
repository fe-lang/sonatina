pub mod builder;
pub mod cfg;
pub mod dfg;
//pub mod dfg_;
pub mod func_cursor;
pub mod function;
// pub mod function_;
pub mod global_variable;
pub mod graphviz;
// pub mod insn;
pub mod inst;
pub mod ir_writer;
pub mod isa;
pub mod layout;
pub mod linkage;
pub mod module;
pub mod types;
pub mod value;
//pub mod value_;

mod bigint;

pub use bigint::{I256, U256};
pub use builder::Variable;
pub use cfg::ControlFlowGraph;
pub use dfg::{Block, BlockId, DataFlowGraph};
pub use function::{Function, Signature};
pub use global_variable::{GlobalVariable, GlobalVariableData};
pub use graphviz::render_to;
pub use inst::{
    inst_set::{InstSetBase, InstSetExt},
    HasInst, Inst, InstDowncast, InstDowncastMut, InstId,
};
pub use layout::Layout;
pub use linkage::Linkage;
pub use module::Module;
pub use types::Type;
pub use value::{Immediate, Value, ValueId};

pub(crate) use inst::ValueVisitable;

pub mod prelude {
    pub use crate::inst::{
        inst_set::{InstSetBase, InstSetExt},
        HasInst, Inst, InstDowncast, InstDowncastMut,
    };
}
