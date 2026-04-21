use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{BlockId, InstId, ValueId, module::FuncRef};

use crate::machinst::lower::SectionWorkModule;

pub(crate) struct MachineSectionModule {
    pub(crate) work: SectionWorkModule,
    pub(crate) source_to_machine: SourceMachineMap,
}

#[derive(Default)]
pub(crate) struct SourceMachineMap {
    pub(crate) funcs: FxHashMap<FuncRef, FuncMachineMap>,
}

pub(crate) struct FuncMachineMap {
    pub(crate) blocks: SecondaryMap<BlockId, Option<BlockId>>,
    pub(crate) values: SecondaryMap<ValueId, Option<ValueId>>,
    pub(crate) insts: SecondaryMap<InstId, Option<InstId>>,
}

impl FuncMachineMap {
    pub(crate) fn new() -> Self {
        Self {
            blocks: SecondaryMap::new(),
            values: SecondaryMap::new(),
            insts: SecondaryMap::new(),
        }
    }
}
