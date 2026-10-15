use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{BlockId, InstId, Module, ValueId, module::FuncRef};

use crate::machinst::lower::SectionWorkModule;

pub(crate) struct MachineSectionModule {
    pub(crate) work: SectionWorkModule,
    pub(crate) source_to_machine: SourceMachineMap,
}

#[derive(Default)]
pub(crate) struct SourceMachineMap {
    pub(crate) funcs: FxHashMap<FuncRef, FuncMachineMap>,
}

impl SourceMachineMap {
    /// Forgets what the machine pipeline removed: GVN and SCCP delete a value
    /// after moving its users to an equal one, ADCE deletes unused values and
    /// instructions, and CFG cleanup removes blocks.
    pub(crate) fn retain_live(&mut self, module: &Module) {
        for (&func, map) in &mut self.funcs {
            module.func_store.view(func, |machine| {
                for value in map.values.values_mut() {
                    if value.is_some_and(|value| !machine.dfg.has_value(value)) {
                        *value = None;
                    }
                }
                for inst in map.insts.values_mut() {
                    if inst.is_some_and(|inst| !machine.layout.is_inst_inserted(inst)) {
                        *inst = None;
                    }
                }
                for block in map.blocks.values_mut() {
                    if block.is_some_and(|block| !machine.layout.is_block_inserted(block)) {
                        *block = None;
                    }
                }
            });
        }
    }
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
