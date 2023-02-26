use cranelift_entity::EntityRef;
use ir::InsnData;
use sonatina_ir as ir;

pub trait Function {
    type ValueType: EntityRef;

    // fn num_insts(&self) -> usize;
    // fn num_blocks(&self) -> usize;
    // fn entry_block(&self) -> ir::Block;

    fn for_each_use(&self, block: ir::Block, f: impl FnMut(Self::ValueType, Option<ir::Block>));
    fn for_each_def(&self, block: ir::Block, f: impl FnMut(Self::ValueType, bool));
}

impl Function for ir::Function {
    type ValueType = ir::Value;

    fn for_each_use(&self, block: ir::Block, mut f: impl FnMut(ir::Value, Option<ir::Block>)) {
        for insn in self.layout.iter_insn(block) {
            match self.dfg.insn_data(insn) {
                InsnData::Phi { values, blocks, .. } => values
                    .iter()
                    .zip(blocks.iter())
                    .for_each(|(v, b)| f(*v, Some(*b))),
                data => data.args().iter().for_each(|v| f(*v, None)),
            }
        }
    }

    fn for_each_def(&self, block: ir::Block, mut f: impl FnMut(ir::Value, bool)) {
        for insn in self.layout.iter_insn(block) {
            if let Some(val) = self.dfg.insn_result(insn) {
                f(val, self.dfg.is_phi(insn))
            }
        }
    }
}
