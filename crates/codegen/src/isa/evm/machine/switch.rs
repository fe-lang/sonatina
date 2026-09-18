use std::collections::BTreeSet;

use sonatina_ir::{
    BlockId, Function, InstId, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        cmp::Lt,
        control_flow::{Br, BrTable, BranchKind},
    },
    isa::{Isa, evm::EvmMachine},
};

use crate::cfg_edit::{copy_phi_incoming_block, remove_phi_incoming_from};

use super::super::immediate_materialization_cost_i256;

// An extra pivot comparison only reduces the average number of comparisons above four
// uniformly likely cases. Small leaves also avoid paying for extra branch destinations.
const LINEAR_LEAF_SIZE: usize = 4;

/// Expand switches before stack allocation: BrTable's allocator and emitter jointly
/// implement a linear chain, so a tree must have explicit CFG edges at this boundary.
pub(crate) fn lower_switches(func: &mut Function) {
    let switches: Vec<_> = func
        .layout
        .iter_block()
        .filter_map(|block| {
            let term = func.layout.last_inst_of(block)?;
            let BranchKind::BrTable(table) = func.dfg.branch_info(term)?.branch_kind() else {
                return None;
            };
            let default = (*table.default())?;
            if table.table().len() <= LINEAR_LEAF_SIZE {
                return None;
            }
            let mut cases = table
                .table()
                .iter()
                .map(|&(value, dest)| {
                    let key = func.dfg.value_imm(value)?.as_i256().to_u256();
                    Some((key, value, dest))
                })
                .collect::<Option<Vec<_>>>()?;
            // Machine values have already been normalized to words. Signed ordering
            // would disagree with the unsigned LT used to partition those words.
            cases.sort_unstable_by_key(|&(key, ..)| key);
            let cases: Vec<_> = cases
                .into_iter()
                .map(|(_, value, dest)| (value, dest))
                .collect();
            split_index(func, &cases)?;
            Some((term, *table.scrutinee(), default, cases))
        })
        .collect();

    for (term, scrutinee, default, cases) in switches {
        let root = func.layout.inst_block(term);
        let destinations: BTreeSet<_> = cases
            .iter()
            .map(|&(_, dest)| dest)
            .chain([default])
            .collect();
        func.layout.remove_inst(term);
        SwitchTree {
            func,
            term,
            root,
            scrutinee,
            default,
        }
        .emit(root, &cases);
        // Every old edge is now owned by a leaf. Copy its phi input once per leaf
        // predecessor, including shared/default targets and edges back to the root.
        for dest in destinations {
            remove_phi_incoming_from(func, dest, root);
        }
        func.erase_inst(term);
    }
}

fn split_index(func: &Function, cases: &[(ValueId, BlockId)]) -> Option<usize> {
    if cases.len() <= LINEAR_LEAF_SIZE {
        return None;
    }
    // DUP, EQ/LT, destination PUSH, and JUMPI cost 19 gas, in addition to
    // materializing the key. A split also adds a JUMPDEST on the selected path.
    // With equally likely keys, upper-half hits save all lower-half comparisons.
    let comparison_cost = |value| {
        let imm = func.dfg.value_imm(value).expect("constant switch key");
        u128::from(immediate_materialization_cost_i256(imm.as_i256()).gas) + 19
    };
    let mid = cases.len() / 2;
    let saved = cases[..mid]
        .iter()
        .map(|&(value, _)| comparison_cost(value))
        .sum::<u128>()
        * (cases.len() - mid) as u128;
    let added = (comparison_cost(cases[mid].0) + 1) * cases.len() as u128;
    (saved > added).then_some(mid)
}

struct SwitchTree<'a> {
    func: &'a mut Function,
    term: InstId,
    root: BlockId,
    scrutinee: ValueId,
    default: BlockId,
}

impl SwitchTree<'_> {
    fn emit(&mut self, block: BlockId, cases: &[(ValueId, BlockId)]) {
        let machine = EvmMachine::new(self.func.ctx().triple);
        let is = machine.inst_set();
        let mut cursor = InstInserter::at_location(CursorLocation::BlockBottom(block));
        let Some(mid) = split_index(self.func, cases) else {
            cursor.insert_inst_data_from(
                self.func,
                self.term,
                BrTable::new(is, self.scrutinee, Some(self.default), cases.to_vec()),
            );
            let destinations: BTreeSet<_> = cases
                .iter()
                .map(|&(_, dest)| dest)
                .chain([self.default])
                .collect();
            for dest in destinations {
                copy_phi_incoming_block(self.func, dest, self.root, block);
            }
            return;
        };

        let (lower, upper) = cases.split_at(mid);
        let upper_block = self.func.dfg.make_block();
        let lower_block = self.func.dfg.make_block();
        self.func.layout.insert_block_after(upper_block, block);
        self.func
            .layout
            .insert_block_after(lower_block, upper_block);
        let cmp = cursor.insert_inst_data_from(
            self.func,
            self.term,
            Lt::new(is, self.scrutinee, upper[0].0),
        );
        let cond = cursor.make_result(self.func, cmp, Type::I256);
        self.func.dfg.append_result(cmp, cond);
        cursor.insert_inst_data_from(
            self.func,
            self.term,
            Br::new(is, cond, lower_block, upper_block),
        );
        self.emit(upper_block, upper);
        self.emit(lower_block, lower);
    }
}
