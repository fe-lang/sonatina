use smallvec::SmallVec;
use sonatina_ir::{BlockId, ValueId};

use super::sym_stack::SymStack;

pub(super) struct BrTableCaseStack {
    pub(super) dest: BlockId,
    pub(super) post_compare_stack: SymStack,
}

pub(super) fn plan_br_table_compare_chain(
    table: &[(ValueId, BlockId)],
    base_stack: &SymStack,
    mut prepare_case: impl FnMut(usize, ValueId, &mut SymStack),
) -> (SmallVec<[BrTableCaseStack; 8]>, SymStack) {
    let mut running_stack = base_stack.clone();
    let mut case_stacks = SmallVec::with_capacity(table.len());

    for (case_idx, &(case_val, dest)) in table.iter().enumerate() {
        let mut case_stack = running_stack.clone();
        prepare_case(case_idx, case_val, &mut case_stack);

        // `br_table` lowering emits `EQ; JUMPI` for each case in order. The non-taken path keeps
        // the stack left after consuming the two compare operands; later cases must plan from that
        // running stack, not from the original terminator-entry stack.
        case_stack.pop_n_operands(2);
        running_stack = case_stack.clone();
        case_stacks.push(BrTableCaseStack {
            dest,
            post_compare_stack: case_stack,
        });
    }

    (case_stacks, running_stack)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stackalloc::{Actions, stackify::sym_stack::StackItem};

    fn stack_values(stack: &SymStack) -> Vec<ValueId> {
        stack
            .iter()
            .map(|item| match item {
                StackItem::Value(value) => *value,
                StackItem::FuncRetAddr | StackItem::CallRetAddr => {
                    panic!("test stack should not contain return markers")
                }
            })
            .collect()
    }

    #[test]
    fn later_br_table_cases_start_from_previous_post_compare_stack() {
        let mut base_stack = SymStack::opaque_prefix_empty(false);
        for value in [
            ValueId::from_u32(4),
            ValueId::from_u32(3),
            ValueId::from_u32(2),
            ValueId::from_u32(1),
        ] {
            base_stack.push_value(value);
        }

        let table = [
            (ValueId::from_u32(10), BlockId::from_u32(1)),
            (ValueId::from_u32(11), BlockId::from_u32(2)),
        ];
        let mut seen_entries = Vec::new();

        let (case_stacks, default_stack) =
            plan_br_table_compare_chain(&table, &base_stack, |case_idx, _, case_stack| {
                seen_entries.push(stack_values(case_stack));
                let mut actions = Actions::new();
                if case_idx == 0 {
                    case_stack.swap(2, &mut actions);
                }
            });

        assert_eq!(
            seen_entries,
            vec![
                vec![
                    ValueId::from_u32(1),
                    ValueId::from_u32(2),
                    ValueId::from_u32(3),
                    ValueId::from_u32(4),
                ],
                vec![ValueId::from_u32(1), ValueId::from_u32(4)],
            ],
        );
        assert_eq!(
            stack_values(&case_stacks[0].post_compare_stack),
            vec![ValueId::from_u32(1), ValueId::from_u32(4)],
        );
        assert_eq!(
            stack_values(&case_stacks[1].post_compare_stack),
            Vec::<ValueId>::new()
        );
        assert_eq!(stack_values(&default_stack), Vec::<ValueId>::new());
    }
}
