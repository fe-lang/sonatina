//! Recognize the u256 MSB search that tries shifts 128, 64, ..., 1.
//! Each successful shift contributes its distance to the u8 index. Each bit
//! is added at most once, so the checked sum cannot exceed 255.
use sonatina_ir::{
    BlockId, Function, I256, Immediate, Inst, InstId, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        arith::{Shr, Uaddo},
        cast::Trunc,
        cmp::IsZero,
        control_flow::Br,
        logic::{Clz, Or, Xor},
    },
};
use sonatina_triple::{EvmVersion, OperatingSystem};

use crate::cfg_edit::CfgEditor;

pub(super) fn run(func: &mut Function) -> bool {
    if func.ctx().triple.operating_system != OperatingSystem::Evm(EvmVersion::Osaka) {
        return false;
    }
    // Only build a CFG when a checked byte addition could be the update step.
    let updates: Vec<_> = func
        .layout
        .iter_block()
        .filter(|&b| {
            let Some(term) = func.layout.last_inst_of(b) else {
                return false;
            };
            let Some(br) = func.dfg.downcast::<&Br>(term) else {
                return false;
            };
            let Some((add, 1)) = func.dfg.value_inst_result(*br.cond()) else {
                return false;
            };
            func.dfg
                .downcast::<&Uaddo>(add)
                .is_some_and(|op| func.dfg.value_ty(*op.lhs()) == Type::I8)
        })
        .collect();
    if updates.is_empty() {
        return false;
    }
    let mut edit = CfgEditor::new(func);
    let mut changed = false;
    for update in updates {
        if let Some(scan) = recognize(&edit, update) {
            scan.replace(&mut edit);
            changed = true;
        }
    }
    changed
}

struct Scan {
    header: BlockId,
    latch: BlockId,
    input: ValueId,
    index: ValueId,
    shifted: InstId,
}

// Both incoming edges and values matter: in particular the unchecked path
// keeps the current word and index, while the update path advances both.
fn incoming(func: &Function, phi: ValueId, from: BlockId) -> Option<ValueId> {
    func.dfg
        .cast_phi(func.dfg.value_inst(phi)?)?
        .args()
        .iter()
        .find_map(|&(value, pred)| (pred == from).then_some(value))
}

fn block_insts<const N: usize>(func: &Function, b: BlockId) -> Option<[InstId; N]> {
    let mut iter = func.layout.iter_inst(b);
    let insts = std::array::from_fn(|_| iter.next());
    if iter.next().is_some() || insts.contains(&None) {
        return None;
    }
    Some(insts.map(Option::unwrap))
}

fn recognize(edit: &CfgEditor<'_>, update: BlockId) -> Option<Scan> {
    let f = edit.func();
    let cfg = edit.cfg();
    let &[header] = cfg.preds_as_slice(update) else {
        return None;
    };
    let [trunc, add, update_term] = block_insts(f, update)?;
    let update_br = f.dfg.downcast::<&Br>(update_term)?;
    let &[sum, overflow] = f.dfg.inst_results(add) else {
        return None;
    };
    let add_op = f.dfg.downcast::<&Uaddo>(add)?;
    let latch = *update_br.z_dest();
    let [phi_a, phi_b, phi_c, shifted, check, header_term] = block_insts(f, header)?;
    let shift = f.dfg.downcast::<&Shr>(shifted)?;
    let (distance, word) = (*shift.bits(), *shift.value());
    let header_br = f.dfg.downcast::<&Br>(header_term)?;
    if *header_br.nz_dest() != latch
        || *header_br.z_dest() != update
        || *f.dfg.downcast::<&IsZero>(check)?.lhs() != f.dfg.inst_result(shifted)?
        || *header_br.cond() != f.dfg.inst_result(check)?
        || *update_br.cond() != overflow
        || [header, update, latch].contains(update_br.nz_dest())
    {
        return None;
    }
    let narrow = f.dfg.downcast::<&Trunc>(trunc)?;
    if *narrow.from() != distance || *narrow.ty() != Type::I8 {
        return None;
    }
    let byte = f.dfg.inst_result(trunc)?;
    let acc = if *add_op.rhs() == byte {
        *add_op.lhs()
    } else if *add_op.lhs() == byte {
        *add_op.rhs()
    } else {
        return None;
    };

    let [phi_x, phi_y, half, done, latch_term] = block_insts(f, latch)?;
    let half_op = f.dfg.downcast::<&Shr>(half)?;
    let latch_br = f.dfg.downcast::<&Br>(latch_term)?;
    let half_value = f.dfg.inst_result(half)?;
    if !f.dfg.value_imm(*half_op.bits())?.is_one()
        || *half_op.value() != distance
        || *f.dfg.downcast::<&IsZero>(done)?.lhs() != half_value
        || *latch_br.cond() != f.dfg.inst_result(done)?
        || *latch_br.z_dest() != header
        || [header, update, latch].contains(latch_br.nz_dest())
    {
        return None;
    }

    let entry = *cfg.preds_of(header).find(|&&p| p != latch)?;
    let input = incoming(f, word, entry)?;
    let index = incoming(f, acc, latch)?;
    let next_word = incoming(f, word, latch)?;
    // Match every instruction in all three blocks, including the merge phis.
    // This rules out side effects and unrelated loop-carried state.
    let header_phis = [acc, word, distance].map(|v| f.dfg.value_inst(v));
    let latch_phis = [index, next_word].map(|v| f.dfg.value_inst(v));
    if cfg.pred_num_of(header) != 2
        || cfg.pred_num_of(latch) != 2
        || ![phi_a, phi_b, phi_c]
            .into_iter()
            .all(|phi| header_phis.contains(&Some(phi)))
        || ![phi_x, phi_y]
            .into_iter()
            .all(|phi| latch_phis.contains(&Some(phi)))
        || f.dfg.value_ty(word) != Type::I256
        || f.dfg.value_ty(acc) != Type::I8
        || f.dfg.value_imm(incoming(f, distance, entry)?)
            != Some(Immediate::I256(I256::from(128u64)))
        || !f.dfg.value_imm(incoming(f, acc, entry)?)?.is_zero()
        || incoming(f, distance, latch)? != half_value
        || incoming(f, index, header)? != acc
        || incoming(f, index, update)? != sum
        || incoming(f, next_word, header)? != word
        || incoming(f, next_word, update)? != f.dfg.inst_result(shifted)?
    {
        return None;
    }
    let region = [header, update, latch];
    for b in region {
        for i in f.layout.iter_inst(b) {
            for &v in f.dfg.inst_results(i) {
                if v != index
                    && f.dfg.users(v).any(|&u| {
                        !f.layout.is_inst_inserted(u) || !region.contains(&f.layout.inst_block(u))
                    })
                {
                    return None;
                }
            }
        }
    }
    Some(Scan {
        header,
        latch,
        input,
        index,
        shifted,
    })
}

impl Scan {
    fn replace(self, editor: &mut CfgEditor<'_>) {
        let f = editor.func_mut();
        let is = f.inst_set();
        let mask = f.dfg.make_imm_value(I256::from(255u64));
        let one = f.dfg.make_imm_value(I256::from(1u64));
        let mut cursor = InstInserter::at_location(CursorLocation::At(self.shifted));
        let mut emit = |inst: Box<dyn Inst>, ty| {
            let id = cursor.insert_inst_data_dyn_from(f, self.shifted, inst);
            let value = cursor.make_result(f, id, ty);
            f.dfg.attach_result(id, value);
            cursor.set_location(CursorLocation::At(id));
            value
        };
        // Setting bit zero preserves every nonzero MSB and gives zero the
        // index 0, exactly as the unguarded search does.
        let word = emit(
            Box::new(Or::new(is.has_or().unwrap(), self.input, one)),
            Type::I256,
        );
        let leading = emit(Box::new(Clz::new(is.has_clz().unwrap(), word)), Type::I256);
        // clz(nonzero) is in 0..=255, so XOR with 255 computes 255 - clz.
        let index = emit(
            Box::new(Xor::new(is.has_xor().unwrap(), leading, mask)),
            Type::I256,
        );
        let result = emit(
            Box::new(Trunc::new(is.has_trunc().unwrap(), index, Type::I8)),
            Type::I8,
        );
        f.dfg.change_to_alias(self.index, result);
        // Take the no-update edge and then the exit. CFG cleanup removes the
        // dead update and the unused phis; the original exit retains its edge.
        editor.retain_out_edges(self.header, &[true, false]);
        editor.retain_out_edges(self.latch, &[true, false]);
    }
}

#[cfg(test)]
mod tests {
    use super::run;
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;

    const SEARCH: &str = include_str!("../../test_files/evm/msb_search.sntn");

    fn check(source: &str, expected: bool) {
        let module = parse_module(source).unwrap().module;
        let id = module.funcs()[0];
        module.func_store.modify(id, |func| {
            assert_eq!(run(func), expected, "{source}");
            assert_eq!(
                FuncWriter::new(id, func).dump_string().contains(" = clz "),
                expected
            );
        });
    }

    #[test]
    fn recognizes_search_with_or_without_zero_guard() {
        check(SEARCH, true);
        check(
            &SEARCH.replace("jump block1;", "v1.i1 = is_zero v0;\n br v1 block6 block1;"),
            true,
        );
    }

    #[test]
    fn preserves_other_loop_semantics() {
        for (from, to) in [
            ("128.i256 block0", "64.i256 block0"),
            ("0.i8 block0", "1.i8 block0"),
            ("shr 1.i256 v2", "shr 2.i256 v2"),
            ("uaddo v4 v7", "uaddo v7 v7"),
            ("(v3 block1) (v5 block2)", "(v5 block1) (v3 block2)"),
            ("v7.i8 = trunc", "mstore 0.i256 v3 i256;\n v7.i8 = trunc"),
            ("return v9;", "v14.i8 = trunc v10 i8;\n return v14;"),
        ] {
            assert!(SEARCH.contains(from));
            check(&SEARCH.replace(from, to), false);
        }
    }

    #[test]
    fn rejects_unreachable_cycle_entered_from_update() {
        // block2's overflow edge re-enters block1, which is otherwise
        // unreachable, so block2 must not be taken as the loop entry.
        let source = [
            ("jump block1;", "return 0.i8;"),
            ("128.i256 block0", "128.i256 block2"),
            ("(v0 block0)", "(v0 block2)"),
            ("0.i8 block0", "0.i8 block2"),
            ("br v13 block6 block3;", "br v13 block1 block3;"),
        ]
        .into_iter()
        .fold(SEARCH.to_string(), |source, (from, to)| {
            assert!(source.contains(from));
            source.replace(from, to)
        });
        check(&source, false);
    }
}
