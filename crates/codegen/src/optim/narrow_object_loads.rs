//! Load narrowing: an `obj.load` of a struct or array whose result is read
//! only by `extract_value`s of constant indices becomes loads of those fields,
//! where the whole load was.
//!
//! A native backend keeps a loaded aggregate that lives across a call or a
//! store in a stack slot, which copies every field, though the code may read
//! one or two of them: settling a journal reads an entry's kind and address.
//! The field loads read the same memory at the same point, so they see what
//! the whole load saw. A field that is itself an aggregate narrows in turn.

use smallvec::smallvec;
use sonatina_ir::{
    Function, I256, Immediate, InstId, Type, Value, ValueId,
    inst::data::{ExtractValue, ObjIndex, ObjLoad, ObjProj},
    types::CompoundType,
};

#[derive(Default)]
pub struct NarrowObjectLoads;

impl NarrowObjectLoads {
    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut changed = false;
        loop {
            let loads: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| narrowable(func, inst))
                .collect();
            if loads.is_empty() {
                return changed;
            }
            for (load, extracts) in loads {
                narrow(func, load, extracts);
            }
            changed = true;
        }
    }
}

/// A load to narrow and its `extract_value` users with their field indices.
type Extracts = Vec<(InstId, u32)>;

fn narrowable(func: &Function, inst: InstId) -> Option<(InstId, Extracts)> {
    func.dfg.downcast::<&ObjLoad>(inst)?;
    let result = func.dfg.inst_result(inst)?;
    match func.dfg.value_ty(result).resolve_compound(func.ctx()) {
        Some(CompoundType::Struct(data)) if !data.packed => {}
        Some(CompoundType::Array { .. }) => {}
        _ => return None,
    }
    let extracts = func
        .dfg
        .users(result)
        .filter(|&&user| func.layout.is_inst_inserted(user))
        .map(|&user| {
            let extract = func.dfg.downcast::<&ExtractValue>(user)?;
            let idx = func
                .dfg
                .value_imm(*extract.idx())?
                .as_i256()
                .to_u256()
                .low_u32();
            (*extract.dest() == result).then_some((user, idx))
        })
        .collect::<Option<Extracts>>()?;
    (!extracts.is_empty()).then_some((inst, extracts))
}

fn narrow(func: &mut Function, load: InstId, mut extracts: Extracts) {
    let is = func.inst_set();
    let object = *func.dfg.downcast::<&ObjLoad>(load).unwrap().object();
    let ty = func.dfg.value_ty(func.dfg.inst_result(load).unwrap());
    let compound = ty.resolve_compound(func.ctx());
    extracts.sort_unstable_by_key(|&(_, idx)| idx);
    let mut after = load;
    let mut field = None;
    for (extract, idx) in extracts {
        let value = match field {
            Some((loaded, value)) if loaded == idx => value,
            _ => {
                let idx_value = func
                    .dfg
                    .make_imm_value(Immediate::from_i256(I256::from(idx), Type::I256));
                let (elem_ty, proj) = match &compound {
                    Some(CompoundType::Struct(data)) => (
                        data.fields[idx as usize],
                        func.dfg.make_inst_dyn(Box::new(ObjProj::new_unchecked(
                            is,
                            smallvec![object, idx_value],
                        ))),
                    ),
                    Some(CompoundType::Array { elem, .. }) => (
                        *elem,
                        func.dfg.make_inst_dyn(Box::new(ObjIndex::new_unchecked(
                            is, object, idx_value,
                        ))),
                    ),
                    other => unreachable!("narrowed a load of {other:?}"),
                };
                let ref_ty = func
                    .ctx()
                    .with_ty_store_mut(|store| store.make_obj_ref(elem_ty));
                let proj_value = attach(func, proj, load, after, ref_ty);
                let field_load = func
                    .dfg
                    .make_inst_dyn(Box::new(ObjLoad::new_unchecked(is, proj_value)));
                let value = attach(func, field_load, load, proj, elem_ty);
                after = field_load;
                field = Some((idx, value));
                value
            }
        };
        let result = func.dfg.inst_result(extract).unwrap();
        func.dfg.change_to_alias(result, value);
        func.layout.remove_inst(extract);
        func.erase_inst(extract);
    }
    func.layout.remove_inst(load);
    func.erase_inst(load);
}

/// Inserts `inst` after `after`, attributed to `source`, with one result of `ty`.
fn attach(func: &mut Function, inst: InstId, source: InstId, after: InstId, ty: Type) -> ValueId {
    func.layout.insert_inst_after(inst, after);
    func.propagate_inst_attribution(inst, source);
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    func.dfg.attach_results(inst, &[value]);
    value
}
