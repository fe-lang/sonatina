//! Fresh aggregates are spelled `agg.make`. An `insert_value` with a constant
//! index into `undef` or into an `agg.make` builds one too, and folds into an
//! `agg.make`: the base's operands, or `undef` per field, with the inserted
//! fields replaced. Fields are independent (`docs/undef.md`), so both spell the
//! same value. A whole chain of such inserts folds at once, from its last
//! insert, so a long chain costs one pass over it.

use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Module, Type, Value, ValueId,
    inst::data::{AggMake, InsertValue},
};

use super::shape;

/// The most fields that no insert of a chain on undef writes for it to fold:
/// a sparse insert into a long array keeps its spelling rather than becoming an
/// `agg.make` of mostly `undef` operands.
pub const MAX_UNWRITTEN_FIELDS: usize = 1024;

/// A chain of constant-index inserts that ends at an insert and starts at
/// `undef` or an `agg.make`.
struct Chain {
    ty: Type,
    fields: usize,
    /// The `agg.make` the chain starts at, or `None` for `undef`.
    base: Option<InstId>,
    /// The inserts from the last back, with the field and value each writes.
    inserts: SmallVec<[(InstId, usize, ValueId); 4]>,
}

impl Chain {
    fn of(func: &Function, last: InstId) -> Option<Self> {
        let ty = func
            .dfg
            .value_ty(*func.dfg.downcast::<&InsertValue>(last)?.dest());
        let fields = shape::aggregate_child_count(func.ctx(), ty)?;
        let mut inserts = SmallVec::new();
        let mut inst = last;
        loop {
            let insert = func.dfg.downcast::<&InsertValue>(inst)?;
            let field = shape::const_u32(&func.dfg, *insert.idx())? as usize;
            if field >= fields {
                return None;
            }
            inserts.push((inst, field, *insert.value()));
            let dest = *insert.dest();
            if matches!(func.dfg.value(dest), Value::Undef { .. }) {
                break;
            }
            let def = func.dfg.value_inst(dest)?;
            if func.dfg.downcast::<&AggMake>(def).is_some() {
                return Some(Self {
                    ty,
                    fields,
                    base: Some(def),
                    inserts,
                });
            }
            inst = def;
        }
        // From `undef`, every field no insert writes becomes an operand.
        if fields > MAX_UNWRITTEN_FIELDS + inserts.len() {
            return None;
        }
        let mut written = vec![false; fields];
        for &(_, field, _) in &inserts {
            written[field] = true;
        }
        let unwritten = written.iter().filter(|&&written| !written).count();
        (unwritten <= MAX_UNWRITTEN_FIELDS).then_some(Self {
            ty,
            fields,
            base: None,
            inserts,
        })
    }

    /// The chain's instructions from its last insert back, its `agg.make`
    /// base included.
    fn insts(&self) -> impl Iterator<Item = InstId> + '_ {
        self.inserts.iter().map(|&(inst, ..)| inst).chain(self.base)
    }
}

/// Whether `inst` is a constant-index `insert_value` into `undef` or an
/// `agg.make`, directly or through more such inserts: what
/// [`fold_fresh_aggregates`] leaves none of.
pub fn is_fresh_insert(func: &Function, inst: InstId) -> bool {
    Chain::of(func, inst).is_some()
}

/// Whether `inst` is the last insert of a chain that folds: a fresh insert
/// whose result something other than a further constant-index insert uses.
pub(crate) fn is_fresh_chain_end(func: &Function, inst: InstId) -> bool {
    let Some(result) = func
        .dfg
        .downcast::<&InsertValue>(inst)
        .and_then(|_| func.dfg.inst_result(inst))
    else {
        return false;
    };
    // Checked before walking the chain, so a long chain is walked once, and
    // the inserts a fold leaves unused do not fold again.
    let ends = func.dfg.users(result).any(|&user| {
        !func
            .dfg
            .downcast::<&InsertValue>(user)
            .is_some_and(|insert| {
                *insert.dest() == result && shape::const_u32(&func.dfg, *insert.idx()).is_some()
            })
    });
    ends && is_fresh_insert(func, inst)
}

/// Folds the chain that ends at the insert `last` into one `agg.make` in its
/// place, and returns the chain's other instructions, its base included, which
/// may be dead now. Does nothing, and returns `None`, unless `last` is a fresh
/// insert.
pub(crate) fn fold_fresh_insert(func: &mut Function, last: InstId) -> Option<Vec<InstId>> {
    let chain = Chain::of(func, last)?;
    let mut values: SmallVec<[ValueId; 4]> = match chain.base {
        Some(base) => func
            .dfg
            .downcast::<&AggMake>(base)
            .expect("the chain starts at an agg.make")
            .values()
            .clone(),
        None => (0..chain.fields)
            .map(|field| {
                let ty = shape::aggregate_child_ty(func.ctx(), chain.ty, field as u32)
                    .expect("a field of the chain's type");
                func.dfg.make_undef_value(ty)
            })
            .collect(),
    };
    for &(_, field, value) in chain.inserts.iter().rev() {
        values[field] = value;
    }
    let make = AggMake::new_unchecked(func.inst_set(), chain.ty, values);
    func.dfg.replace_inst(last, Box::new(make));
    Some(chain.insts().skip(1).collect())
}

/// Folds every fresh insert chain of `func`, and removes the instructions of
/// each that nothing uses any more. A chain whose result nothing uses goes
/// whole.
pub(crate) fn fold_fresh_aggregates_in(func: &mut Function) -> bool {
    let insts: Vec<InstId> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .collect();
    let mut changed = false;
    // From the last instruction back, so a chain folds at its end before its
    // other inserts are reached.
    for inst in insts.into_iter().rev() {
        if !func.layout.is_inst_inserted(inst) {
            continue;
        }
        let unused = func.dfg.downcast::<&InsertValue>(inst).is_some()
            && func
                .dfg
                .inst_result(inst)
                .is_some_and(|result| func.dfg.users_num(result) == 0);
        let dead = if unused {
            Chain::of(func, inst).map(|chain| chain.insts().collect())
        } else if is_fresh_chain_end(func, inst) {
            fold_fresh_insert(func, inst)
        } else {
            None
        };
        let Some(dead) = dead else {
            continue;
        };
        changed = true;
        // From the last insert back: each goes once the one after it has.
        for inst in dead {
            if func
                .dfg
                .inst_result(inst)
                .is_some_and(|result| func.dfg.users_num(result) > 0)
            {
                break;
            }
            func.layout.remove_inst(inst);
            func.erase_inst(inst);
        }
    }
    changed
}

/// Folds the fresh insert chains of every function in `module` into
/// `agg.make`s. `Compile::optimize` runs it before the pipeline, so passes see
/// fresh aggregates spelled one way. Passes may make new ones by substituting
/// `undef` or an `agg.make` for an insert's base; `concretize` folds those at
/// the end. Afterwards no constant-index `insert_value` has an `undef` or
/// `agg.make` base, except a sparse one into an aggregate with more than
/// [`MAX_UNWRITTEN_FIELDS`] fields it does not write ([`is_fresh_insert`]).
pub fn fold_fresh_aggregates(module: &Module) {
    for func in module.funcs() {
        module.func_store.modify(func, |function| {
            fold_fresh_aggregates_in(function);
        });
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::{MAX_UNWRITTEN_FIELDS, fold_fresh_aggregates_in};

    /// Folds the one function of `body`, checks the result verifies, and
    /// returns whether anything changed and the function's text.
    fn fold(body: &str) -> (bool, String) {
        let source = format!(
            "target = \"evm-ethereum-osaka\"
type @pair = {{ i64, i64 }};
type @flag = enum {{ #A, #B(i64) }};
type @kinds = {{ @flag, unit, [i8; 0], @pair, [i64; 2] }};
{body}"
        );
        let module = parse_module(&source).unwrap().module;
        let func = module.funcs()[0];
        let changed = module.func_store.modify(func, fold_fresh_aggregates_in);
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        let text = module.func_store.view(func, |function| {
            FuncWriter::new(func, function).dump_string()
        });
        (changed, text)
    }

    #[test]
    fn a_chain_on_undef_becomes_one_agg_make() {
        // The last insert of a field wins.
        let (changed, text) = fold(
            "func public %f(v0.i64, v1.i64) -> [i64; 3] {
block0:
    v2.[i64; 3] = insert_value undef.[i64; 3] 0.i8 v0;
    v3.[i64; 3] = insert_value v2 2.i8 v1;
    v4.[i64; 3] = insert_value v3 0.i8 v1;
    return v4;
}",
        );
        assert!(changed);
        assert!(
            text.contains("v4.[i64; 3] = agg.make [i64; 3] v1 undef.i64 v1;"),
            "{text}"
        );
        assert!(!text.contains("insert_value"), "{text}");
    }

    #[test]
    fn an_insert_into_an_agg_make_replaces_its_operand() {
        // `v2` is read too, so it stays.
        let (changed, text) = fold(
            "func public %f(v0.i64, v1.i64) -> i64 {
block0:
    v2.@pair = agg.make @pair v0 v0;
    v3.@pair = insert_value v2 1.i8 v1;
    v4.i64 = extract_value v2 0.i8;
    v5.i64 = extract_value v3 1.i8;
    v6.i64 = add v4 v5;
    return v6;
}",
        );
        assert!(changed);
        assert!(text.contains("v2.@pair = agg.make @pair v0 v0;"), "{text}");
        assert!(text.contains("v3.@pair = agg.make @pair v0 v1;"), "{text}");
    }

    #[test]
    fn updates_and_dynamic_indices_stay() {
        let (changed, _) = fold(
            "func public %f(v0.@pair, v1.i64, v2.i8) -> @pair {
block0:
    v3.@pair = insert_value v0 0.i8 v1;
    v4.[i64; 2] = insert_value undef.[i64; 2] v2 v1;
    v5.i64 = extract_value v4 0.i8;
    v6.@pair = insert_value v3 1.i8 v5;
    return v6;
}",
        );
        assert!(!changed);
    }

    #[test]
    fn a_dynamic_insert_ends_the_chain_before_it() {
        let (changed, text) = fold(
            "func public %f(v0.i64, v1.i8) -> [i64; 2] {
block0:
    v2.[i64; 2] = insert_value undef.[i64; 2] 0.i8 v0;
    v3.[i64; 2] = insert_value v2 v1 v0;
    return v3;
}",
        );
        assert!(changed);
        assert!(
            text.contains("v2.[i64; 2] = agg.make [i64; 2] v0 undef.i64;"),
            "{text}"
        );
        assert!(
            text.contains("v3.[i64; 2] = insert_value v2 v1 v0;"),
            "{text}"
        );
    }

    #[test]
    fn chains_sharing_a_prefix_fold_apart() {
        let (changed, text) = fold(
            "func public %f(v0.i64, v1.i64) -> @pair {
block0:
    v2.@pair = insert_value undef.@pair 0.i8 v0;
    v3.@pair = insert_value v2 1.i8 v0;
    v4.@pair = insert_value v2 1.i8 v1;
    v5.i64 = extract_value v3 1.i8;
    v6.@pair = insert_value v4 0.i8 v5;
    return v6;
}",
        );
        assert!(changed);
        assert!(text.contains("v3.@pair = agg.make @pair v0 v0;"), "{text}");
        assert!(text.contains("v6.@pair = agg.make @pair v5 v1;"), "{text}");
        assert!(!text.contains("insert_value"), "{text}");
    }

    #[test]
    fn a_chain_nothing_reads_goes() {
        let (changed, text) = fold(
            "func public %f(v0.i64) -> i64 {
block0:
    v1.@pair = agg.make @pair v0 v0;
    v2.@pair = insert_value v1 0.i8 v0;
    v3.@pair = insert_value undef.@pair 0.i8 v0;
    v4.@pair = insert_value v3 1.i8 v0;
    return v0;
}",
        );
        assert!(changed);
        assert!(!text.contains("insert_value"), "{text}");
        assert!(!text.contains("agg.make"), "{text}");
    }

    #[test]
    fn a_long_chain_folds_once() {
        let len = 1000;
        let mut body = format!("func public %f(v0.i64) -> [i64; {len}] {{\nblock0:\n");
        let mut current = format!("undef.[i64; {len}]");
        for index in 0..len {
            let next = format!("v{}", index + 1);
            body.push_str(&format!(
                "    {next}.[i64; {len}] = insert_value {current} {index}.i32 v0;\n"
            ));
            current = next;
        }
        body.push_str(&format!("    return {current};\n}}"));
        let (changed, text) = fold(&body);
        assert!(changed);
        assert_eq!(text.matches("agg.make").count(), 1, "{text}");
        assert!(!text.contains("insert_value"));
    }

    #[test]
    fn a_sparse_insert_into_a_long_array_stays() {
        for (len, folds) in [
            (MAX_UNWRITTEN_FIELDS + 1, true),
            (MAX_UNWRITTEN_FIELDS + 2, false),
        ] {
            let (changed, _) = fold(&format!(
                "func public %f(v0.i8) -> [i8; {len}] {{
block0:
    v1.[i8; {len}] = insert_value undef.[i8; {len}] 0.i8 v0;
    return v1;
}}"
            ));
            assert_eq!(changed, folds, "{len}");
        }
    }

    #[test]
    fn unwritten_fields_are_undef_of_their_type() {
        let (changed, text) = fold(
            "func private %f(v0.@flag) -> @kinds {
block0:
    v1.@kinds = insert_value undef.@kinds 0.i8 v0;
    return v1;
}",
        );
        assert!(changed);
        assert!(
            text.contains(
                "v1.@kinds = agg.make @kinds v0 undef.unit undef.[i8; 0] undef.@pair undef.[i64; 2];"
            ),
            "{text}"
        );
    }
}
