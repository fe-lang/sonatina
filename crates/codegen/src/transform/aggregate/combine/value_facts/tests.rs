use super::{
    super::{inst_const_index, shape},
    AggregateValueFacts,
};
use rustc_hash::FxHashMap;
use sonatina_ir::{Function, ValueId, inst::data};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

fn compare_with_reference(source: &str) {
    let module = parse_module(source).expect("valid test IR").module;
    verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    for func_ref in module.funcs() {
        module.func_store.view(func_ref, |func| {
            let facts = AggregateValueFacts::compute(func);
            for value in func.dfg.value_ids() {
                if shape::is_supported_aggregate_ty(func.ctx(), func.dfg.value_ty(value)) {
                    assert_eq!(
                        facts.reconstructed[value],
                        try_reconstruct_original_aggregate(func, value),
                        "reconstruction of {value:?}\n{source}"
                    );
                }
            }
        });
    }
}

#[test]
fn insertion_forests_match_independent_prefix_evaluation() {
    for seed in 0..24u64 {
        let mut state = seed + 1;
        let mut source = String::from(
            "target = \"evm-ethereum-osaka\"\nfunc private %f(v0.[i256; 4], v1.[i256; 4], v2.i8) {\nblock0:\n",
        );
        let mut bases = vec![
            "zero.[i256; 4]".to_string(),
            "v0".to_string(),
            "v1".to_string(),
        ];
        for step in 0..96 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let field = step * 2 + 3;
            let result = field + 1;
            let index = (state >> 32) % 4;
            let payload = match state % 4 {
                0 | 1 => {
                    source.push_str(&format!(
                        "v{field}.i256 = extract_value v{} {index}.i8;\n",
                        state % 2
                    ));
                    format!("v{field}")
                }
                2 => "0.i256".to_string(),
                _ => format!("{step}.i256"),
            };
            let base = if step % 3 == 0 {
                bases.len() - 1
            } else {
                (state >> 16) as usize % bases.len()
            };
            let index = if state % 11 == 0 {
                "v2".to_string()
            } else {
                format!("{index}.i8")
            };
            source.push_str(&format!(
                "v{result}.[i256; 4] = insert_value {} {index} {payload};\n",
                bases[base]
            ));
            bases.push(format!("v{result}"));
        }
        source.push_str("return;\n}\n");
        compare_with_reference(&source);
    }
}

#[test]
fn nested_and_loop_carried_facts_match_independent_evaluation() {
    compare_with_reference(
        r#"
target = "evm-ethereum-osaka"
type @pair = { i256, i256 };
type @outer = { @pair, @pair };

func private %nested(v0.@outer, v1.i8) {
block0:
    v2.@pair = extract_value v0 0.i8;
    v3.@pair = extract_value v0 0.i8;
    v4.i256 = extract_value v2 0.i8;
    v5.i256 = extract_value v3 1.i8;
    v6.@pair = agg.make @pair v4 0.i256;
    v7.@pair = insert_value v6 1.i8 v5;
    v8.@pair = extract_value v0 1.i8;
    v9.@outer = agg.make @outer v7 zero.@pair;
    v10.@outer = insert_value v9 1.i8 v8;
    v11.@pair = insert_value v6 1.i8 0.i256;
    v12.@outer = insert_value v9 1.i8 v11;
    v13.@pair = insert_value v6 0.i8 42.i256;
    v14.@pair = insert_value v13 1.i8 v5;
    v15.@outer = insert_value v9 0.i8 v14;
    v16.@outer = insert_value v15 1.i8 v8;
    v17.[i256; 2] = insert_value zero.[i256; 2] v1 v4;
    v18.[i256; 2] = insert_value v17 0.i8 v4;
    v19.[i256; 2] = insert_value v18 1.i8 v5;
    v20.@pair = bitcast v19 @pair;
    v21.@outer = insert_value v9 1.i8 v7;
    v22.@outer = insert_value v21 1.i8 v8;
    return;
}

func private %loop(v0.i1, v1.@pair) {
block0:
    jump block1;
block2:
    v5.@pair = insert_value v2 0.i8 7.i256;
    v6.@pair = insert_value v3 1.i8 9.i256;
    jump block1;
block1:
    v2.@pair = phi (v1 block0) (v5 block2);
    v3.@pair = phi (zero.@pair block0) (v6 block2);
    v4.@pair = phi (v1 block0) (v4 block2);
    br v0 block2 block3;
block3:
    return;
}
"#,
    );
}

fn try_reconstruct_original_aggregate(func: &Function, value: ValueId) -> Option<ValueId> {
    let agg_ty = func.dfg.value_ty(value);
    let field_count = shape::aggregate_child_count(func.ctx(), agg_ty)?;
    if field_count == 0 {
        return None;
    }

    let assignments = collect_insert_assignments(func, value)?;
    if assignments.len() != field_count {
        return None;
    }

    let mut source: Option<ValueId> = None;
    for idx in 0..field_count {
        let idx_u32 = u32::try_from(idx).ok()?;
        let field_val = *assignments.get(&idx_u32)?;
        let mut path = vec![idx_u32];
        let field_source = source_for_path_value(func, field_val, &mut path)?;
        if source.is_none() {
            source = Some(field_source);
        } else if source != Some(field_source) {
            return None;
        }
    }

    let source = source?;
    (func.dfg.value_ty(source) == agg_ty).then_some(source)
}

fn collect_insert_assignments(func: &Function, value: ValueId) -> Option<FxHashMap<u32, ValueId>> {
    let mut assignments: FxHashMap<u32, ValueId> = FxHashMap::default();
    let mut current = value;
    while let Some(inst) = func.dfg.value_inst(current) {
        let Some(insert) = func.dfg.downcast::<&data::InsertValue>(inst) else {
            break;
        };
        let idx = inst_const_index(func, *insert.idx())?;
        assignments.entry(idx).or_insert(*insert.value());
        current = *insert.dest();
    }
    Some(assignments)
}

fn source_for_path_value(func: &Function, value: ValueId, path: &mut Vec<u32>) -> Option<ValueId> {
    if let Some(source) = extract_chain_source(func, value, path) {
        return Some(source);
    }

    let value_ty = func.dfg.value_ty(value);
    let child_count = shape::aggregate_child_count(func.ctx(), value_ty)?;
    if child_count == 0 {
        return None;
    }

    let assignments = collect_insert_assignments(func, value)?;
    if assignments.len() != child_count {
        return None;
    }

    let mut source: Option<ValueId> = None;
    for idx in 0..child_count {
        let idx_u32 = u32::try_from(idx).ok()?;
        let field_val = *assignments.get(&idx_u32)?;
        path.push(idx_u32);
        let field_source = source_for_path_value(func, field_val, path)?;
        path.pop();
        if source.is_none() {
            source = Some(field_source);
        } else if source != Some(field_source) {
            return None;
        }
    }

    source
}

fn extract_chain_source(func: &Function, mut value: ValueId, path: &[u32]) -> Option<ValueId> {
    for &idx in path.iter().rev() {
        let inst = func.dfg.value_inst(value)?;
        let extract = func.dfg.downcast::<&data::ExtractValue>(inst)?;
        if inst_const_index(func, *extract.idx()) != Some(idx) {
            return None;
        }
        value = *extract.dest();
    }
    Some(value)
}
