use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, Immediate, Linkage, Module, Signature, Type, Value, ValueId,
    inst::{control_flow, data},
    module::FuncRef,
    types::CompoundType,
};

use super::const_eval::{
    ConstPath, ConstPathAnalysis, ConstPathStep, analyze_const_paths, collect_constref_value_tys,
};

#[derive(Debug, Default)]
pub(crate) struct ConstRefSpecializationStats {
    pub(crate) changed: bool,
    pub(crate) clones_created: usize,
    pub(crate) calls_rewritten: usize,
    pub(crate) args_bound: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SpecializationKey {
    callee: FuncRef,
    bindings: Vec<ConstRefBinding>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ConstRefBinding {
    arg_idx: usize,
    path: ConstPath,
}

#[derive(Debug)]
struct Candidate {
    constref_args: Vec<usize>,
}

#[derive(Debug)]
struct RewriteSite {
    caller: FuncRef,
    inst: sonatina_ir::InstId,
    key: SpecializationKey,
}

#[derive(Clone, Copy)]
struct PrependedValue {
    inst: sonatina_ir::InstId,
    value: ValueId,
}

pub(crate) fn specialize_private_constrefs(
    module: &Module,
    funcs: &[FuncRef],
) -> ConstRefSpecializationStats {
    let candidates = collect_candidates(module, funcs);
    if candidates.is_empty() {
        return ConstRefSpecializationStats::default();
    }

    let sites = collect_rewrite_sites(module, funcs, &candidates);
    if sites.is_empty() {
        return ConstRefSpecializationStats::default();
    }

    let mut stats = ConstRefSpecializationStats::default();
    let mut clones = FxHashMap::<SpecializationKey, FuncRef>::default();
    let mut rewrites_by_caller =
        FxHashMap::<FuncRef, Vec<(sonatina_ir::InstId, FuncRef)>>::default();
    for site in sites {
        let clone = if let Some(&clone) = clones.get(&site.key) {
            clone
        } else {
            let clone = clone_specialized_func(module, &site.key);
            stats.clones_created += 1;
            stats.args_bound += site.key.bindings.len();
            clones.insert(site.key.clone(), clone);
            clone
        };
        rewrites_by_caller
            .entry(site.caller)
            .or_default()
            .push((site.inst, clone));
    }

    for (caller, rewrites) in rewrites_by_caller {
        module.func_store.modify(caller, |function| {
            for (inst, clone) in rewrites {
                if rewrite_call_callee(function, inst, clone) {
                    stats.calls_rewritten += 1;
                }
            }
        });
    }

    stats.changed = stats.calls_rewritten != 0;
    stats
}

fn collect_candidates(module: &Module, funcs: &[FuncRef]) -> FxHashMap<FuncRef, Candidate> {
    funcs
        .iter()
        .copied()
        .filter_map(|func| {
            let sig = module.ctx.get_sig(func)?;
            if sig.linkage() != Linkage::Private || !module.func_store.contains(func) {
                return None;
            }

            let constref_args = sig
                .args()
                .iter()
                .enumerate()
                .filter_map(|(idx, &ty)| is_constref_ty(module, ty).then_some(idx))
                .collect::<Vec<_>>();
            (!constref_args.is_empty()).then_some((func, Candidate { constref_args }))
        })
        .collect()
}

fn collect_rewrite_sites(
    module: &Module,
    funcs: &[FuncRef],
    candidates: &FxHashMap<FuncRef, Candidate>,
) -> Vec<RewriteSite> {
    let mut sites = Vec::new();
    for &caller in funcs {
        module.func_store.view(caller, |function| {
            let const_paths = analyze_const_paths(function, &collect_constref_value_tys(function));
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.cast_call(inst) else {
                        continue;
                    };
                    let callee = *call.callee();
                    let Some(candidate) = candidates.get(&callee) else {
                        continue;
                    };
                    let bindings = collect_call_bindings(call.args(), candidate, &const_paths);
                    if !bindings.is_empty() {
                        sites.push(RewriteSite {
                            caller,
                            inst,
                            key: SpecializationKey { callee, bindings },
                        });
                    }
                }
            }
        });
    }
    sites
}

fn collect_call_bindings(
    args: &[ValueId],
    candidate: &Candidate,
    const_paths: &ConstPathAnalysis,
) -> Vec<ConstRefBinding> {
    let mut bindings = Vec::new();
    for &arg_idx in &candidate.constref_args {
        let Some(path) = args.get(arg_idx).and_then(|&arg| const_paths.path(arg)) else {
            continue;
        };
        if path
            .steps
            .iter()
            .any(|step| matches!(step, ConstPathStep::IndexValue(_)))
        {
            continue;
        }
        bindings.push(ConstRefBinding {
            arg_idx,
            path: path.clone(),
        });
    }
    bindings
}

fn clone_specialized_func(module: &Module, key: &SpecializationKey) -> FuncRef {
    let sig = module
        .ctx
        .get_sig(key.callee)
        .expect("specialized callee should have a signature");
    let mut func = module.func_store.view(key.callee, Clone::clone);
    bind_constref_args(&mut func, &key.bindings);

    let clone = module.func_store.insert(func);
    module.ctx.clear_func_metadata(clone);
    module
        .ctx
        .declared_funcs
        .insert(clone, specialized_sig(module, key, &sig));
    let hints = module.ctx.func_hints(key.callee);
    if !hints.is_empty() {
        module.ctx.set_func_hints(clone, hints);
    }
    clone
}

fn specialized_sig(module: &Module, key: &SpecializationKey, sig: &Signature) -> Signature {
    Signature::new(
        &fresh_func_name(module, key, sig.name()),
        Linkage::Private,
        sig.args(),
        sig.ret_tys(),
    )
}

fn fresh_func_name(module: &Module, key: &SpecializationKey, base: &str) -> String {
    let mut stem = format!("{base}__constref");
    for binding in &key.bindings {
        stem.push_str(&format!(
            "_a{}_g{}",
            binding.arg_idx,
            binding.path.global.as_u32()
        ));
        for step in &binding.path.steps {
            match step {
                ConstPathStep::Field(idx) => stem.push_str(&format!("f{idx}")),
                ConstPathStep::IndexConst(idx) => stem.push_str(&format!("i{idx}")),
                ConstPathStep::IndexValue(_) => unreachable!("dynamic constref bindings rejected"),
            }
        }
    }
    if !func_name_exists(module, &stem) {
        return stem;
    }

    for suffix in 1u32.. {
        let name = format!("{stem}_{suffix}");
        if !func_name_exists(module, &name) {
            return name;
        }
    }
    unreachable!("fresh function name search should not overflow");
}

fn func_name_exists(module: &Module, name: &str) -> bool {
    module
        .ctx
        .declared_funcs
        .iter()
        .any(|entry| entry.value().name() == name)
}

fn bind_constref_args(func: &mut Function, bindings: &[ConstRefBinding]) {
    let Some(entry) = func.layout.entry_block() else {
        return;
    };

    for binding in bindings.iter().rev() {
        let arg = func.arg_values[binding.arg_idx];
        let replacement = prepend_const_path(func, entry, &binding.path);
        debug_assert_eq!(func.dfg.value_ty(replacement), func.dfg.value_ty(arg));
        func.dfg.change_to_alias(arg, replacement);
    }
}

fn prepend_const_path(
    func: &mut Function,
    entry: sonatina_ir::BlockId,
    path: &ConstPath,
) -> ValueId {
    let mut current_ty = func.ctx().with_gv_store(|store| store.ty(path.global));
    let mut cursor = prepend_const_ref(
        func,
        entry,
        path.global,
        current_ty.to_const_ref(func.ctx()),
    );

    for step in &path.steps {
        let (next, next_ty) = match step {
            ConstPathStep::Field(idx) => prepend_const_proj(func, cursor, current_ty, *idx),
            ConstPathStep::IndexConst(idx) => prepend_const_index(func, cursor, current_ty, *idx),
            ConstPathStep::IndexValue(_) => unreachable!("dynamic constref bindings rejected"),
        };
        cursor = next;
        current_ty = next_ty;
    }

    cursor.value
}

fn prepend_const_ref(
    func: &mut Function,
    entry: sonatina_ir::BlockId,
    global: sonatina_ir::GlobalVariableRef,
    ty: Type,
) -> PrependedValue {
    let inst = func.dfg.make_inst(data::ConstRef::new(
        func.inst_set()
            .has_const_ref()
            .expect("target ISA should support const.ref"),
        global.into(),
    ));
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    func.dfg.attach_result(inst, value);
    func.layout.prepend_inst(inst, entry);
    PrependedValue { inst, value }
}

fn prepend_const_proj(
    func: &mut Function,
    base: PrependedValue,
    base_ty: Type,
    idx: usize,
) -> (PrependedValue, Type) {
    let Some(CompoundType::Struct(s)) = base_ty.resolve_compound(func.ctx()) else {
        panic!("specialized const.proj base must be a struct");
    };
    assert!(
        !s.packed,
        "packed structs are unsupported in constref specialization"
    );
    let field_ty = *s
        .fields
        .get(idx)
        .expect("specialized const.proj index out of bounds");
    let index = func
        .dfg
        .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
    let inst = func.dfg.make_inst(data::ConstProj::new(
        func.inst_set()
            .has_const_proj()
            .expect("target ISA should support const.proj"),
        smallvec![base.value, index],
    ));
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty: field_ty.to_const_ref(func.ctx()),
    });
    func.dfg.attach_result(inst, value);
    func.layout.insert_inst_after(inst, base.inst);
    func.propagate_inst_attribution(inst, base.inst);
    (PrependedValue { inst, value }, field_ty)
}

fn prepend_const_index(
    func: &mut Function,
    base: PrependedValue,
    base_ty: Type,
    idx: usize,
) -> (PrependedValue, Type) {
    let Some(CompoundType::Array { elem, len }) = base_ty.resolve_compound(func.ctx()) else {
        panic!("specialized const.index base must be an array");
    };
    assert!(idx < len, "specialized const.index index out of bounds");
    let index = func
        .dfg
        .make_imm_value(Immediate::I64(i64::try_from(idx).expect("index overflow")));
    let inst = func.dfg.make_inst(data::ConstIndex::new(
        func.inst_set()
            .has_const_index()
            .expect("target ISA should support const.index"),
        base.value,
        index,
    ));
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty: elem.to_const_ref(func.ctx()),
    });
    func.dfg.attach_result(inst, value);
    func.layout.insert_inst_after(inst, base.inst);
    func.propagate_inst_attribution(inst, base.inst);
    (PrependedValue { inst, value }, elem)
}

fn rewrite_call_callee(function: &mut Function, inst: sonatina_ir::InstId, clone: FuncRef) -> bool {
    let Some(call) = function.dfg.cast_call(inst).cloned() else {
        return false;
    };
    let args: SmallVec<[_; 8]> = call.args().iter().copied().collect();
    function.dfg.replace_inst_preserving_results(
        inst,
        Box::new(control_flow::Call::new(
            function
                .inst_set()
                .has_call()
                .expect("target ISA should support call"),
            clone,
            args,
        )),
    );
    true
}

fn is_constref_ty(module: &Module, ty: Type) -> bool {
    matches!(
        ty.resolve_compound(&module.ctx),
        Some(CompoundType::ConstRef(_))
    )
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        ir_writer::ModuleWriter,
        module::{FuncHints, FuncRef},
    };
    use sonatina_parser::parse_module;

    use super::*;

    #[test]
    fn specializes_private_callee_for_known_constref_root() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $zeros = [0, 0, 0, 0];

func private %get(v0.constref<[i256; 4]>, v1.i256) -> i256 {
    block0:
        v2.constref<i256> = const.index v0 v1;
        v3.i256 = const.load v2;
        return v3;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $zeros;
        v2.i256 = call %get v1 v0;
        return v2;
}
"#,
        )
        .expect("module parses");

        let stats = specialize_private_constrefs(&parsed.module, &parsed.module.funcs());
        assert!(stats.changed);
        assert_eq!(stats.clones_created, 1);
        assert_eq!(stats.calls_rewritten, 1);

        let dumped = ModuleWriter::new(&parsed.module).dump_string();
        assert!(dumped.contains("func private %get__constref_a0_g"));
        assert!(dumped.contains("call %get__constref_a0_g"));

        let clone = find_func(&parsed.module, "get__constref_a0_g");
        let clone_dump = parsed.module.func_store.view(clone, |func| {
            sonatina_ir::ir_writer::FuncWriter::new(clone, func).dump_string()
        });
        assert!(clone_dump.contains("const.ref $zeros"));
    }

    #[test]
    fn specializes_private_callee_for_static_constref_subpath() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

global private const [[i256; 2]; 2] $rows = [[1, 2], [7, 7]];

func private %get(v0.constref<[i256; 2]>, v1.i256) -> i256 {
    block0:
        v2.constref<i256> = const.index v0 v1;
        v3.i256 = const.load v2;
        return v3;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[[i256; 2]; 2]> = const.ref $rows;
        v2.constref<[i256; 2]> = const.index v1 1.i8;
        v3.i256 = call %get v2 v0;
        return v3;
}
"#,
        )
        .expect("module parses");

        let stats = specialize_private_constrefs(&parsed.module, &parsed.module.funcs());
        assert!(stats.changed);
        assert_eq!(stats.clones_created, 1);
        assert_eq!(stats.calls_rewritten, 1);

        let dumped = ModuleWriter::new(&parsed.module).dump_string();
        assert!(dumped.contains("func private %get__constref_a0_g0i1"));
        assert!(dumped.contains("call %get__constref_a0_g0i1"));

        let clone = find_func(&parsed.module, "get__constref_a0_g0i1");
        let clone_dump = parsed.module.func_store.view(clone, |func| {
            sonatina_ir::ir_writer::FuncWriter::new(clone, func).dump_string()
        });
        assert!(clone_dump.contains("const.ref $rows"));
        assert!(clone_dump.contains("const.index"));
    }

    #[test]
    fn specialized_clone_preserves_noinline_hint() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $zeros = [0, 0, 0, 0];

func inline(never) private %get(v0.constref<[i256; 4]>, v1.i256) -> i256 {
    block0:
        v2.constref<i256> = const.index v0 v1;
        v3.i256 = const.load v2;
        return v3;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $zeros;
        v2.i256 = call %get v1 v0;
        return v2;
}
"#,
        )
        .expect("module parses");

        let stats = specialize_private_constrefs(&parsed.module, &parsed.module.funcs());
        assert!(stats.changed);

        let clone = find_func(&parsed.module, "get__constref_a0_g");
        assert!(
            parsed
                .module
                .ctx
                .func_hints(clone)
                .contains(FuncHints::NOINLINE),
            "specialized clones of noinline callees must remain noinline"
        );
    }

    fn find_func(module: &Module, name_prefix: &str) -> FuncRef {
        module
            .ctx
            .declared_funcs
            .iter()
            .find_map(|entry| {
                entry
                    .value()
                    .name()
                    .starts_with(name_prefix)
                    .then_some(*entry.key())
            })
            .expect("function should exist")
    }
}
