use cranelift_entity::SecondaryMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, Immediate, InstId, ValueId,
    inst::{BinaryInstKind, InstClassKind, data, downcast},
};

use super::{
    const_eval::{
        BlockEdge, ConstPathAnalysis, dynamic_index_values, eval_const_path_domain_immediate,
    },
    sccp::LatticeCell,
    simplify_expr::{
        ExprFactProvider, SimplifiedInst, SimplifiedResult, ZextI1CompareRewrite,
        simplify_inst_with_facts, simplify_zext_i1_compare,
    },
};
use crate::{
    analysis::known_bits::{KnownBits, KnownBitsQuery},
    transform::aggregate::fresh::is_fresh_chain_end,
};

#[derive(Clone, Copy)]
pub(super) enum SimplifyAction {
    Const(Immediate),
    Copy(ValueId),
    BuildIsZero(ValueId),
    /// The last insert of a chain into `zero` or an `agg.make`: it becomes
    /// an `agg.make` (`transform::aggregate::fresh`).
    FoldFreshInsert,
    NoChange,
}

pub(super) type SimplifyResults = SmallVec<[SimplifyAction; 1]>;

#[derive(Default)]
pub(super) struct AuxDeps {
    pub(super) value_deps: SmallVec<[ValueId; 2]>,
    pub(super) edge_deps: SmallVec<[BlockEdge; 2]>,
}

impl AuxDeps {
    fn clear(&mut self) {
        self.value_deps.clear();
        self.edge_deps.clear();
    }
}

pub(super) struct SimplifyCtx<'a> {
    pub(super) const_paths: &'a ConstPathAnalysis,
    pub(super) known_bits: &'a KnownBitsQuery,
    pub(super) is_edge_executable: &'a dyn Fn(BlockId, BlockId) -> bool,
    pub(super) aux_deps: &'a mut AuxDeps,
}

fn from_simplified_result(simplified: SimplifiedResult) -> SimplifyAction {
    match simplified {
        SimplifiedResult::Const(imm) => SimplifyAction::Const(imm),
        SimplifiedResult::Copy(value) => SimplifyAction::Copy(value),
        SimplifiedResult::NoChange => SimplifyAction::NoChange,
    }
}

fn from_simplified_inst(simplified: SimplifiedInst) -> SimplifyResults {
    simplified
        .results
        .into_iter()
        .map(from_simplified_result)
        .collect()
}

fn wrap_action(action: SimplifyAction) -> SimplifyResults {
    smallvec![action]
}

fn no_change_results(len: usize) -> SimplifyResults {
    std::iter::repeat_n(SimplifyAction::NoChange, len).collect()
}

fn known_imm(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    v: ValueId,
) -> Option<Immediate> {
    func.dfg
        .get_value(v)
        .and_then(|_| func.dfg.value_imm(v))
        .or_else(|| match lattice.get(v) {
            Some(LatticeCell::Const(imm)) => Some(*imm),
            _ => None,
        })
}

struct SccpExprFacts<'a, 'b> {
    func: &'a Function,
    lattice: &'b SecondaryMap<ValueId, LatticeCell>,
    known_bits: &'b KnownBitsQuery,
}

impl ExprFactProvider for SccpExprFacts<'_, '_> {
    fn known_imm(&self, v: ValueId) -> Option<Immediate> {
        known_imm(self.func, self.lattice, v)
    }

    fn known_bits(&self, func: &Function, v: ValueId) -> KnownBits {
        if let Some(imm) = self.known_imm(v) {
            return KnownBits::from_imm(imm);
        }

        debug_assert_eq!(func.dfg.value_ty(v), self.func.dfg.value_ty(v));
        self.known_bits.for_value(func, v)
    }
}

fn simplify_gep_all_zero(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    values: &[ValueId],
) -> SimplifyAction {
    let Some((&base, indices)) = values.split_first() else {
        return SimplifyAction::NoChange;
    };

    if indices
        .iter()
        .all(|&idx| known_imm(func, lattice, idx).is_some_and(Immediate::is_zero))
    {
        return SimplifyAction::Copy(base);
    }

    SimplifyAction::NoChange
}

fn simplify_const_load(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    object: ValueId,
    ctx: &mut SimplifyCtx<'_>,
) -> SimplifyAction {
    if let Some(path) = ctx.const_paths.reachable_path(
        func,
        object,
        |from, to| (ctx.is_edge_executable)(from, to),
        &mut ctx.aux_deps.edge_deps,
    ) {
        for value in dynamic_index_values(&path) {
            if !ctx.aux_deps.value_deps.contains(&value) {
                ctx.aux_deps.value_deps.push(value);
            }
        }
        return eval_const_path_domain_immediate(func.ctx(), &path, |value| {
            known_imm(func, lattice, value)
        })
        .map_or(SimplifyAction::NoChange, SimplifyAction::Const);
    }

    SimplifyAction::NoChange
}

fn simplify_zext_i1_compare_action(
    func: &Function,
    facts: &impl ExprFactProvider,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    simplify_zext_i1_compare(func, kind, lhs, rhs, |value| facts.known_imm(value)).map_or(
        SimplifyAction::NoChange,
        |rewrite| match rewrite {
            ZextI1CompareRewrite::Copy(value) => SimplifyAction::Copy(value),
            ZextI1CompareRewrite::IsZero(value) => SimplifyAction::BuildIsZero(value),
        },
    )
}

pub(super) fn simplify_inst(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    inst_id: InstId,
    ctx: &mut SimplifyCtx<'_>,
) -> SimplifyResults {
    ctx.aux_deps.clear();
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();
    let results_len = func.dfg.inst_results(inst_id).len();
    let facts = SccpExprFacts {
        func,
        lattice,
        known_bits: ctx.known_bits,
    };

    let shared = simplify_inst_with_facts(func, inst_id, &facts);
    if !shared.is_no_change() {
        return from_simplified_inst(shared);
    }

    match inst.kind() {
        InstClassKind::Binary(kind @ (BinaryInstKind::Eq | BinaryInstKind::Ne)) => {
            let values = inst.collect_values();
            let [lhs, rhs] = values.as_slice() else {
                return no_change_results(results_len);
            };
            let simplified = simplify_zext_i1_compare_action(func, &facts, kind, *lhs, *rhs);
            if matches!(simplified, SimplifyAction::NoChange) {
                no_change_results(results_len)
            } else {
                wrap_action(simplified)
            }
        }
        InstClassKind::Phi | InstClassKind::Opaque => {
            if let Some(extract) = downcast::<&data::ExtractValue>(is, inst)
                && let Some(make) = func
                    .dfg
                    .value_inst(*extract.dest())
                    .and_then(|make| downcast::<&data::AggMake>(is, func.dfg.inst(make)))
                && let Some(index) = facts
                    .known_imm(*extract.idx())
                    .and_then(Immediate::to_nonnegative_usize)
                && let Some(&field) = make.values().get(index)
            {
                // The field is not an operand of the extract: reevaluate it
                // when the field changes.
                ctx.aux_deps.value_deps.push(field);
                return wrap_action(SimplifyAction::Copy(field));
            }
            if downcast::<&data::InsertValue>(is, inst).is_some()
                && is_fresh_chain_end(func, inst_id)
            {
                return wrap_action(SimplifyAction::FoldFreshInsert);
            }
            if let Some(i) = downcast::<&data::ConstLoad>(is, inst) {
                return wrap_action(simplify_const_load(func, lattice, *i.object(), ctx));
            }
            if let Some(i) = downcast::<&data::Gep>(is, inst) {
                return wrap_action(simplify_gep_all_zero(func, lattice, i.values().as_slice()));
            }
            no_change_results(results_len)
        }
        InstClassKind::Unary(_) | InstClassKind::Binary(_) | InstClassKind::Cast(_) => {
            no_change_results(results_len)
        }
    }
}

#[cfg(test)]
mod tests {
    use cranelift_entity::SecondaryMap;
    use sonatina_ir::{Function, I256, Immediate, InstId, Type, U256, inst::data, module::FuncRef};
    use sonatina_parser::parse_module;

    use super::{AuxDeps, SimplifyAction, SimplifyCtx, simplify_inst};
    use crate::{
        analysis::known_bits::KnownBitsQuery,
        optim::{
            const_eval::{analyze_const_paths, collect_constref_value_tys},
            sccp::LatticeCell,
        },
    };

    #[test]
    fn simplify_inst_folds_logical_shr_mask_with_known_bits() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-london"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = shr 224.i256 v0;
    v2.i256 = and v1 4294967295.i256;
    return v2;
}
"#,
        );

        module.func_store.view(func_ref, |func| {
            let and_inst = find_inst(
                func,
                sonatina_ir::inst::InstClassKind::Binary(sonatina_ir::inst::BinaryInstKind::And),
            );
            let inst = and_inst.expect("missing and");
            let lattice = SecondaryMap::<_, LatticeCell>::default();
            let constref_value_tys = collect_constref_value_tys(func);
            let const_paths = analyze_const_paths(func, &constref_value_tys);
            let known_bits = KnownBitsQuery::new(func);
            let is_edge_executable = |_, _| false;
            let mut aux_deps = AuxDeps::default();
            let mut simplify_ctx = SimplifyCtx {
                const_paths: &const_paths,
                known_bits: &known_bits,
                is_edge_executable: &is_edge_executable,
                aux_deps: &mut aux_deps,
            };
            let simplified = simplify_inst(func, &lattice, inst, &mut simplify_ctx);
            let and_args = func.dfg.inst(inst).collect_values();
            let [value, _mask] = and_args.as_slice() else {
                panic!("and should have two args");
            };
            assert!(simplified.iter().any(|action| {
                matches!(action, SimplifyAction::Copy(candidate) if candidate == value)
            }));
        });
    }

    #[test]
    fn simplify_inst_folds_eq_zext_i1_one_to_copy() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-london"

func public %f(v0.i1) -> i1 {
block0:
    v1.i256 = zext v0 i256;
    v2.i1 = eq v1 1.i256;
    return v2;
}
"#,
        );

        module.func_store.view(func_ref, |func| {
            let inst = find_inst(
                func,
                sonatina_ir::inst::InstClassKind::Binary(sonatina_ir::inst::BinaryInstKind::Eq),
            )
            .expect("missing eq");
            let lattice = SecondaryMap::<_, LatticeCell>::default();
            let constref_value_tys = collect_constref_value_tys(func);
            let const_paths = analyze_const_paths(func, &constref_value_tys);
            let known_bits = KnownBitsQuery::new(func);
            let is_edge_executable = |_, _| false;
            let mut aux_deps = AuxDeps::default();
            let mut simplify_ctx = SimplifyCtx {
                const_paths: &const_paths,
                known_bits: &known_bits,
                is_edge_executable: &is_edge_executable,
                aux_deps: &mut aux_deps,
            };
            let simplified = simplify_inst(func, &lattice, inst, &mut simplify_ctx);
            assert!(matches!(simplified.as_slice(), [SimplifyAction::Copy(value)] if *value == func.arg_values[0]));
        });
    }

    #[test]
    fn simplify_inst_folds_ne_zext_i1_one_to_is_zero() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-london"

func public %f(v0.i1) -> i1 {
block0:
    v1.i256 = zext v0 i256;
    v2.i1 = ne v1 1.i256;
    return v2;
}
"#,
        );

        module.func_store.view(func_ref, |func| {
            let inst = find_inst(
                func,
                sonatina_ir::inst::InstClassKind::Binary(sonatina_ir::inst::BinaryInstKind::Ne),
            )
            .expect("missing ne");
            let lattice = SecondaryMap::<_, LatticeCell>::default();
            let constref_value_tys = collect_constref_value_tys(func);
            let const_paths = analyze_const_paths(func, &constref_value_tys);
            let known_bits = KnownBitsQuery::new(func);
            let is_edge_executable = |_, _| false;
            let mut aux_deps = AuxDeps::default();
            let mut simplify_ctx = SimplifyCtx {
                const_paths: &const_paths,
                known_bits: &known_bits,
                is_edge_executable: &is_edge_executable,
                aux_deps: &mut aux_deps,
            };
            let simplified = simplify_inst(func, &lattice, inst, &mut simplify_ctx);
            assert!(matches!(simplified.as_slice(), [SimplifyAction::BuildIsZero(value)] if *value == func.arg_values[0]));
        });
    }

    #[test]
    fn simplify_const_load_keeps_huge_known_dynamic_index_unfolded() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $arr = [11, 22];

func public %f(v0.i256) -> i256 {
block0:
    v1.constref<[i256; 2]> = const.ref $arr;
    v2.constref<i256> = const.index v1 v0;
    v3.i256 = const.load v2;
    return v3;
}
"#,
        );

        module.func_store.view(func_ref, |func| {
            let inst = find_const_load_inst(func);
            let mut lattice = SecondaryMap::<_, LatticeCell>::default();
            lattice[func.arg_values[0]] = LatticeCell::Const(Immediate::from_i256(
                I256::from(U256::one() << 200),
                Type::I256,
            ));
            let constref_value_tys = collect_constref_value_tys(func);
            let const_paths = analyze_const_paths(func, &constref_value_tys);
            let known_bits = KnownBitsQuery::new(func);
            let is_edge_executable = |_, _| false;
            let mut aux_deps = AuxDeps::default();
            let mut simplify_ctx = SimplifyCtx {
                const_paths: &const_paths,
                known_bits: &known_bits,
                is_edge_executable: &is_edge_executable,
                aux_deps: &mut aux_deps,
            };
            let simplified = simplify_inst(func, &lattice, inst, &mut simplify_ctx);
            assert!(matches!(simplified.as_slice(), [SimplifyAction::NoChange]));
        });
    }

    #[test]
    fn simplify_const_load_folds_unknown_dynamic_splat() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [7, 7, 7, 7];

func public %f(v0.i256) -> i256 {
block0:
    v1.constref<[i256; 4]> = const.ref $arr;
    v2.constref<i256> = const.index v1 v0;
    v3.i256 = const.load v2;
    return v3;
}
"#,
        );

        module.func_store.view(func_ref, |func| {
            let inst = find_const_load_inst(func);
            let lattice = SecondaryMap::<_, LatticeCell>::default();
            let constref_value_tys = collect_constref_value_tys(func);
            let const_paths = analyze_const_paths(func, &constref_value_tys);
            let known_bits = KnownBitsQuery::new(func);
            let is_edge_executable = |_, _| false;
            let mut aux_deps = AuxDeps::default();
            let mut simplify_ctx = SimplifyCtx {
                const_paths: &const_paths,
                known_bits: &known_bits,
                is_edge_executable: &is_edge_executable,
                aux_deps: &mut aux_deps,
            };
            let simplified = simplify_inst(func, &lattice, inst, &mut simplify_ctx);
            assert!(matches!(
                simplified.as_slice(),
                [SimplifyAction::Const(Immediate::I256(value))] if *value == I256::from(7)
            ));
        });
    }

    #[test]
    fn simplify_const_load_keeps_unknown_dynamic_nonuniform_unfolded() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [7, 8, 7, 8];

func public %f(v0.i256) -> i256 {
block0:
    v1.constref<[i256; 4]> = const.ref $arr;
    v2.constref<i256> = const.index v1 v0;
    v3.i256 = const.load v2;
    return v3;
}
"#,
        );

        module.func_store.view(func_ref, |func| {
            let inst = find_const_load_inst(func);
            let lattice = SecondaryMap::<_, LatticeCell>::default();
            let constref_value_tys = collect_constref_value_tys(func);
            let const_paths = analyze_const_paths(func, &constref_value_tys);
            let known_bits = KnownBitsQuery::new(func);
            let is_edge_executable = |_, _| false;
            let mut aux_deps = AuxDeps::default();
            let mut simplify_ctx = SimplifyCtx {
                const_paths: &const_paths,
                known_bits: &known_bits,
                is_edge_executable: &is_edge_executable,
                aux_deps: &mut aux_deps,
            };
            let simplified = simplify_inst(func, &lattice, inst, &mut simplify_ctx);
            assert!(matches!(simplified.as_slice(), [SimplifyAction::NoChange]));
        });
    }

    fn parse_test_module(src: &str) -> (sonatina_ir::Module, FuncRef) {
        let parsed = parse_module(src).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .expect("missing f");
        (parsed.module, func_ref)
    }

    fn find_inst(func: &Function, kind: sonatina_ir::inst::InstClassKind) -> Option<InstId> {
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if func.dfg.inst(inst).kind() == kind {
                    return Some(inst);
                }
            }
        }
        None
    }

    fn find_const_load_inst(func: &Function) -> InstId {
        func.layout
            .iter_all_insts()
            .find(|&inst| func.dfg.downcast::<&data::ConstLoad>(inst).is_some())
            .expect("missing const.load")
    }
}
