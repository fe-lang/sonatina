use std::collections::VecDeque;

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, Immediate, InstId, Type, U256, Value, ValueId,
    inst::{BinaryInstKind, CastInstKind, InstClassKind, UnaryInstKind, control_flow::BranchKind},
};

use crate::loop_analysis::LoopTree;

pub type RangeEnv = FxHashMap<ValueId, RangeFact>;

const LOOP_WIDEN_CAP: u8 = 4;

#[derive(Clone, Debug, Default)]
pub struct RangeAnalysis {
    entry_envs: SecondaryMap<BlockId, RangeEnv>,
    exit_envs: SecondaryMap<BlockId, RangeEnv>,
    reachable: SecondaryMap<BlockId, bool>,
    initialized: SecondaryMap<BlockId, bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeFact {
    pub unsigned: UnsignedInterval,
    pub signed: SignedInterval,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnsignedInterval {
    pub lo: U256,
    pub hi: U256,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedInterval {
    pub lo: I256,
    pub hi: I256,
}

impl RangeAnalysis {
    pub fn compute(&mut self, func: &Function, cfg: &ControlFlowGraph, lpt: &LoopTree) {
        self.entry_envs.clear();
        self.exit_envs.clear();
        self.reachable.clear();
        self.initialized.clear();

        let Some(entry) = cfg.entry() else {
            return;
        };

        let static_reachable = cfg.reachable_blocks();
        let mut rpo: Vec<_> = cfg.post_order().collect();
        rpo.reverse();

        let mut worklist = VecDeque::new();
        let mut queued = SecondaryMap::<BlockId, bool>::default();
        let mut revisit_count = SecondaryMap::<BlockId, u8>::default();

        for &block in &rpo {
            if static_reachable[block] {
                worklist.push_back(block);
                queued[block] = true;
            }
        }

        while let Some(block) = worklist.pop_front() {
            queued[block] = false;

            let old_reachable = self.reachable[block];
            let old_initialized = self.initialized[block];

            let Some(mut new_entry) =
                compute_block_entry(func, cfg, block, entry, &self.exit_envs, &self.reachable)
            else {
                if old_reachable || old_initialized {
                    self.reachable[block] = false;
                    self.initialized[block] = false;
                    self.entry_envs[block].clear();
                    self.exit_envs[block].clear();
                    enqueue_succs(cfg, block, &mut worklist, &mut queued);
                }
                continue;
            };

            if old_initialized {
                revisit_count[block] = revisit_count[block].saturating_add(1);
            }
            if is_loop_header(lpt, block) && revisit_count[block] > LOOP_WIDEN_CAP {
                new_entry = widen_env(func, &self.entry_envs[block], &new_entry);
            }

            let entry_changed = !old_initialized || new_entry != self.entry_envs[block];
            let reachability_changed = !old_reachable;
            if !entry_changed && !reachability_changed {
                continue;
            }

            self.entry_envs[block] = new_entry.clone();
            self.reachable[block] = true;
            self.initialized[block] = true;

            let new_exit = simulate_block_from_entry(func, block, &new_entry);
            let exit_changed = new_exit != self.exit_envs[block];
            if exit_changed {
                self.exit_envs[block] = new_exit;
            }

            if exit_changed || reachability_changed {
                enqueue_succs(cfg, block, &mut worklist, &mut queued);
            }
        }
    }

    pub fn entry_env(&self, block: BlockId) -> &RangeEnv {
        &self.entry_envs[block]
    }

    pub fn exit_env(&self, block: BlockId) -> &RangeEnv {
        &self.exit_envs[block]
    }

    pub fn is_reachable(&self, block: BlockId) -> bool {
        self.reachable[block]
    }
}

impl RangeFact {
    pub fn full_for(ty: Type) -> Self {
        debug_assert!(ty.is_integral());
        Self {
            unsigned: UnsignedInterval {
                lo: U256::zero(),
                hi: unsigned_max(ty),
            },
            signed: SignedInterval {
                lo: signed_min(ty),
                hi: signed_max(ty),
            },
        }
    }

    pub fn singleton(imm: Immediate) -> Self {
        let ty = imm.ty();
        debug_assert!(ty.is_integral());
        let unsigned = imm_to_unsigned(imm);
        let signed = imm.as_i256();
        Self {
            unsigned: UnsignedInterval {
                lo: unsigned,
                hi: unsigned,
            },
            signed: SignedInterval {
                lo: signed,
                hi: signed,
            },
        }
    }

    pub fn is_full_for(&self, ty: Type) -> bool {
        *self == Self::full_for(ty)
    }
}

impl UnsignedInterval {
    fn join(self, other: Self) -> Self {
        Self {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }

    fn intersect(self, other: Self) -> Option<Self> {
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        (lo <= hi).then_some(Self { lo, hi })
    }
}

impl SignedInterval {
    fn join(self, other: Self) -> Self {
        Self {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }

    fn intersect(self, other: Self) -> Option<Self> {
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        (lo <= hi).then_some(Self { lo, hi })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NormalizedCond {
    Constant(bool),
    Compare {
        kind: BinaryInstKind,
        lhs: ValueId,
        rhs: ValueId,
        invert: bool,
    },
    Value {
        value: ValueId,
        invert: bool,
    },
}

pub(crate) fn fact_for_value(func: &Function, env: &RangeEnv, value: ValueId) -> RangeFact {
    let ty = func.dfg.value_ty(value);
    debug_assert!(ty.is_integral());

    if let Some(imm) = func.dfg.value_imm(value) {
        return RangeFact::singleton(imm);
    }

    match func.dfg.value(value) {
        Value::Undef { .. } => RangeFact::full_for(ty),
        _ => env
            .get(&value)
            .copied()
            .unwrap_or_else(|| RangeFact::full_for(ty)),
    }
}

pub(crate) fn exact_immediate(
    func: &Function,
    env: &RangeEnv,
    value: ValueId,
) -> Option<Immediate> {
    if let Some(imm) = func.dfg.value_imm(value) {
        return Some(imm);
    }

    let ty = func.dfg.value_ty(value);
    if !ty.is_integral() {
        return None;
    }

    let fact = env.get(&value).copied()?;
    if fact.unsigned.lo == fact.unsigned.hi {
        let imm = unsigned_imm(fact.unsigned.lo, ty);
        return range_contains_imm(fact, imm).then_some(imm);
    }
    if fact.signed.lo == fact.signed.hi {
        let imm = Immediate::from_i256(fact.signed.lo, ty);
        return range_contains_imm(fact, imm).then_some(imm);
    }
    None
}

pub(crate) fn simulate_block_from_entry(
    func: &Function,
    block: BlockId,
    entry: &RangeEnv,
) -> RangeEnv {
    let mut env = entry.clone();
    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            continue;
        }
        transfer_inst(func, &mut env, inst);
    }
    env
}

pub(crate) fn transfer_inst(func: &Function, env: &mut RangeEnv, inst: InstId) {
    let kind = func.dfg.inst(inst).kind();
    match kind {
        InstClassKind::Cast(kind) => transfer_cast_inst(func, env, inst, kind),
        InstClassKind::Unary(UnaryInstKind::Snego) => transfer_snego_inst(func, env, inst),
        InstClassKind::Unary(UnaryInstKind::Not | UnaryInstKind::IsZero) => {
            transfer_bool_unary_inst(func, env, inst, kind)
        }
        InstClassKind::Binary(kind) => transfer_binary_inst(func, env, inst, kind),
        _ => clear_inst_results(func, env, inst),
    }
}

pub(crate) fn checked_value_fact(
    func: &Function,
    env: &RangeEnv,
    inst: InstId,
) -> Option<RangeFact> {
    let value = func.dfg.inst_result_at(inst, 0)?;
    let ty = func.dfg.value_ty(value);

    match func.dfg.inst(inst).kind() {
        InstClassKind::Unary(UnaryInstKind::Snego) => {
            let args = func.dfg.inst(inst).collect_values();
            let [arg] = args.as_slice() else {
                return None;
            };
            let arg_fact = fact_for_value(func, env, *arg);
            prove_snego(arg_fact, ty)
                .then(|| plain_sub_fact(RangeFact::singleton(Immediate::zero(ty)), arg_fact, ty))
        }
        InstClassKind::Binary(kind) => {
            let args = func.dfg.inst(inst).collect_values();
            let [lhs, rhs] = args.as_slice() else {
                return None;
            };
            let lhs_fact = fact_for_value(func, env, *lhs);
            let rhs_fact = fact_for_value(func, env, *rhs);
            checked_binary_value_fact(kind, lhs_fact, rhs_fact, ty)
        }
        _ => None,
    }
}

fn checked_binary_value_fact(
    kind: BinaryInstKind,
    lhs: RangeFact,
    rhs: RangeFact,
    ty: Type,
) -> Option<RangeFact> {
    let safe = match kind {
        BinaryInstKind::Uaddo => prove_uaddo(lhs, rhs, ty),
        BinaryInstKind::Usubo => prove_usubo(lhs, rhs, ty),
        BinaryInstKind::Umulo => prove_umulo(lhs, rhs, ty),
        BinaryInstKind::Saddo => prove_saddo(lhs, rhs, ty),
        BinaryInstKind::Ssubo => prove_ssubo(lhs, rhs, ty),
        BinaryInstKind::Smulo => prove_smulo(lhs, rhs, ty),
        BinaryInstKind::EvmUdivo => prove_evm_udivo(rhs),
        BinaryInstKind::EvmUmodo => prove_evm_umodo(rhs),
        BinaryInstKind::EvmSdivo => prove_evm_sdivo(lhs, rhs, ty),
        BinaryInstKind::EvmSmodo => prove_evm_smodo(rhs),
        _ => return None,
    };
    if !safe {
        return None;
    }

    Some(match kind {
        BinaryInstKind::Uaddo | BinaryInstKind::Saddo => plain_add_fact(lhs, rhs, ty),
        BinaryInstKind::Usubo | BinaryInstKind::Ssubo => plain_sub_fact(lhs, rhs, ty),
        BinaryInstKind::Umulo | BinaryInstKind::Smulo => plain_mul_fact(lhs, rhs, ty),
        BinaryInstKind::EvmUdivo
        | BinaryInstKind::EvmUmodo
        | BinaryInstKind::EvmSdivo
        | BinaryInstKind::EvmSmodo => RangeFact::full_for(ty),
        _ => unreachable!(),
    })
}

fn enqueue_succs(
    cfg: &ControlFlowGraph,
    block: BlockId,
    worklist: &mut VecDeque<BlockId>,
    queued: &mut SecondaryMap<BlockId, bool>,
) {
    for &succ in cfg.succs_of(block) {
        if !queued[succ] {
            queued[succ] = true;
            worklist.push_back(succ);
        }
    }
}

fn is_loop_header(lpt: &LoopTree, block: BlockId) -> bool {
    lpt.loop_of_block(block)
        .is_some_and(|lp| lpt.loop_header(lp) == block)
}

fn compute_block_entry(
    func: &Function,
    cfg: &ControlFlowGraph,
    block: BlockId,
    entry: BlockId,
    exit_envs: &SecondaryMap<BlockId, RangeEnv>,
    reachable: &SecondaryMap<BlockId, bool>,
) -> Option<RangeEnv> {
    let mut edge_envs = Vec::new();
    for &pred in cfg.preds_of(block) {
        if !reachable[pred] {
            continue;
        }
        let Some(refined) = refine_edge(func, pred, block, &exit_envs[pred]) else {
            continue;
        };
        edge_envs.push((pred, refined));
    }
    let pred_env_index: FxHashMap<_, _> = edge_envs
        .iter()
        .enumerate()
        .map(|(index, (pred, _))| (*pred, index))
        .collect();

    if block != entry && edge_envs.is_empty() {
        return None;
    }

    let mut entry_env = if let Some((_, first)) = edge_envs.first() {
        first.clone()
    } else {
        RangeEnv::default()
    };
    for (_, env) in edge_envs.iter().skip(1) {
        entry_env = join_envs(func, &entry_env, env);
        if entry_env.is_empty() {
            break;
        }
    }

    apply_phi_entry_facts(func, block, &edge_envs, &pred_env_index, &mut entry_env);
    Some(entry_env)
}

fn apply_phi_entry_facts(
    func: &Function,
    block: BlockId,
    edge_envs: &[(BlockId, RangeEnv)],
    pred_env_index: &FxHashMap<BlockId, usize>,
    entry_env: &mut RangeEnv,
) {
    for inst in func.layout.iter_inst(block) {
        if !func.dfg.is_phi(inst) {
            break;
        }

        let Some(result) = func.dfg.inst_result(inst) else {
            continue;
        };
        let ty = func.dfg.value_ty(result);
        if !ty.is_integral() {
            entry_env.remove(&result);
            continue;
        }

        let Some(phi) = func.dfg.cast_phi(inst) else {
            continue;
        };

        let mut joined = None;
        for &(incoming, pred) in phi.args() {
            let Some(&pred_env_index) = pred_env_index.get(&pred) else {
                continue;
            };
            let pred_env = &edge_envs[pred_env_index].1;
            let incoming_fact = fact_for_value(func, pred_env, incoming);
            joined = Some(match joined {
                Some(current) => join_facts(current, incoming_fact, ty),
                None => incoming_fact,
            });
        }

        if let Some(fact) = joined {
            set_env_fact(func, entry_env, result, fact);
        } else {
            entry_env.remove(&result);
        }
    }
}

fn refine_edge(func: &Function, pred: BlockId, succ: BlockId, env: &RangeEnv) -> Option<RangeEnv> {
    let term = func.layout.last_inst_of(pred)?;
    let branch = func.dfg.branch_info(term)?;

    match branch.branch_kind() {
        BranchKind::Jump(jump) => ((*jump.dest() == succ) as u8 == 1).then(|| env.clone()),
        BranchKind::Br(br) => refine_br_edge(func, env, *br.cond(), succ == *br.nz_dest()),
        BranchKind::BrTable(_) => Some(env.clone()),
    }
}

fn refine_br_edge(
    func: &Function,
    env: &RangeEnv,
    cond: ValueId,
    take_true_edge: bool,
) -> Option<RangeEnv> {
    match normalize_condition(func, env, cond) {
        NormalizedCond::Constant(value) => (value == take_true_edge).then(|| env.clone()),
        NormalizedCond::Value { value, invert } => {
            let effective = take_true_edge ^ invert;
            if let Some(value) = exact_bool(func, env, value) {
                (value == effective).then(|| env.clone())
            } else if func.dfg.value_ty(value) == Type::I1 {
                let mut refined = env.clone();
                set_env_fact(
                    func,
                    &mut refined,
                    value,
                    RangeFact::singleton(Immediate::from(effective)),
                );
                Some(refined)
            } else {
                Some(env.clone())
            }
        }
        NormalizedCond::Compare {
            kind,
            lhs,
            rhs,
            invert,
        } => refine_compare_edge(func, env, kind, lhs, rhs, take_true_edge ^ invert),
    }
}

fn normalize_condition(func: &Function, env: &RangeEnv, mut value: ValueId) -> NormalizedCond {
    let mut invert = false;

    loop {
        if let Some(bool_value) = exact_bool(func, env, value) {
            return NormalizedCond::Constant(bool_value ^ invert);
        }

        let Some(inst) = func.dfg.value_inst(value) else {
            return NormalizedCond::Value { value, invert };
        };

        match func.dfg.inst(inst).kind() {
            InstClassKind::Unary(UnaryInstKind::Not | UnaryInstKind::IsZero) => {
                let args = func.dfg.inst(inst).collect_values();
                let [arg] = args.as_slice() else {
                    return NormalizedCond::Value { value, invert };
                };
                if func.dfg.value_ty(*arg) != Type::I1 {
                    return NormalizedCond::Value { value, invert };
                }
                value = *arg;
                invert = !invert;
            }
            InstClassKind::Binary(BinaryInstKind::Eq | BinaryInstKind::Ne) => {
                let args = func.dfg.inst(inst).collect_values();
                let [lhs, rhs] = args.as_slice() else {
                    return NormalizedCond::Value { value, invert };
                };

                if let Some(next) = normalize_bool_compare(
                    *lhs,
                    *rhs,
                    func.dfg.inst(inst).kind(),
                    &mut invert,
                    func,
                    env,
                ) {
                    value = next;
                    continue;
                }

                let kind = match func.dfg.inst(inst).kind() {
                    InstClassKind::Binary(kind) => kind,
                    _ => unreachable!(),
                };
                let (kind, lhs, rhs) = canonicalize_compare(kind, *lhs, *rhs);
                return NormalizedCond::Compare {
                    kind,
                    lhs,
                    rhs,
                    invert,
                };
            }
            InstClassKind::Binary(kind) if is_compare(kind) => {
                let args = func.dfg.inst(inst).collect_values();
                let [lhs, rhs] = args.as_slice() else {
                    return NormalizedCond::Value { value, invert };
                };
                let (kind, lhs, rhs) = canonicalize_compare(kind, *lhs, *rhs);
                return NormalizedCond::Compare {
                    kind,
                    lhs,
                    rhs,
                    invert,
                };
            }
            _ => return NormalizedCond::Value { value, invert },
        }
    }
}

fn normalize_bool_compare(
    lhs: ValueId,
    rhs: ValueId,
    kind: InstClassKind,
    invert: &mut bool,
    func: &Function,
    env: &RangeEnv,
) -> Option<ValueId> {
    let InstClassKind::Binary(kind) = kind else {
        return None;
    };

    let rhs_bool = exact_bool(func, env, rhs);
    if func.dfg.value_ty(lhs) == Type::I1
        && let Some(rhs_bool) = rhs_bool
    {
        *invert ^= matches!(
            (kind, rhs_bool),
            (BinaryInstKind::Eq, false) | (BinaryInstKind::Ne, true)
        );
        return Some(lhs);
    }

    let lhs_bool = exact_bool(func, env, lhs);
    if func.dfg.value_ty(rhs) == Type::I1
        && let Some(lhs_bool) = lhs_bool
    {
        *invert ^= matches!(
            (kind, lhs_bool),
            (BinaryInstKind::Eq, false) | (BinaryInstKind::Ne, true)
        );
        return Some(rhs);
    }

    None
}

fn refine_compare_edge(
    func: &Function,
    env: &RangeEnv,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    compare_truth: bool,
) -> Option<RangeEnv> {
    if !compare_truth {
        return match kind {
            BinaryInstKind::Eq => {
                refine_compare_edge(func, env, BinaryInstKind::Ne, lhs, rhs, true)
            }
            BinaryInstKind::Ne => {
                refine_compare_edge(func, env, BinaryInstKind::Eq, lhs, rhs, true)
            }
            _ => refine_compare_edge_impl(func, env, kind, lhs, rhs, compare_truth),
        };
    }

    refine_compare_edge_impl(func, env, kind, lhs, rhs, compare_truth)
}

fn refine_compare_edge_impl(
    func: &Function,
    env: &RangeEnv,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    compare_truth: bool,
) -> Option<RangeEnv> {
    if let Some(value) = compare_truth_in_env(func, env, kind, lhs, rhs) {
        return (value == compare_truth).then(|| env.clone());
    }

    let ty = func.dfg.value_ty(lhs);
    if !ty.is_integral() || func.dfg.value_ty(rhs) != ty {
        return Some(env.clone());
    }

    let lhs_fact = fact_for_value(func, env, lhs);
    let rhs_fact = fact_for_value(func, env, rhs);
    let mut refined = env.clone();

    match kind {
        BinaryInstKind::Lt => {
            let (lhs_interval, rhs_interval) =
                refine_unsigned_lt(lhs_fact.unsigned, rhs_fact.unsigned, compare_truth)?;
            set_env_unsigned(func, &mut refined, lhs, lhs_fact, lhs_interval);
            set_env_unsigned(func, &mut refined, rhs, rhs_fact, rhs_interval);
        }
        BinaryInstKind::Le => {
            let (lhs_interval, rhs_interval) =
                refine_unsigned_le(lhs_fact.unsigned, rhs_fact.unsigned, compare_truth)?;
            set_env_unsigned(func, &mut refined, lhs, lhs_fact, lhs_interval);
            set_env_unsigned(func, &mut refined, rhs, rhs_fact, rhs_interval);
        }
        BinaryInstKind::Slt => {
            let (lhs_interval, rhs_interval) =
                refine_signed_lt(lhs_fact.signed, rhs_fact.signed, compare_truth)?;
            set_env_signed(func, &mut refined, lhs, lhs_fact, lhs_interval);
            set_env_signed(func, &mut refined, rhs, rhs_fact, rhs_interval);
        }
        BinaryInstKind::Sle => {
            let (lhs_interval, rhs_interval) =
                refine_signed_le(lhs_fact.signed, rhs_fact.signed, compare_truth)?;
            set_env_signed(func, &mut refined, lhs, lhs_fact, lhs_interval);
            set_env_signed(func, &mut refined, rhs, rhs_fact, rhs_interval);
        }
        BinaryInstKind::Eq => {
            if compare_truth {
                let unsigned = lhs_fact.unsigned.intersect(rhs_fact.unsigned)?;
                let signed = lhs_fact.signed.intersect(rhs_fact.signed)?;
                set_env_fact(func, &mut refined, lhs, RangeFact { unsigned, signed });
                set_env_fact(func, &mut refined, rhs, RangeFact { unsigned, signed });
            }
        }
        BinaryInstKind::Ne => {
            if compare_truth {
                refine_not_equal_constant_edge(func, &mut refined, lhs, lhs_fact, rhs, rhs_fact);
                refine_not_equal_constant_edge(func, &mut refined, rhs, rhs_fact, lhs, lhs_fact);
            }
        }
        _ => {}
    }

    Some(refined)
}

fn refine_not_equal_constant_edge(
    func: &Function,
    env: &mut RangeEnv,
    value: ValueId,
    value_fact: RangeFact,
    other: ValueId,
    _other_fact: RangeFact,
) {
    let Some(imm) = exact_immediate(func, env, other) else {
        return;
    };
    let ty = imm.ty();
    if !ty.is_integral() {
        return;
    }

    let unsigned = imm_to_unsigned(imm);
    let signed = imm.as_i256();
    let mut updated = value_fact;

    if updated.unsigned.lo == unsigned && updated.unsigned.lo < updated.unsigned.hi {
        updated.unsigned.lo += U256::one();
    } else if updated.unsigned.hi == unsigned && updated.unsigned.lo < updated.unsigned.hi {
        updated.unsigned.hi -= U256::one();
    }

    if updated.signed.lo == signed && updated.signed.lo < updated.signed.hi {
        updated.signed.lo = updated.signed.lo.overflowing_add(I256::one()).0;
    } else if updated.signed.hi == signed && updated.signed.lo < updated.signed.hi {
        updated.signed.hi = updated.signed.hi.overflowing_sub(I256::one()).0;
    }

    set_env_fact(func, env, value, updated);
}

fn refine_unsigned_lt(
    lhs: UnsignedInterval,
    rhs: UnsignedInterval,
    compare_truth: bool,
) -> Option<(UnsignedInterval, UnsignedInterval)> {
    if compare_truth {
        let lhs_hi = if rhs.hi == U256::zero() {
            return None;
        } else {
            lhs.hi.min(rhs.hi - U256::one())
        };
        let rhs_lo = rhs.lo.max(lhs.lo + U256::one());
        (lhs.lo <= lhs_hi && rhs_lo <= rhs.hi).then_some((
            UnsignedInterval {
                lo: lhs.lo,
                hi: lhs_hi,
            },
            UnsignedInterval {
                lo: rhs_lo,
                hi: rhs.hi,
            },
        ))
    } else {
        let lhs_lo = lhs.lo.max(rhs.lo);
        let rhs_hi = rhs.hi.min(lhs.hi);
        (lhs_lo <= lhs.hi && rhs.lo <= rhs_hi).then_some((
            UnsignedInterval {
                lo: lhs_lo,
                hi: lhs.hi,
            },
            UnsignedInterval {
                lo: rhs.lo,
                hi: rhs_hi,
            },
        ))
    }
}

fn refine_unsigned_le(
    lhs: UnsignedInterval,
    rhs: UnsignedInterval,
    compare_truth: bool,
) -> Option<(UnsignedInterval, UnsignedInterval)> {
    if compare_truth {
        let lhs_hi = lhs.hi.min(rhs.hi);
        let rhs_lo = rhs.lo.max(lhs.lo);
        (lhs.lo <= lhs_hi && rhs_lo <= rhs.hi).then_some((
            UnsignedInterval {
                lo: lhs.lo,
                hi: lhs_hi,
            },
            UnsignedInterval {
                lo: rhs_lo,
                hi: rhs.hi,
            },
        ))
    } else {
        let lhs_lo = lhs.lo.max(rhs.lo + U256::one());
        if lhs.hi == U256::zero() {
            return None;
        }
        let rhs_hi = rhs.hi.min(lhs.hi - U256::one());
        (lhs_lo <= lhs.hi && rhs.lo <= rhs_hi).then_some((
            UnsignedInterval {
                lo: lhs_lo,
                hi: lhs.hi,
            },
            UnsignedInterval {
                lo: rhs.lo,
                hi: rhs_hi,
            },
        ))
    }
}

fn refine_signed_lt(
    lhs: SignedInterval,
    rhs: SignedInterval,
    compare_truth: bool,
) -> Option<(SignedInterval, SignedInterval)> {
    if compare_truth {
        let rhs_hi_minus_one = rhs.hi.overflowing_sub(I256::one()).0;
        let lhs_hi = lhs.hi.min(rhs_hi_minus_one);
        let rhs_lo = rhs.lo.max(lhs.lo.overflowing_add(I256::one()).0);
        (lhs.lo <= lhs_hi && rhs_lo <= rhs.hi).then_some((
            SignedInterval {
                lo: lhs.lo,
                hi: lhs_hi,
            },
            SignedInterval {
                lo: rhs_lo,
                hi: rhs.hi,
            },
        ))
    } else {
        let lhs_lo = lhs.lo.max(rhs.lo);
        let rhs_hi = rhs.hi.min(lhs.hi);
        (lhs_lo <= lhs.hi && rhs.lo <= rhs_hi).then_some((
            SignedInterval {
                lo: lhs_lo,
                hi: lhs.hi,
            },
            SignedInterval {
                lo: rhs.lo,
                hi: rhs_hi,
            },
        ))
    }
}

fn refine_signed_le(
    lhs: SignedInterval,
    rhs: SignedInterval,
    compare_truth: bool,
) -> Option<(SignedInterval, SignedInterval)> {
    if compare_truth {
        let lhs_hi = lhs.hi.min(rhs.hi);
        let rhs_lo = rhs.lo.max(lhs.lo);
        (lhs.lo <= lhs_hi && rhs_lo <= rhs.hi).then_some((
            SignedInterval {
                lo: lhs.lo,
                hi: lhs_hi,
            },
            SignedInterval {
                lo: rhs_lo,
                hi: rhs.hi,
            },
        ))
    } else {
        let lhs_lo = lhs.lo.max(rhs.lo.overflowing_add(I256::one()).0);
        let rhs_hi = rhs.hi.min(lhs.hi.overflowing_sub(I256::one()).0);
        (lhs_lo <= lhs.hi && rhs.lo <= rhs_hi).then_some((
            SignedInterval {
                lo: lhs_lo,
                hi: lhs.hi,
            },
            SignedInterval {
                lo: rhs.lo,
                hi: rhs_hi,
            },
        ))
    }
}

fn compare_truth_in_env(
    func: &Function,
    env: &RangeEnv,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<bool> {
    let ty = func.dfg.value_ty(lhs);
    if !ty.is_integral() || func.dfg.value_ty(rhs) != ty {
        return None;
    }

    let lhs_fact = fact_for_value(func, env, lhs);
    let rhs_fact = fact_for_value(func, env, rhs);

    match kind {
        BinaryInstKind::Lt => {
            if lhs_fact.unsigned.hi < rhs_fact.unsigned.lo {
                Some(true)
            } else if lhs_fact.unsigned.lo >= rhs_fact.unsigned.hi {
                Some(false)
            } else {
                None
            }
        }
        BinaryInstKind::Le => {
            if lhs_fact.unsigned.hi <= rhs_fact.unsigned.lo {
                Some(true)
            } else if lhs_fact.unsigned.lo > rhs_fact.unsigned.hi {
                Some(false)
            } else {
                None
            }
        }
        BinaryInstKind::Slt => {
            if lhs_fact.signed.hi < rhs_fact.signed.lo {
                Some(true)
            } else if lhs_fact.signed.lo >= rhs_fact.signed.hi {
                Some(false)
            } else {
                None
            }
        }
        BinaryInstKind::Sle => {
            if lhs_fact.signed.hi <= rhs_fact.signed.lo {
                Some(true)
            } else if lhs_fact.signed.lo > rhs_fact.signed.hi {
                Some(false)
            } else {
                None
            }
        }
        BinaryInstKind::Eq => {
            if let (Some(lhs_imm), Some(rhs_imm)) = (
                exact_immediate(func, env, lhs),
                exact_immediate(func, env, rhs),
            ) {
                return Some(lhs_imm == rhs_imm);
            }

            if lhs_fact.unsigned.intersect(rhs_fact.unsigned).is_none()
                || lhs_fact.signed.intersect(rhs_fact.signed).is_none()
            {
                Some(false)
            } else {
                None
            }
        }
        BinaryInstKind::Ne => {
            compare_truth_in_env(func, env, BinaryInstKind::Eq, lhs, rhs).map(|v| !v)
        }
        _ => None,
    }
}

fn transfer_cast_inst(func: &Function, env: &mut RangeEnv, inst: InstId, kind: CastInstKind) {
    let Some(result) = func.dfg.inst_result(inst) else {
        return;
    };
    let ty = func.dfg.value_ty(result);
    let args = func.dfg.inst(inst).collect_values();
    let [arg] = args.as_slice() else {
        clear_inst_results(func, env, inst);
        return;
    };
    let arg_ty = func.dfg.value_ty(*arg);
    if !ty.is_integral() || !arg_ty.is_integral() {
        clear_inst_results(func, env, inst);
        return;
    }

    let src = fact_for_value(func, env, *arg);
    let fact = match kind {
        CastInstKind::Zext => zext_fact(src, ty),
        CastInstKind::Sext => sext_fact(src, ty),
        CastInstKind::Trunc => trunc_fact(src, ty),
        CastInstKind::Bitcast | CastInstKind::IntToPtr | CastInstKind::PtrToInt => {
            RangeFact::full_for(ty)
        }
    };
    set_env_fact(func, env, result, fact);
}

fn transfer_snego_inst(func: &Function, env: &mut RangeEnv, inst: InstId) {
    let Some(value_result) = func.dfg.inst_result_at(inst, 0) else {
        clear_inst_results(func, env, inst);
        return;
    };
    let Some(overflow_result) = func.dfg.inst_result_at(inst, 1) else {
        clear_inst_results(func, env, inst);
        return;
    };
    let ty = func.dfg.value_ty(value_result);
    let args = func.dfg.inst(inst).collect_values();
    let [arg] = args.as_slice() else {
        clear_inst_results(func, env, inst);
        return;
    };
    let arg_fact = fact_for_value(func, env, *arg);

    if prove_snego(arg_fact, ty) {
        let zero = RangeFact::singleton(Immediate::zero(ty));
        set_env_fact(func, env, value_result, plain_sub_fact(zero, arg_fact, ty));
        set_env_fact(
            func,
            env,
            overflow_result,
            RangeFact::singleton(Immediate::from(false)),
        );
    } else {
        set_env_fact(func, env, value_result, RangeFact::full_for(ty));
        set_env_fact(func, env, overflow_result, RangeFact::full_for(Type::I1));
    }
}

fn transfer_bool_unary_inst(
    func: &Function,
    env: &mut RangeEnv,
    inst: InstId,
    kind: InstClassKind,
) {
    let Some(result) = func.dfg.inst_result(inst) else {
        return;
    };
    let args = func.dfg.inst(inst).collect_values();
    let [arg] = args.as_slice() else {
        return;
    };

    if func.dfg.value_ty(*arg) != Type::I1 {
        env.remove(&result);
        return;
    }

    let exact = exact_bool(func, env, *arg);
    let value = match (kind, exact) {
        (InstClassKind::Unary(UnaryInstKind::Not | UnaryInstKind::IsZero), Some(value)) => {
            Some(!value)
        }
        _ => None,
    };

    if let Some(value) = value {
        set_env_fact(
            func,
            env,
            result,
            RangeFact::singleton(Immediate::from(value)),
        );
    } else {
        env.remove(&result);
    }
}

fn transfer_binary_inst(func: &Function, env: &mut RangeEnv, inst: InstId, kind: BinaryInstKind) {
    match kind {
        BinaryInstKind::Add => transfer_plain_binary(func, env, inst, plain_add_fact),
        BinaryInstKind::Sub => transfer_plain_binary(func, env, inst, plain_sub_fact),
        BinaryInstKind::Mul => transfer_plain_binary(func, env, inst, plain_mul_fact),
        BinaryInstKind::Uaddo
        | BinaryInstKind::Usubo
        | BinaryInstKind::Umulo
        | BinaryInstKind::Saddo
        | BinaryInstKind::Ssubo
        | BinaryInstKind::Smulo
        | BinaryInstKind::EvmUdivo
        | BinaryInstKind::EvmUmodo
        | BinaryInstKind::EvmSdivo
        | BinaryInstKind::EvmSmodo => transfer_checked_binary(func, env, inst, kind),
        kind if is_compare(kind) => transfer_compare_inst(func, env, inst, kind),
        _ => clear_inst_results(func, env, inst),
    }
}

fn transfer_plain_binary(
    func: &Function,
    env: &mut RangeEnv,
    inst: InstId,
    transfer: fn(RangeFact, RangeFact, Type) -> RangeFact,
) {
    let Some(result) = func.dfg.inst_result(inst) else {
        return;
    };
    let args = func.dfg.inst(inst).collect_values();
    let [lhs, rhs] = args.as_slice() else {
        return;
    };
    let ty = func.dfg.value_ty(result);
    if !ty.is_integral() {
        env.remove(&result);
        return;
    }

    let lhs_fact = fact_for_value(func, env, *lhs);
    let rhs_fact = fact_for_value(func, env, *rhs);
    set_env_fact(func, env, result, transfer(lhs_fact, rhs_fact, ty));
}

fn transfer_checked_binary(
    func: &Function,
    env: &mut RangeEnv,
    inst: InstId,
    kind: BinaryInstKind,
) {
    let Some(value_result) = func.dfg.inst_result_at(inst, 0) else {
        clear_inst_results(func, env, inst);
        return;
    };
    let Some(overflow_result) = func.dfg.inst_result_at(inst, 1) else {
        clear_inst_results(func, env, inst);
        return;
    };
    let ty = func.dfg.value_ty(value_result);
    let args = func.dfg.inst(inst).collect_values();
    let [lhs, rhs] = args.as_slice() else {
        clear_inst_results(func, env, inst);
        return;
    };
    let lhs_fact = fact_for_value(func, env, *lhs);
    let rhs_fact = fact_for_value(func, env, *rhs);

    if let Some(fact) = checked_binary_value_fact(kind, lhs_fact, rhs_fact, ty) {
        set_env_fact(func, env, value_result, fact);
        set_env_fact(
            func,
            env,
            overflow_result,
            RangeFact::singleton(Immediate::from(false)),
        );
    } else {
        set_env_fact(func, env, value_result, RangeFact::full_for(ty));
        set_env_fact(func, env, overflow_result, RangeFact::full_for(Type::I1));
    }
}

fn transfer_compare_inst(func: &Function, env: &mut RangeEnv, inst: InstId, kind: BinaryInstKind) {
    let Some(result) = func.dfg.inst_result(inst) else {
        return;
    };
    let args = func.dfg.inst(inst).collect_values();
    let [lhs, rhs] = args.as_slice() else {
        return;
    };

    if let Some(value) = compare_truth_in_env(func, env, kind, *lhs, *rhs) {
        set_env_fact(
            func,
            env,
            result,
            RangeFact::singleton(Immediate::from(value)),
        );
    } else {
        env.remove(&result);
    }
}

fn clear_inst_results(func: &Function, env: &mut RangeEnv, inst: InstId) {
    for &result in func.dfg.inst_results(inst) {
        env.remove(&result);
    }
}

fn zext_fact(src: RangeFact, _dst_ty: Type) -> RangeFact {
    let unsigned = UnsignedInterval {
        lo: src.unsigned.lo,
        hi: src.unsigned.hi,
    };
    let signed = SignedInterval {
        lo: I256::zero(),
        hi: I256::from(src.unsigned.hi),
    };
    RangeFact { unsigned, signed }
}

fn sext_fact(src: RangeFact, dst_ty: Type) -> RangeFact {
    let signed = SignedInterval {
        lo: src.signed.lo,
        hi: src.signed.hi,
    };
    let unsigned = if src.signed.hi < I256::zero() {
        UnsignedInterval {
            lo: signed_to_unsigned(src.signed.lo, dst_ty),
            hi: signed_to_unsigned(src.signed.hi, dst_ty),
        }
    } else if src.signed.lo >= I256::zero() {
        UnsignedInterval {
            lo: I256::zero().to_u256(),
            hi: I256::from(src.signed.hi.to_u256()).to_u256(),
        }
    } else {
        return RangeFact {
            unsigned: UnsignedInterval {
                lo: U256::zero(),
                hi: unsigned_max(dst_ty),
            },
            signed,
        };
    };

    RangeFact { unsigned, signed }
}

fn trunc_fact(src: RangeFact, dst_ty: Type) -> RangeFact {
    let mut fact = RangeFact::full_for(dst_ty);

    if src.unsigned.hi <= unsigned_max(dst_ty) {
        fact.unsigned = UnsignedInterval {
            lo: src.unsigned.lo,
            hi: src.unsigned.hi,
        };
    }
    if src.signed.lo >= signed_min(dst_ty) && src.signed.hi <= signed_max(dst_ty) {
        fact.signed = SignedInterval {
            lo: src.signed.lo,
            hi: src.signed.hi,
        };
    }

    fact
}

fn plain_add_fact(lhs: RangeFact, rhs: RangeFact, ty: Type) -> RangeFact {
    let full = RangeFact::full_for(ty);
    let unsigned = if !unsigned_add_overflow(lhs.unsigned.hi, rhs.unsigned.hi, ty) {
        UnsignedInterval {
            lo: unsigned_add(lhs.unsigned.lo, rhs.unsigned.lo, ty).0,
            hi: unsigned_add(lhs.unsigned.hi, rhs.unsigned.hi, ty).0,
        }
    } else {
        full.unsigned
    };
    let signed = if !signed_add_overflow(lhs.signed.lo, rhs.signed.lo, ty)
        && !signed_add_overflow(lhs.signed.hi, rhs.signed.hi, ty)
    {
        SignedInterval {
            lo: signed_add(lhs.signed.lo, rhs.signed.lo, ty).0,
            hi: signed_add(lhs.signed.hi, rhs.signed.hi, ty).0,
        }
    } else {
        full.signed
    };
    RangeFact { unsigned, signed }
}

fn plain_sub_fact(lhs: RangeFact, rhs: RangeFact, ty: Type) -> RangeFact {
    let full = RangeFact::full_for(ty);
    let unsigned = if !unsigned_sub_overflow(lhs.unsigned.lo, rhs.unsigned.hi, ty) {
        UnsignedInterval {
            lo: unsigned_sub(lhs.unsigned.lo, rhs.unsigned.hi, ty).0,
            hi: unsigned_sub(lhs.unsigned.hi, rhs.unsigned.lo, ty).0,
        }
    } else {
        full.unsigned
    };
    let signed = if !signed_sub_overflow(lhs.signed.lo, rhs.signed.hi, ty)
        && !signed_sub_overflow(lhs.signed.hi, rhs.signed.lo, ty)
    {
        SignedInterval {
            lo: signed_sub(lhs.signed.lo, rhs.signed.hi, ty).0,
            hi: signed_sub(lhs.signed.hi, rhs.signed.lo, ty).0,
        }
    } else {
        full.signed
    };
    RangeFact { unsigned, signed }
}

fn plain_mul_fact(lhs: RangeFact, rhs: RangeFact, ty: Type) -> RangeFact {
    let full = RangeFact::full_for(ty);
    let unsigned = if !unsigned_mul_overflow(lhs.unsigned.hi, rhs.unsigned.hi, ty) {
        UnsignedInterval {
            lo: unsigned_mul(lhs.unsigned.lo, rhs.unsigned.lo, ty).0,
            hi: unsigned_mul(lhs.unsigned.hi, rhs.unsigned.hi, ty).0,
        }
    } else {
        full.unsigned
    };
    let signed = if let Some(corners) = signed_mul_corners(lhs.signed, rhs.signed, ty) {
        SignedInterval {
            lo: *corners.iter().min().unwrap(),
            hi: *corners.iter().max().unwrap(),
        }
    } else {
        full.signed
    };
    RangeFact { unsigned, signed }
}

fn signed_mul_corners(lhs: SignedInterval, rhs: SignedInterval, ty: Type) -> Option<[I256; 4]> {
    let corners = [
        (lhs.lo, rhs.lo),
        (lhs.lo, rhs.hi),
        (lhs.hi, rhs.lo),
        (lhs.hi, rhs.hi),
    ];
    let mut values = [I256::zero(); 4];
    for (idx, (a, b)) in corners.into_iter().enumerate() {
        if signed_mul_overflow(a, b, ty) {
            return None;
        }
        values[idx] = Immediate::from_i256(a, ty)
            .overflowing_smul(Immediate::from_i256(b, ty))
            .0
            .as_i256();
    }
    Some(values)
}

fn prove_uaddo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    !unsigned_add_overflow(lhs.unsigned.hi, rhs.unsigned.hi, ty)
}

fn prove_usubo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    !unsigned_sub_overflow(lhs.unsigned.lo, rhs.unsigned.hi, ty)
}

fn prove_umulo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    !unsigned_mul_overflow(lhs.unsigned.hi, rhs.unsigned.hi, ty)
}

fn prove_saddo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    !signed_add_overflow(lhs.signed.lo, rhs.signed.lo, ty)
        && !signed_add_overflow(lhs.signed.hi, rhs.signed.hi, ty)
}

fn prove_ssubo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    !signed_sub_overflow(lhs.signed.lo, rhs.signed.hi, ty)
        && !signed_sub_overflow(lhs.signed.hi, rhs.signed.lo, ty)
}

fn prove_smulo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    signed_mul_corners(lhs.signed, rhs.signed, ty).is_some()
}

fn prove_snego(arg: RangeFact, ty: Type) -> bool {
    !contains_signed(arg.signed, signed_min(ty))
}

fn prove_evm_udivo(rhs: RangeFact) -> bool {
    rhs.unsigned.lo > U256::zero()
}

fn prove_evm_umodo(rhs: RangeFact) -> bool {
    rhs.unsigned.lo > U256::zero()
}

fn prove_evm_sdivo(lhs: RangeFact, rhs: RangeFact, ty: Type) -> bool {
    if contains_signed(rhs.signed, I256::zero()) {
        return false;
    }
    !(contains_signed(lhs.signed, signed_min(ty)) && contains_signed(rhs.signed, -I256::one()))
}

fn prove_evm_smodo(rhs: RangeFact) -> bool {
    !contains_signed(rhs.signed, I256::zero())
}

fn unsigned_add_overflow(lhs: U256, rhs: U256, ty: Type) -> bool {
    unsigned_add(lhs, rhs, ty).1
}

fn unsigned_sub_overflow(lhs: U256, rhs: U256, ty: Type) -> bool {
    unsigned_sub(lhs, rhs, ty).1
}

fn unsigned_mul_overflow(lhs: U256, rhs: U256, ty: Type) -> bool {
    unsigned_mul(lhs, rhs, ty).1
}

fn signed_add_overflow(lhs: I256, rhs: I256, ty: Type) -> bool {
    signed_add(lhs, rhs, ty).1
}

fn signed_sub_overflow(lhs: I256, rhs: I256, ty: Type) -> bool {
    signed_sub(lhs, rhs, ty).1
}

fn signed_mul_overflow(lhs: I256, rhs: I256, ty: Type) -> bool {
    Immediate::from_i256(lhs, ty)
        .overflowing_smul(Immediate::from_i256(rhs, ty))
        .1
}

fn set_env_unsigned(
    func: &Function,
    env: &mut RangeEnv,
    value: ValueId,
    old: RangeFact,
    unsigned: UnsignedInterval,
) {
    set_env_fact(
        func,
        env,
        value,
        RangeFact {
            unsigned,
            signed: old.signed,
        },
    );
}

fn set_env_signed(
    func: &Function,
    env: &mut RangeEnv,
    value: ValueId,
    old: RangeFact,
    signed: SignedInterval,
) {
    set_env_fact(
        func,
        env,
        value,
        RangeFact {
            unsigned: old.unsigned,
            signed,
        },
    );
}

fn set_env_fact(func: &Function, env: &mut RangeEnv, value: ValueId, fact: RangeFact) {
    let ty = func.dfg.value_ty(value);
    if !ty.is_integral() || matches!(func.dfg.value(value), Value::Immediate { .. }) {
        return;
    }
    if fact.is_full_for(ty) {
        env.remove(&value);
    } else {
        env.insert(value, fact);
    }
}

fn join_envs(func: &Function, lhs: &RangeEnv, rhs: &RangeEnv) -> RangeEnv {
    let mut joined = RangeEnv::default();
    let (smaller, larger) = if lhs.len() <= rhs.len() {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    };

    for (&value, &smaller_fact) in smaller {
        let Some(&larger_fact) = larger.get(&value) else {
            continue;
        };
        let ty = func.dfg.value_ty(value);
        if !ty.is_integral() {
            continue;
        }
        let fact = join_facts(smaller_fact, larger_fact, ty);
        if !fact.is_full_for(ty) {
            joined.insert(value, fact);
        }
    }
    joined
}

fn widen_env(func: &Function, old: &RangeEnv, new: &RangeEnv) -> RangeEnv {
    let mut widened = RangeEnv::default();
    let (smaller, larger) = if old.len() <= new.len() {
        (old, new)
    } else {
        (new, old)
    };

    for &value in smaller.keys() {
        if !larger.contains_key(&value) {
            continue;
        }
        let ty = func.dfg.value_ty(value);
        if !ty.is_integral() {
            continue;
        }
        let old_fact = old[&value];
        let new_fact = new[&value];
        let mut widened_fact = old_fact;

        if new_fact.unsigned.lo < old_fact.unsigned.lo {
            widened_fact.unsigned.lo = U256::zero();
        }
        if new_fact.unsigned.hi > old_fact.unsigned.hi {
            widened_fact.unsigned.hi = unsigned_max(ty);
        }
        if new_fact.signed.lo < old_fact.signed.lo {
            widened_fact.signed.lo = signed_min(ty);
        }
        if new_fact.signed.hi > old_fact.signed.hi {
            widened_fact.signed.hi = signed_max(ty);
        }

        if !widened_fact.is_full_for(ty) {
            widened.insert(value, widened_fact);
        }
    }
    widened
}

fn join_facts(lhs: RangeFact, rhs: RangeFact, _ty: Type) -> RangeFact {
    RangeFact {
        unsigned: lhs.unsigned.join(rhs.unsigned),
        signed: lhs.signed.join(rhs.signed),
    }
}

fn exact_bool(func: &Function, env: &RangeEnv, value: ValueId) -> Option<bool> {
    let imm = exact_immediate(func, env, value)?;
    (imm.ty() == Type::I1).then(|| !imm.is_zero())
}

fn is_compare(kind: BinaryInstKind) -> bool {
    matches!(
        kind,
        BinaryInstKind::Lt
            | BinaryInstKind::Gt
            | BinaryInstKind::Slt
            | BinaryInstKind::Sgt
            | BinaryInstKind::Le
            | BinaryInstKind::Ge
            | BinaryInstKind::Sle
            | BinaryInstKind::Sge
            | BinaryInstKind::Eq
            | BinaryInstKind::Ne
    )
}

fn canonicalize_compare(
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> (BinaryInstKind, ValueId, ValueId) {
    match kind {
        BinaryInstKind::Gt => (BinaryInstKind::Lt, rhs, lhs),
        BinaryInstKind::Ge => (BinaryInstKind::Le, rhs, lhs),
        BinaryInstKind::Sgt => (BinaryInstKind::Slt, rhs, lhs),
        BinaryInstKind::Sge => (BinaryInstKind::Sle, rhs, lhs),
        _ => (kind, lhs, rhs),
    }
}

fn range_contains_imm(fact: RangeFact, imm: Immediate) -> bool {
    let unsigned = imm_to_unsigned(imm);
    let signed = imm.as_i256();
    fact.unsigned.lo <= unsigned
        && unsigned <= fact.unsigned.hi
        && fact.signed.lo <= signed
        && signed <= fact.signed.hi
}

fn contains_signed(interval: SignedInterval, value: I256) -> bool {
    interval.lo <= value && value <= interval.hi
}

fn signed_to_unsigned(value: I256, ty: Type) -> U256 {
    imm_to_unsigned(Immediate::from_i256(value, ty))
}

fn imm_to_unsigned(imm: Immediate) -> U256 {
    imm.as_i256().to_u256() & unsigned_max(imm.ty())
}

fn unsigned_imm(value: U256, ty: Type) -> Immediate {
    Immediate::from_i256(I256::from(value), ty)
}

fn unsigned_add(lhs: U256, rhs: U256, ty: Type) -> (U256, bool) {
    let max = unsigned_max(ty);
    let (sum, carry) = lhs.overflowing_add(rhs);
    (sum & max, carry || sum > max)
}

fn unsigned_sub(lhs: U256, rhs: U256, ty: Type) -> (U256, bool) {
    let max = unsigned_max(ty);
    let (diff, borrow) = lhs.overflowing_sub(rhs);
    (diff & max, borrow || lhs < rhs)
}

fn unsigned_mul(lhs: U256, rhs: U256, ty: Type) -> (U256, bool) {
    let max = unsigned_max(ty);
    let (product, carry) = lhs.overflowing_mul(rhs);
    (product & max, carry || product > max)
}

fn signed_add(lhs: I256, rhs: I256, ty: Type) -> (I256, bool) {
    let result = lhs.overflowing_add(rhs).0;
    let overflow = if ty == Type::I256 {
        lhs.is_negative() == rhs.is_negative() && result.is_negative() != lhs.is_negative()
    } else {
        result < signed_min(ty) || result > signed_max(ty)
    };
    (result, overflow)
}

fn signed_sub(lhs: I256, rhs: I256, ty: Type) -> (I256, bool) {
    let result = lhs.overflowing_sub(rhs).0;
    let overflow = if ty == Type::I256 {
        lhs.is_negative() != rhs.is_negative() && result.is_negative() != lhs.is_negative()
    } else {
        result < signed_min(ty) || result > signed_max(ty)
    };
    (result, overflow)
}

fn unsigned_max(ty: Type) -> U256 {
    match type_bits(ty) {
        256 => !U256::zero(),
        bits => (U256::one() << usize::from(bits)) - U256::one(),
    }
}

fn signed_min(ty: Type) -> I256 {
    Immediate::signed_min(ty).as_i256()
}

fn signed_max(ty: Type) -> I256 {
    Immediate::signed_max(ty).as_i256()
}

fn type_bits(ty: Type) -> u16 {
    match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        _ => panic!("non-integral type {ty:?} has no bit width"),
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Function, Type,
        builder::test_util::*,
        inst::{
            arith::Add,
            cmp::{Eq, Le, Lt, Ne},
            control_flow::{Br, Jump, Phi, Return},
        },
        prelude::*,
    };

    use crate::domtree::DomTree;

    use super::*;

    #[test]
    fn interval_helpers_handle_join_intersect_singleton_and_extrema() {
        let joined = UnsignedInterval {
            lo: U256::from(1u8),
            hi: U256::from(4u8),
        }
        .join(UnsignedInterval {
            lo: U256::from(2u8),
            hi: U256::from(9u8),
        });
        assert_eq!(joined.lo, U256::from(1u8));
        assert_eq!(joined.hi, U256::from(9u8));

        let intersected = SignedInterval {
            lo: I256::from(-4i8),
            hi: I256::from(8i8),
        }
        .intersect(SignedInterval {
            lo: I256::from(0i8),
            hi: I256::from(10i8),
        })
        .unwrap();
        assert_eq!(intersected.lo, I256::from(0i8));
        assert_eq!(intersected.hi, I256::from(8i8));

        let singleton = RangeFact::singleton(Immediate::from_i256(I256::from(-1i8), Type::I8));
        assert_eq!(singleton.unsigned.lo, U256::from(255u16));
        assert_eq!(singleton.unsigned.hi, U256::from(255u16));
        assert_eq!(singleton.signed.lo, I256::from(-1i8));
        assert_eq!(singleton.signed.hi, I256::from(-1i8));

        assert_eq!(unsigned_max(Type::I8), U256::from(255u16));
        assert_eq!(signed_min(Type::I8), I256::from(i8::MIN));
        assert_eq!(signed_max(Type::I8), I256::from(i8::MAX));
        assert_eq!(unsigned_max(Type::I256), !U256::zero());
        assert_eq!(signed_min(Type::I256), I256::from(U256::one() << 255));
        assert_eq!(
            signed_max(Type::I256),
            I256::from((U256::one() << 255) - U256::one())
        );
    }

    #[test]
    fn widening_moves_outward_to_type_extrema() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));
        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut old = RangeEnv::default();
            old.insert(
                arg,
                RangeFact {
                    unsigned: UnsignedInterval {
                        lo: U256::from(5u8),
                        hi: U256::from(10u8),
                    },
                    signed: SignedInterval {
                        lo: I256::from(5i8),
                        hi: I256::from(10i8),
                    },
                },
            );

            let mut new = RangeEnv::default();
            new.insert(
                arg,
                RangeFact {
                    unsigned: UnsignedInterval {
                        lo: U256::from(4u8),
                        hi: U256::from(11u8),
                    },
                    signed: SignedInterval {
                        lo: I256::from(4i8),
                        hi: I256::from(11i8),
                    },
                },
            );

            let widened = widen_env(func, &old, &new);
            let fact = widened
                .get(&arg)
                .copied()
                .unwrap_or_else(|| RangeFact::full_for(Type::I8));
            assert_eq!(fact.unsigned.lo, U256::zero());
            assert_eq!(fact.unsigned.hi, U256::from(255u16));
            assert_eq!(fact.signed.lo, I256::from(i8::MIN));
            assert_eq!(fact.signed.hi, I256::from(i8::MAX));
        });
    }

    #[test]
    fn widening_never_shrinks_a_previous_result() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));
        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut old = RangeEnv::default();
            old.insert(
                arg,
                RangeFact {
                    unsigned: UnsignedInterval {
                        lo: U256::zero(),
                        hi: U256::from(10u8),
                    },
                    signed: SignedInterval {
                        lo: I256::zero(),
                        hi: I256::from(10i8),
                    },
                },
            );

            let mut new = RangeEnv::default();
            new.insert(
                arg,
                RangeFact {
                    unsigned: UnsignedInterval {
                        lo: U256::from(5u8),
                        hi: U256::from(8u8),
                    },
                    signed: SignedInterval {
                        lo: I256::from(5i8),
                        hi: I256::from(8i8),
                    },
                },
            );

            let widened = widen_env(func, &old, &new);
            assert_eq!(widened.get(&arg), old.get(&arg));
        });
    }

    #[test]
    fn sparse_joins_and_widens_drop_single_sided_facts() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8, Type::I8], Type::I8);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let &[lhs, rhs] = builder.args() else {
            panic!("expected two args");
        };
        builder.insert_inst_no_result_with(|| Return::new_single(is, lhs));
        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut left = RangeEnv::default();
            left.insert(
                lhs,
                RangeFact {
                    unsigned: UnsignedInterval {
                        lo: U256::from(1u8),
                        hi: U256::from(10u8),
                    },
                    signed: SignedInterval {
                        lo: I256::from(1i8),
                        hi: I256::from(10i8),
                    },
                },
            );
            let mut right = RangeEnv::default();
            right.insert(
                rhs,
                RangeFact {
                    unsigned: UnsignedInterval {
                        lo: U256::from(2u8),
                        hi: U256::from(9u8),
                    },
                    signed: SignedInterval {
                        lo: I256::from(2i8),
                        hi: I256::from(9i8),
                    },
                },
            );

            assert!(join_envs(func, &left, &right).is_empty());
            assert!(widen_env(func, &left, &right).is_empty());
        });
    }

    #[test]
    fn true_edge_of_lt_refines_upper_bound() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b0);
        let arg = builder.args()[0];
        let ten = builder.make_imm_value(10i8);
        let cond = builder.insert_inst_with(|| Lt::new(is, arg, ten), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_single(is, ten));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            let fact = fact_for_value(func, analysis.entry_env(b1), arg);
            assert_eq!(fact.unsigned.lo, U256::zero());
            assert_eq!(fact.unsigned.hi, U256::from(9u8));
        });
    }

    #[test]
    fn true_edge_of_ne_refines_boundary_constant() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();

        builder.switch_to_block(b0);
        let arg = builder.args()[0];
        let ten = builder.make_imm_value(10i8);
        let upper = builder.insert_inst_with(|| Le::new(is, arg, ten), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, upper, b1, b4));

        builder.switch_to_block(b1);
        let zero = builder.make_imm_value(0i8);
        let nonzero = builder.insert_inst_with(|| Ne::new(is, arg, zero), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, nonzero, b2, b3));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));

        builder.switch_to_block(b3);
        builder.insert_inst_no_result_with(|| Return::new_single(is, zero));

        builder.switch_to_block(b4);
        builder.insert_inst_no_result_with(|| Return::new_single(is, ten));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            let fact = fact_for_value(func, analysis.entry_env(b2), arg);
            assert_eq!(fact.unsigned.lo, U256::from(1u8));
            assert_eq!(fact.unsigned.hi, U256::from(10u8));
        });
    }

    #[test]
    fn false_edge_of_le_zero_stays_reachable() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b0);
        let arg = builder.args()[0];
        let zero = builder.make_imm_value(0i8);
        let cond = builder.insert_inst_with(|| Le::new(is, arg, zero), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Return::new_single(is, zero));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            assert!(analysis.is_reachable(b2));
            let fact = fact_for_value(func, analysis.entry_env(b2), arg);
            assert_eq!(fact.unsigned.lo, U256::from(1u8));
            assert_eq!(fact.unsigned.hi, U256::from(255u16));
        });
    }

    #[test]
    fn impossible_edge_is_marked_unreachable() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b0);
        let arg = builder.args()[0];
        let zero = builder.make_imm_value(0i8);
        let cond = builder.insert_inst_with(|| Lt::new(is, arg, zero), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_single(is, zero));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            assert!(!analysis.is_reachable(b1));
            assert!(analysis.is_reachable(b2));
        });
    }

    #[test]
    fn eq_bool_false_normalization_flips_truth() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I1);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b0);
        let arg = builder.args()[0];
        let zero = builder.make_imm_value(false);
        let cond = builder.insert_inst_with(|| Eq::new(is, arg, zero), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_single(is, arg));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            assert_eq!(exact_bool(func, analysis.entry_env(b1), arg), Some(false));
            assert_eq!(exact_bool(func, analysis.entry_env(b2), arg), Some(true));
        });
    }

    #[test]
    fn solver_handles_simple_linear_block() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        builder.switch_to_block(b0);
        let one = builder.make_imm_value(1i8);
        let two = builder.make_imm_value(2i8);
        let sum = builder.insert_inst_with(|| Add::new(is, one, two), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_single(is, sum));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            assert_eq!(
                exact_immediate(func, analysis.exit_env(b0), sum),
                Some(Immediate::from_i256(I256::from(3i8), Type::I8))
            );
        });
    }

    #[test]
    fn solver_handles_diamond_phi_join() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let cond = builder.args()[0];
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        let one = builder.make_imm_value(1i8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b3));

        builder.switch_to_block(b2);
        let five = builder.make_imm_value(5i8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b3));

        builder.switch_to_block(b3);
        let phi = builder.insert_inst_with(|| Phi::new(is, vec![(one, b1), (five, b2)]), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_single(is, phi));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            let fact = fact_for_value(func, analysis.entry_env(b3), phi);
            assert_eq!(fact.unsigned.lo, U256::from(1u8));
            assert_eq!(fact.unsigned.hi, U256::from(5u8));
        });
    }

    #[test]
    fn bounded_loop_converges_without_aggressive_widening() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let zero = builder.make_imm_value(0i8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b1);
        let iter = builder.insert_inst_with(|| Phi::new(is, vec![(zero, b0)]), Type::I8);
        let hundred = builder.make_imm_value(100i8);
        let cond = builder.insert_inst_with(|| Lt::new(is, iter, hundred), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b2, b3));

        builder.switch_to_block(b2);
        let one = builder.make_imm_value(1i8);
        let [next, overflow] = builder.insert_uaddo(iter, one);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));
        builder.append_phi_arg(iter, next, b2);

        builder.switch_to_block(b3);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iter));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            let fact = fact_for_value(func, analysis.entry_env(b2), iter);
            assert_eq!(fact.unsigned.lo, U256::zero());
            assert_eq!(fact.unsigned.hi, U256::from(99u8));
            assert_eq!(
                exact_bool(func, analysis.exit_env(b2), overflow),
                Some(false)
            );
        });
    }

    #[test]
    fn unbounded_loop_terminates_via_widening() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let zero = builder.make_imm_value(0i8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b1);
        let cond = builder.args()[0];
        let iter = builder.insert_inst_with(|| Phi::new(is, vec![(zero, b0)]), Type::I8);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b2, b3));

        builder.switch_to_block(b2);
        let one = builder.make_imm_value(1i8);
        let next = builder.insert_inst_with(|| Add::new(is, iter, one), Type::I8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));
        builder.append_phi_arg(iter, next, b2);

        builder.switch_to_block(b3);
        builder.insert_inst_no_result_with(|| Return::new_single(is, iter));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            let fact = fact_for_value(func, analysis.entry_env(b1), iter);
            assert!(fact.is_full_for(Type::I8));
        });
    }

    #[test]
    fn checked_div_and_negation_set_overflow_false_when_guarded() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8, Type::I8], Type::I8);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();

        builder.switch_to_block(b0);
        let lhs = builder.args()[0];
        let rhs = builder.args()[1];
        let zero = builder.make_imm_value(0i8);
        let rhs_nonzero = builder.insert_inst_with(|| Ne::new(is, rhs, zero), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, rhs_nonzero, b1, b2));

        builder.switch_to_block(b1);
        let [_div, div_ov] = builder.insert_evm_udivo(lhs, rhs);
        let min = builder.make_imm_value(i8::MIN);
        let not_min = builder.insert_inst_with(|| Ne::new(is, lhs, min), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, not_min, b3, b4));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_single(is, zero));

        builder.switch_to_block(b3);
        let [neg, neg_ov] = builder.insert_snego(lhs);
        builder.insert_inst_no_result_with(|| Return::new_single(is, neg));

        builder.switch_to_block(b4);
        builder.insert_inst_no_result_with(|| Return::new_single(is, lhs));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let analysis = compute_analysis(func);
            assert_eq!(exact_bool(func, analysis.exit_env(b1), div_ov), Some(false));
            assert_eq!(exact_bool(func, analysis.exit_env(b3), neg_ov), Some(false));
        });
    }

    fn compute_analysis(func: &Function) -> RangeAnalysis {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let mut domtree = DomTree::new();
        domtree.compute(&cfg);
        let mut lpt = LoopTree::new();
        lpt.compute(&cfg, &domtree);
        let mut analysis = RangeAnalysis::default();
        analysis.compute(func, &cfg, &lpt);
        analysis
    }
}
