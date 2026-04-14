use crate::bitset::BitSet;
use rustc_hash::{FxHashMap, FxHasher};
use sonatina_ir::{I256, Immediate, ValueId};
use std::{
    cmp::Ordering,
    collections::{BinaryHeap, VecDeque},
    hash::Hasher,
    sync::{Mutex, OnceLock},
};

use super::{
    super::{
        StackifyContext,
        sym_stack::{StackItem, SymStack},
    },
    Planner,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Cost {
    pub(super) gas: u32,
    pub(super) bytes: u32,
}

impl Cost {
    pub(super) fn saturating_add(self, rhs: Self) -> Self {
        Self {
            gas: self.gas.saturating_add(rhs.gas),
            bytes: self.bytes.saturating_add(rhs.bytes),
        }
    }
}

impl PartialOrd for Cost {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cost {
    fn cmp(&self, other: &Self) -> Ordering {
        self.gas
            .cmp(&other.gas)
            .then_with(|| self.bytes.cmp(&other.bytes))
    }
}

pub(super) trait CostModel {
    fn cost_pop(&self) -> Cost;
    fn cost_dup(&self, pos: u8) -> Cost;
    fn cost_swap(&self, depth: u8) -> Cost;
    fn cost_push_imm(&self, imm: I256) -> Cost;
    fn cost_load(&self, v: ValueId) -> Cost;
}

#[derive(Clone, Copy, Debug)]
pub(super) struct EstimatedCostModel {
    pub(super) load_cost: Cost,
}

impl Default for EstimatedCostModel {
    fn default() -> Self {
        Self {
            load_cost: Cost { gas: 15, bytes: 7 },
        }
    }
}

impl CostModel for EstimatedCostModel {
    fn cost_pop(&self) -> Cost {
        Cost { gas: 2, bytes: 1 }
    }

    fn cost_dup(&self, _pos: u8) -> Cost {
        Cost { gas: 3, bytes: 1 }
    }

    fn cost_swap(&self, _depth: u8) -> Cost {
        Cost { gas: 3, bytes: 1 }
    }

    fn cost_push_imm(&self, imm: I256) -> Cost {
        if imm.is_zero() {
            // PUSH0
            return Cost { gas: 2, bytes: 1 };
        }

        let n = minimal_push_bytes(imm) as u32;
        let mut cost = Cost {
            gas: 3,
            bytes: 1 + n,
        };

        // Approximate the EVM lowerer's sign-extension behavior for negative literals.
        if imm.is_negative() && n < 32 {
            // PUSH (n-1)
            if n == 1 {
                cost = cost.saturating_add(Cost { gas: 2, bytes: 1 }); // PUSH0
            } else {
                cost = cost.saturating_add(Cost { gas: 3, bytes: 2 }); // PUSH1 <idx>
            }

            // SIGNEXTEND
            cost = cost.saturating_add(Cost { gas: 5, bytes: 1 });
        }

        cost
    }

    fn cost_load(&self, _v: ValueId) -> Cost {
        self.load_cost
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Key {
    Imm(I256),
    Val(ValueId),
}

#[derive(Clone, Copy, Debug)]
pub(super) enum KeyInfo {
    Imm {
        canon: I256,
        rep_vid: ValueId,
        rep_imm: Immediate,
    },
    Val {
        vid: ValueId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Step {
    Pop,
    Dup(u8),
    Swap(u8),
    PushImm(u8),
    LoadVal(u8),
}

#[derive(Clone, Copy, Debug)]
pub(super) struct SearchCfg {
    pub(super) dup_max: usize,
    pub(super) swap_max: usize,
    pub(super) max_len: usize,
    pub(super) max_expansions: usize,
}

#[derive(Clone, Debug)]
pub(super) struct NormalizePlan {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) cost: Cost,
    pub(super) steps: Vec<Step>,
    pub(super) key_infos: Vec<KeyInfo>,
    #[allow(dead_code)]
    pub(super) goal_keys: Vec<u8>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PackedState {
    len: u8,
    data: u128,
}

impl PackedState {
    const EMPTY: Self = Self { len: 0, data: 0 };

    const SLOT_BITS: u32 = 6;
    const SLOT_MASK: u128 = (1u128 << Self::SLOT_BITS) - 1;

    fn from_ids(ids: &[u8]) -> Option<Self> {
        if ids.len() > 21 {
            return None;
        }

        let mut data = 0u128;
        for (idx, &id) in ids.iter().enumerate() {
            debug_assert!(id < 64, "packed id out of range");
            data |= (id as u128) << (Self::SLOT_BITS * idx as u32);
        }

        Some(Self {
            len: ids.len() as u8,
            data,
        })
    }

    fn len(&self) -> usize {
        self.len as usize
    }

    fn get(&self, idx: usize) -> u8 {
        debug_assert!(idx < self.len());
        ((self.data >> (Self::SLOT_BITS * idx as u32)) & Self::SLOT_MASK) as u8
    }

    fn set(&mut self, idx: usize, id: u8) {
        debug_assert!(idx < self.len());
        debug_assert!(id < 64);
        let shift = Self::SLOT_BITS * idx as u32;
        let mask = Self::SLOT_MASK << shift;
        self.data = (self.data & !mask) | ((id as u128) << shift);
    }

    fn pop(self) -> Self {
        debug_assert!(self.len > 0);
        Self {
            len: self.len - 1,
            data: self.data >> Self::SLOT_BITS,
        }
    }

    fn push(self, id: u8) -> Self {
        debug_assert!(id < 64);
        Self {
            len: self.len + 1,
            data: (self.data << Self::SLOT_BITS) | id as u128,
        }
    }

    fn swap(mut self, depth: usize) -> Self {
        debug_assert!(depth > 0);
        debug_assert!(depth < self.len());
        let top = self.get(0);
        let other = self.get(depth);
        self.set(0, other);
        self.set(depth, top);
        self
    }

    fn dup(self, pos: usize) -> Self {
        let id = self.get(pos);
        self.push(id)
    }
}

impl PartialOrd for PackedState {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PackedState {
    fn cmp(&self, other: &Self) -> Ordering {
        self.len
            .cmp(&other.len)
            .then_with(|| self.data.cmp(&other.data))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct QueueEntry {
    f: Cost,
    g: Cost,
    state: PackedState,
}

impl PartialOrd for QueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse ordering for min-heap behavior.
        other
            .f
            .cmp(&self.f)
            .then_with(|| other.g.cmp(&self.g))
            .then_with(|| other.state.cmp(&self.state))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PrepState {
    window: PackedState,
    tail: u64,
    mem: u64,
}

impl PartialOrd for PrepState {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrepState {
    fn cmp(&self, other: &Self) -> Ordering {
        self.window
            .cmp(&other.window)
            .then_with(|| self.tail.cmp(&other.tail))
            .then_with(|| self.mem.cmp(&other.mem))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct PrepQueueEntry {
    f: Cost,
    g: Cost,
    state: PrepState,
}

impl PartialOrd for PrepQueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrepQueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .f
            .cmp(&self.f)
            .then_with(|| other.g.cmp(&self.g))
            .then_with(|| other.state.cmp(&self.state))
    }
}

const NORMALIZE_PLAN_CACHE_CAP: usize = 4096;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PlanCacheKey {
    mode: u8,
    func_ptr: usize,
    dup_max: u8,
    swap_max: u8,
    max_len: u8,
    max_expansions: u32,
    cost_hash: u64,
    start: PackedState,
    goal: PackedState,
    ctx: PackedState,
    ctx_bits0: u64,
    ctx_bits1: u64,
    ctx_bits2: u64,
}

#[derive(Clone, Debug)]
enum PlanCacheVal {
    None,
    Steps(Vec<Step>),
}

struct PlanCache {
    map: FxHashMap<PlanCacheKey, PlanCacheVal>,
    order: VecDeque<PlanCacheKey>,
}

impl PlanCache {
    fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            order: VecDeque::new(),
        }
    }

    fn get(&self, key: &PlanCacheKey) -> Option<&PlanCacheVal> {
        self.map.get(key)
    }

    fn insert(&mut self, key: PlanCacheKey, val: PlanCacheVal) {
        if let Some(existing) = self.map.get_mut(&key) {
            if matches!(existing, PlanCacheVal::None) && matches!(val, PlanCacheVal::Steps(_)) {
                *existing = val;
            }
            return;
        }

        self.map.insert(key, val);
        self.order.push_back(key);

        while self.order.len() > NORMALIZE_PLAN_CACHE_CAP {
            let Some(old) = self.order.pop_front() else {
                break;
            };
            self.map.remove(&old);
        }
    }
}

fn plan_cache() -> &'static Mutex<PlanCache> {
    static CACHE: OnceLock<Mutex<PlanCache>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(PlanCache::new()))
}

fn normalize_search_debug_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        matches!(
            std::env::var("SONATINA_STACKIFY_NORMALIZE_DEBUG")
                .as_deref()
                .ok(),
            Some("1") | Some("true") | Some("yes")
        )
    })
}

fn compute_cost_hash(cost: &impl CostModel, key_infos: &[KeyInfo], cfg: SearchCfg) -> u64 {
    let mut h = FxHasher::default();

    let pop = cost.cost_pop();
    h.write_u32(pop.gas);
    h.write_u32(pop.bytes);

    for pos in 0..cfg.dup_max {
        let c = cost.cost_dup(pos as u8);
        h.write_u32(c.gas);
        h.write_u32(c.bytes);
    }

    for depth in 1..cfg.swap_max {
        let c = cost.cost_swap(depth as u8);
        h.write_u32(c.gas);
        h.write_u32(c.bytes);
    }

    for info in key_infos {
        match *info {
            KeyInfo::Imm { canon, .. } => {
                let c = cost.cost_push_imm(canon);
                h.write_u32(c.gas);
                h.write_u32(c.bytes);
            }
            KeyInfo::Val { vid } => {
                let c = cost.cost_load(vid);
                h.write_u32(c.gas);
                h.write_u32(c.bytes);
            }
        }
    }

    h.finish()
}

fn common_suffix_len(state: PackedState, goal: PackedState) -> usize {
    let n = state.len();
    let m = goal.len();
    let mut k = 0usize;
    while k < n && k < m {
        if state.get(n - 1 - k) != goal.get(m - 1 - k) {
            break;
        }
        k += 1;
    }
    k
}

fn common_suffix_len_keys(cur: &[u8], goal: &[u8]) -> usize {
    let mut k = 0usize;
    while k < cur.len() && k < goal.len() {
        if cur[cur.len() - 1 - k] != goal[goal.len() - 1 - k] {
            break;
        }
        k += 1;
    }
    k
}

fn should_prune(f: Cost, upper_bound: Cost, have_incumbent: bool) -> bool {
    if have_incumbent {
        f >= upper_bound
    } else {
        f > upper_bound
    }
}

pub(super) fn solve_optimal_normalize_plan(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    desired: &[ValueId],
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> Option<NormalizePlan> {
    let debug = normalize_search_debug_enabled();

    if desired.len() > cfg.swap_max {
        if debug {
            eprintln!(
                "normalize_search: reject desired_len={} swap_max={}",
                desired.len(),
                cfg.swap_max
            );
        }
        return None;
    }

    let start_limit = stack.len_above_func_ret();
    if start_limit > cfg.swap_max {
        if debug {
            eprintln!(
                "normalize_search: reject start_len={} swap_max={}",
                start_limit, cfg.swap_max
            );
        }
        return None;
    }

    if cfg.max_len > 21 {
        if debug {
            eprintln!("normalize_search: reject max_len={}", cfg.max_len);
        }
        return None;
    }
    if start_limit > cfg.max_len || desired.len() > cfg.max_len {
        if debug {
            eprintln!(
                "normalize_search: reject bounds start_len={} desired_len={} max_len={}",
                start_limit,
                desired.len(),
                cfg.max_len
            );
        }
        return None;
    }

    let mut key_ids: FxHashMap<Key, u8> = FxHashMap::default();
    let mut key_infos: Vec<KeyInfo> = Vec::new();

    let mut goal_keys: Vec<u8> = Vec::with_capacity(desired.len());
    let mut materializable_imm: Vec<u8> = Vec::new();
    let mut materializable_val: Vec<u8> = Vec::new();
    let mut seen_push: u64 = 0;
    let mut seen_load: u64 = 0;

    for &v in desired {
        let key = canonical_key(ctx, v);
        let kid = intern_key(ctx, key, v, &mut key_ids, &mut key_infos)?;
        goal_keys.push(kid);

        if ctx.func.dfg.value_is_imm(v) {
            if (seen_push & (1u64 << kid)) == 0 {
                seen_push |= 1u64 << kid;
                materializable_imm.push(kid);
            }
        } else if (seen_load & (1u64 << kid)) == 0 {
            seen_load |= 1u64 << kid;
            materializable_val.push(kid);
        }
    }

    let mut start_keys: Vec<u8> = Vec::with_capacity(start_limit);
    for depth in 0..start_limit {
        let Some(StackItem::Value(v)) = stack.item_at(depth) else {
            return None;
        };
        let key = canonical_key(ctx, *v);
        let kid = intern_key(ctx, key, *v, &mut key_ids, &mut key_infos)?;
        start_keys.push(kid);
    }

    if key_infos.len() > 64 {
        return None;
    }

    let start = PackedState::from_ids(&start_keys)?;
    let goal = PackedState::from_ids(&goal_keys)?;

    let cache_key = PlanCacheKey {
        mode: 0,
        func_ptr: ctx.func as *const _ as usize,
        dup_max: cfg.dup_max as u8,
        swap_max: cfg.swap_max as u8,
        max_len: cfg.max_len as u8,
        max_expansions: cfg.max_expansions as u32,
        cost_hash: compute_cost_hash(cost, &key_infos, cfg),
        start,
        goal,
        ctx: PackedState::EMPTY,
        ctx_bits0: 0,
        ctx_bits1: 0,
        ctx_bits2: 0,
    };

    if let Some(hit) = {
        let cache = plan_cache().lock().unwrap();
        cache.get(&cache_key).cloned()
    } {
        if debug {
            eprintln!("normalize_search: cache hit");
        }
        return match hit {
            PlanCacheVal::None => None,
            PlanCacheVal::Steps(steps) => Some(NormalizePlan {
                cost: cost_for_steps(&steps, &key_infos, cost),
                steps,
                key_infos,
                goal_keys,
            }),
        };
    }

    if start == goal {
        plan_cache()
            .lock()
            .unwrap()
            .insert(cache_key, PlanCacheVal::Steps(Vec::new()));
        return Some(NormalizePlan {
            cost: Cost::default(),
            steps: Vec::new(),
            key_infos,
            goal_keys,
        });
    }

    let pop_cost = cost.cost_pop();
    let pop_gas = pop_cost.gas;
    let dup_gas_lb = minimal_dup_gas(cost, cfg.dup_max);
    let goal_counts = compute_goal_counts(&goal_keys);

    let mut upper_bound = estimate_flush_rebuild_cost(ctx, stack, desired, cost);
    let mut incumbent_steps: Option<Vec<Step>> = None;

    if let Some(steps) = build_delete_tail_under_prefix_upper_bound(&start_keys, &goal_keys, cfg) {
        let greedy_cost = cost_for_steps(&steps, &key_infos, cost);
        if greedy_cost <= upper_bound {
            if debug && greedy_cost < upper_bound {
                eprintln!(
                    "normalize_search: upper_bound improved by prefix-tail plan: ub={upper_bound:?} greedy={greedy_cost:?}"
                );
            }
            upper_bound = greedy_cost;
            incumbent_steps = Some(steps);
        }
    }

    if let Some(steps) =
        build_dup_and_star_swap_upper_bound(&start_keys, &goal_keys, &goal_counts, cfg)
    {
        let greedy_cost = cost_for_steps(&steps, &key_infos, cost);
        if greedy_cost <= upper_bound {
            if debug && greedy_cost < upper_bound {
                eprintln!(
                    "normalize_search: upper_bound improved by greedy plan: ub={upper_bound:?} greedy={greedy_cost:?}"
                );
            }
            upper_bound = greedy_cost;
            incumbent_steps = Some(steps);
        }
    }

    let push0_kid: Option<u8> = materializable_imm.iter().copied().find(|&kid| {
        matches!(
            key_infos[kid as usize],
            KeyInfo::Imm { canon, .. } if canon.is_zero()
        )
    });
    let push0_cost = push0_kid.map(|kid| {
        let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
            unreachable!("expected imm key info")
        };
        cost.cost_push_imm(canon)
    });

    let start_h = heuristic(start, &goal_counts, pop_gas, dup_gas_lb, &key_infos, cost);

    let mut best: FxHashMap<PackedState, Cost> = FxHashMap::default();
    best.insert(start, Cost::default());

    let mut parent: FxHashMap<PackedState, (PackedState, Step)> = FxHashMap::default();

    let mut open: BinaryHeap<QueueEntry> = BinaryHeap::new();
    open.push(QueueEntry {
        f: start_h,
        g: Cost::default(),
        state: start,
    });

    let mut expansions: usize = 0;
    while let Some(entry) = open.pop() {
        let Some(&g) = best.get(&entry.state) else {
            continue;
        };
        if entry.g != g {
            continue;
        }

        if entry.state == goal {
            let Some(steps) = reconstruct_steps(start, goal, &parent) else {
                break;
            };
            if incumbent_steps.is_none() || g < upper_bound {
                upper_bound = g;
                incumbent_steps = Some(steps);
            }
            continue;
        }

        if should_prune(entry.f, upper_bound, incumbent_steps.is_some()) {
            break;
        }

        // If we already have a feasible incumbent (greedy or found) plan, don't let the exact
        // search blow up compile time or memory trying to prove optimality.
        let max_states = if incumbent_steps.is_some() {
            200_000usize
        } else {
            500_000usize
        };
        if best.len() > max_states || open.len() > max_states {
            if debug {
                eprintln!(
                    "normalize_search: exceeded max_states={} (best_states={} open={})",
                    max_states,
                    best.len(),
                    open.len()
                );
            }
            break;
        }

        let h = heuristic(
            entry.state,
            &goal_counts,
            pop_gas,
            dup_gas_lb,
            &key_infos,
            cost,
        );
        if should_prune(g.saturating_add(h), upper_bound, incumbent_steps.is_some()) {
            continue;
        }

        expansions += 1;
        if expansions > cfg.max_expansions {
            if debug {
                eprintln!(
                    "normalize_search: exceeded max_expansions={} (best_states={} open={})",
                    cfg.max_expansions,
                    best.len(),
                    open.len()
                );
            }
            break;
        }

        let cur_len = entry.state.len();
        let suffix_k = common_suffix_len(entry.state, goal);
        let suffix_start = cur_len.saturating_sub(suffix_k);

        let prev_step = parent.get(&entry.state).map(|(_, s)| *s);

        let mut dup_cost_for_kid = [Cost {
            gas: u32::MAX,
            bytes: u32::MAX,
        }; 64];
        let mut duplicable: u64 = 0;
        if cur_len != 0 && cfg.dup_max != 0 {
            let max_pos = cur_len.saturating_sub(1).min(cfg.dup_max.saturating_sub(1));
            for pos in 0..=max_pos {
                let kid = entry.state.get(pos) as usize;
                duplicable |= 1u64 << kid;
                dup_cost_for_kid[kid] = dup_cost_for_kid[kid].min(cost.cost_dup(pos as u8));
            }
        }

        let mut consider_ctx = ConsiderCtx {
            goal_counts: &goal_counts,
            ctx_present: 0,
            pop_gas,
            dup_gas: dup_gas_lb,
            key_infos: &key_infos,
            cost,
            upper_bound,
            have_incumbent: incumbent_steps.is_some(),
            best: &mut best,
            parent: &mut parent,
            open: &mut open,
        };

        // POP
        if cur_len != 0 {
            consider_succ(
                entry.state.pop(),
                g.saturating_add(cost.cost_pop()),
                entry.state,
                Step::Pop,
                &mut consider_ctx,
            );
        }

        // PUSH0 (if present in the goal) before the 3-gas moves.
        if cur_len < cfg.max_len
            && let (Some(kid), Some(push0_cost)) = (push0_kid, push0_cost)
        {
            let bit = 1u64 << kid;
            let dominated = (duplicable & bit) != 0 && push0_cost >= dup_cost_for_kid[kid as usize];
            if !dominated {
                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(push0_cost),
                    entry.state,
                    Step::PushImm(kid),
                    &mut consider_ctx,
                );
            }
        }

        // SWAP
        if cur_len >= 2 {
            let max_depth = cur_len
                .saturating_sub(1)
                .min(cfg.swap_max.saturating_sub(1));
            for depth in 1..=max_depth {
                if matches!(prev_step, Some(Step::Swap(d)) if d as usize == depth) {
                    continue;
                }
                if entry.state.get(0) == entry.state.get(depth) {
                    continue;
                }
                if depth >= suffix_start && depth < cfg.dup_max {
                    continue;
                }
                consider_succ(
                    entry.state.swap(depth),
                    g.saturating_add(cost.cost_swap(depth as u8)),
                    entry.state,
                    Step::Swap(depth as u8),
                    &mut consider_ctx,
                );
            }
        }

        // DUP
        if cur_len != 0 && cfg.dup_max != 0 && cur_len < cfg.max_len {
            let max_pos = cur_len.saturating_sub(1).min(cfg.dup_max.saturating_sub(1));
            let mut seen: u64 = 0;
            for pos in 0..=max_pos {
                let kid = entry.state.get(pos);
                let bit = 1u64 << kid;
                if (seen & bit) != 0 {
                    continue;
                }
                seen |= bit;

                if Some(kid) == push0_kid
                    && let Some(push0_cost) = push0_cost
                    && push0_cost < dup_cost_for_kid[kid as usize]
                {
                    continue;
                }
                consider_succ(
                    entry.state.dup(pos),
                    g.saturating_add(cost.cost_dup(pos as u8)),
                    entry.state,
                    Step::Dup(pos as u8),
                    &mut consider_ctx,
                );
            }
        }

        if cur_len < cfg.max_len {
            for &kid in &materializable_imm {
                if Some(kid) == push0_kid {
                    continue;
                }

                let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
                    unreachable!("expected imm key info")
                };
                let push_cost = cost.cost_push_imm(canon);
                let bit = 1u64 << kid;
                let dominated =
                    (duplicable & bit) != 0 && push_cost >= dup_cost_for_kid[kid as usize];
                if dominated {
                    continue;
                }

                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(push_cost),
                    entry.state,
                    Step::PushImm(kid),
                    &mut consider_ctx,
                );
            }

            for &kid in &materializable_val {
                // If a value is duplicable, `DUP` dominates `LOAD` to the same successor state.
                if (duplicable & (1u64 << kid)) != 0 {
                    continue;
                }
                let KeyInfo::Val { vid } = key_infos[kid as usize] else {
                    unreachable!("expected val key info")
                };
                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(cost.cost_load(vid)),
                    entry.state,
                    Step::LoadVal(kid),
                    &mut consider_ctx,
                );
            }
        }
    }

    if debug {
        eprintln!(
            "normalize_search: exhausted search (best_states={} upper_bound={upper_bound:?})",
            best.len()
        );
    }

    plan_cache().lock().unwrap().insert(
        cache_key,
        incumbent_steps
            .as_ref()
            .map_or(PlanCacheVal::None, |steps| {
                PlanCacheVal::Steps(steps.clone())
            }),
    );

    incumbent_steps.map(|steps| NormalizePlan {
        cost: cost_for_steps(&steps, &key_infos, cost),
        steps,
        key_infos,
        goal_keys,
    })
}

pub(super) fn solve_optimal_repair_normalize_plan(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    desired: &[ValueId],
    base_len: usize,
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> Option<NormalizePlan> {
    let start_len = stack.len_above_func_ret();
    if base_len > start_len || base_len > desired.len() {
        return None;
    }
    let goal_repair = desired.len() - base_len;
    solve_optimal_repair_prefix_plan(ctx, stack, &desired[..goal_repair], base_len, cost, cfg)
}

pub(super) fn solve_optimal_repair_prefix_plan(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    desired_prefix: &[ValueId],
    base_len: usize,
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> Option<NormalizePlan> {
    let debug = normalize_search_debug_enabled();

    let start_len = stack.len_above_func_ret();
    if base_len > start_len {
        return None;
    }
    let start_repair = start_len - base_len;
    let goal_repair = desired_prefix.len();

    if start_repair > cfg.swap_max || goal_repair > cfg.swap_max {
        if debug {
            eprintln!(
                "repair_normalize_search: reject repair_len start={} goal={} swap_max={}",
                start_repair, goal_repair, cfg.swap_max
            );
        }
        return None;
    }

    if cfg.max_len > 21 {
        if debug {
            eprintln!("repair_normalize_search: reject max_len={}", cfg.max_len);
        }
        return None;
    }
    if start_repair > cfg.max_len || goal_repair > cfg.max_len {
        if debug {
            eprintln!(
                "repair_normalize_search: reject bounds start_repair={} goal_repair={} max_len={}",
                start_repair, goal_repair, cfg.max_len
            );
        }
        return None;
    }

    let mut key_ids: FxHashMap<Key, u8> = FxHashMap::default();
    let mut key_infos: Vec<KeyInfo> = Vec::new();

    let mut goal_keys: Vec<u8> = Vec::with_capacity(desired_prefix.len());
    let mut materializable_imm: Vec<u8> = Vec::new();
    let mut materializable_val: Vec<u8> = Vec::new();
    let mut seen_push: u64 = 0;
    let mut seen_load: u64 = 0;

    for &v in desired_prefix {
        let key = canonical_key(ctx, v);
        let kid = intern_key(ctx, key, v, &mut key_ids, &mut key_infos)?;
        goal_keys.push(kid);

        if ctx.func.dfg.value_is_imm(v) {
            if (seen_push & (1u64 << kid)) == 0 {
                seen_push |= 1u64 << kid;
                materializable_imm.push(kid);
            }
        } else if (seen_load & (1u64 << kid)) == 0 {
            seen_load |= 1u64 << kid;
            materializable_val.push(kid);
        }
    }

    let mut start_keys: Vec<u8> = Vec::with_capacity(start_repair);
    for depth in 0..start_repair {
        let Some(StackItem::Value(v)) = stack.item_at(depth) else {
            return None;
        };
        let key = canonical_key(ctx, *v);
        let kid = intern_key(ctx, key, *v, &mut key_ids, &mut key_infos)?;
        start_keys.push(kid);
    }

    let suffix_ctx_len = base_len.min(cfg.dup_max);
    let mut suffix_ctx_keys: Vec<u8> = Vec::with_capacity(suffix_ctx_len);
    for off in 0..suffix_ctx_len {
        let Some(StackItem::Value(v)) = stack.item_at(start_repair + off) else {
            return None;
        };
        let key = canonical_key(ctx, *v);
        let kid = intern_key(ctx, key, *v, &mut key_ids, &mut key_infos)?;
        suffix_ctx_keys.push(kid);
    }

    if key_infos.len() > 64 {
        return None;
    }

    let start = PackedState::from_ids(&start_keys)?;
    let goal = PackedState::from_ids(&goal_keys)?;
    let ctx_state = PackedState::from_ids(&suffix_ctx_keys)?;

    let cache_key = PlanCacheKey {
        mode: 1,
        func_ptr: ctx.func as *const _ as usize,
        dup_max: cfg.dup_max as u8,
        swap_max: cfg.swap_max as u8,
        max_len: cfg.max_len as u8,
        max_expansions: cfg.max_expansions as u32,
        cost_hash: compute_cost_hash(cost, &key_infos, cfg),
        start,
        goal,
        ctx: ctx_state,
        ctx_bits0: 0,
        ctx_bits1: 0,
        ctx_bits2: 0,
    };

    if let Some(hit) = {
        let cache = plan_cache().lock().unwrap();
        cache.get(&cache_key).cloned()
    } {
        if debug {
            eprintln!("repair_normalize_search: cache hit");
        }
        return match hit {
            PlanCacheVal::None => None,
            PlanCacheVal::Steps(steps) => Some(NormalizePlan {
                cost: cost_for_steps(&steps, &key_infos, cost),
                steps,
                key_infos,
                goal_keys,
            }),
        };
    }

    if start == goal {
        plan_cache()
            .lock()
            .unwrap()
            .insert(cache_key, PlanCacheVal::Steps(Vec::new()));
        return Some(NormalizePlan {
            cost: Cost::default(),
            steps: Vec::new(),
            key_infos,
            goal_keys,
        });
    }

    let mut ctx_present: u64 = 0;
    for &kid in &suffix_ctx_keys {
        ctx_present |= 1u64 << kid;
    }

    let pop_cost = cost.cost_pop();
    let pop_gas = pop_cost.gas;
    let dup_gas_lb = minimal_dup_gas(cost, cfg.dup_max);
    let goal_counts = compute_goal_counts(&goal_keys);

    let mut upper_bound = Cost::default();
    for _ in 0..start_repair {
        upper_bound = upper_bound.saturating_add(pop_cost);
    }
    for &v in desired_prefix {
        if ctx.func.dfg.value_is_imm(v) {
            let imm = ctx
                .func
                .dfg
                .value_imm(v)
                .expect("imm value missing payload")
                .as_i256();
            upper_bound = upper_bound.saturating_add(cost.cost_push_imm(imm));
        } else {
            upper_bound = upper_bound.saturating_add(cost.cost_load(v));
        }
    }
    let mut incumbent_steps: Option<Vec<Step>> = None;

    if let Some(steps) = build_greedy_repair_prefix_upper_bound(
        &start_keys,
        &goal_keys,
        &suffix_ctx_keys,
        &key_infos,
        cost,
        cfg,
    ) {
        let greedy_cost = cost_for_steps(&steps, &key_infos, cost);
        if greedy_cost <= upper_bound {
            if debug && greedy_cost < upper_bound {
                eprintln!(
                    "repair_normalize_search: upper_bound improved by greedy repair plan: ub={upper_bound:?} greedy={greedy_cost:?}"
                );
            }
            upper_bound = greedy_cost;
            incumbent_steps = Some(steps);
        }
    }

    let push0_kid: Option<u8> = materializable_imm.iter().copied().find(|&kid| {
        matches!(
            key_infos[kid as usize],
            KeyInfo::Imm { canon, .. } if canon.is_zero()
        )
    });
    let push0_cost = push0_kid.map(|kid| {
        let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
            unreachable!("expected imm key info")
        };
        cost.cost_push_imm(canon)
    });

    let start_h = heuristic_with_ctx(
        start,
        &goal_counts,
        ctx_present,
        pop_gas,
        dup_gas_lb,
        &key_infos,
        cost,
    );

    let mut best: FxHashMap<PackedState, Cost> = FxHashMap::default();
    best.insert(start, Cost::default());

    let mut parent: FxHashMap<PackedState, (PackedState, Step)> = FxHashMap::default();

    let mut open: BinaryHeap<QueueEntry> = BinaryHeap::new();
    open.push(QueueEntry {
        f: start_h,
        g: Cost::default(),
        state: start,
    });

    let mut expansions: usize = 0;
    while let Some(entry) = open.pop() {
        let Some(&g) = best.get(&entry.state) else {
            continue;
        };
        if entry.g != g {
            continue;
        }

        if entry.state == goal {
            let Some(steps) = reconstruct_steps(start, goal, &parent) else {
                break;
            };
            if incumbent_steps.is_none() || g < upper_bound {
                upper_bound = g;
                incumbent_steps = Some(steps);
            }
            continue;
        }

        if should_prune(entry.f, upper_bound, incumbent_steps.is_some()) {
            break;
        }

        let max_states = if incumbent_steps.is_some() {
            200_000usize
        } else {
            500_000usize
        };
        if best.len() > max_states || open.len() > max_states {
            if debug {
                eprintln!(
                    "repair_normalize_search: exceeded max_states={} (best_states={} open={})",
                    max_states,
                    best.len(),
                    open.len()
                );
            }
            break;
        }

        let h = heuristic_with_ctx(
            entry.state,
            &goal_counts,
            ctx_present,
            pop_gas,
            dup_gas_lb,
            &key_infos,
            cost,
        );
        if should_prune(g.saturating_add(h), upper_bound, incumbent_steps.is_some()) {
            continue;
        }

        expansions += 1;
        if expansions > cfg.max_expansions {
            if debug {
                eprintln!(
                    "repair_normalize_search: exceeded max_expansions={} (best_states={} open={})",
                    cfg.max_expansions,
                    best.len(),
                    open.len()
                );
            }
            break;
        }

        let cur_len = entry.state.len();
        let suffix_k = common_suffix_len(entry.state, goal);
        let suffix_start = cur_len.saturating_sub(suffix_k);

        let prev_step = parent.get(&entry.state).map(|(_, s)| *s);

        let mut dup_cost_for_kid = [Cost {
            gas: u32::MAX,
            bytes: u32::MAX,
        }; 64];
        let mut duplicable: u64 = 0;
        if cfg.dup_max != 0 {
            let total_len = cur_len.saturating_add(base_len);
            if total_len != 0 {
                let max_pos = total_len
                    .saturating_sub(1)
                    .min(cfg.dup_max.saturating_sub(1));
                for pos in 0..=max_pos {
                    let kid = if pos < cur_len {
                        entry.state.get(pos)
                    } else {
                        let off = pos - cur_len;
                        debug_assert!(off < suffix_ctx_keys.len());
                        suffix_ctx_keys[off]
                    } as usize;
                    duplicable |= 1u64 << kid;
                    dup_cost_for_kid[kid] = dup_cost_for_kid[kid].min(cost.cost_dup(pos as u8));
                }
            }
        }

        let mut consider_ctx = ConsiderCtx {
            goal_counts: &goal_counts,
            ctx_present,
            pop_gas,
            dup_gas: dup_gas_lb,
            key_infos: &key_infos,
            cost,
            upper_bound,
            have_incumbent: incumbent_steps.is_some(),
            best: &mut best,
            parent: &mut parent,
            open: &mut open,
        };

        // POP (only within the repair region).
        if cur_len != 0 {
            consider_succ(
                entry.state.pop(),
                g.saturating_add(cost.cost_pop()),
                entry.state,
                Step::Pop,
                &mut consider_ctx,
            );
        }

        // PUSH0 (if present in the goal) before the 3-gas moves.
        if cur_len < cfg.max_len
            && let (Some(kid), Some(push0_cost)) = (push0_kid, push0_cost)
        {
            let bit = 1u64 << kid;
            let dominated = (duplicable & bit) != 0 && push0_cost >= dup_cost_for_kid[kid as usize];
            if !dominated {
                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(push0_cost),
                    entry.state,
                    Step::PushImm(kid),
                    &mut consider_ctx,
                );
            }
        }

        // SWAP (restricted to the repair region).
        if cur_len >= 2 {
            let max_depth = cur_len
                .saturating_sub(1)
                .min(cfg.swap_max.saturating_sub(1));
            for depth in 1..=max_depth {
                if matches!(prev_step, Some(Step::Swap(d)) if d as usize == depth) {
                    continue;
                }
                if entry.state.get(0) == entry.state.get(depth) {
                    continue;
                }
                if depth >= suffix_start && depth < cfg.dup_max {
                    continue;
                }
                consider_succ(
                    entry.state.swap(depth),
                    g.saturating_add(cost.cost_swap(depth as u8)),
                    entry.state,
                    Step::Swap(depth as u8),
                    &mut consider_ctx,
                );
            }
        }

        // DUP (can read from the repair region or the frozen suffix context).
        if cfg.dup_max != 0 && cur_len < cfg.max_len {
            let total_len = cur_len.saturating_add(base_len);
            if total_len != 0 {
                let max_pos = total_len
                    .saturating_sub(1)
                    .min(cfg.dup_max.saturating_sub(1));

                let mut seen: u64 = 0;
                for pos in 0..=max_pos {
                    let kid = if pos < cur_len {
                        entry.state.get(pos)
                    } else {
                        let off = pos - cur_len;
                        debug_assert!(off < suffix_ctx_keys.len());
                        suffix_ctx_keys[off]
                    };

                    if goal_counts[kid as usize] == 0 {
                        continue;
                    }

                    let bit = 1u64 << kid;
                    if (seen & bit) != 0 {
                        continue;
                    }
                    seen |= bit;

                    if Some(kid) == push0_kid
                        && let Some(push0_cost) = push0_cost
                        && push0_cost < dup_cost_for_kid[kid as usize]
                    {
                        continue;
                    }

                    consider_succ(
                        entry.state.push(kid),
                        g.saturating_add(cost.cost_dup(pos as u8)),
                        entry.state,
                        Step::Dup(pos as u8),
                        &mut consider_ctx,
                    );
                }
            }
        }

        if cur_len < cfg.max_len {
            for &kid in &materializable_imm {
                if Some(kid) == push0_kid {
                    continue;
                }

                let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
                    unreachable!("expected imm key info")
                };
                let push_cost = cost.cost_push_imm(canon);
                let bit = 1u64 << kid;
                let dominated =
                    (duplicable & bit) != 0 && push_cost >= dup_cost_for_kid[kid as usize];
                if dominated {
                    continue;
                }

                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(push_cost),
                    entry.state,
                    Step::PushImm(kid),
                    &mut consider_ctx,
                );
            }

            for &kid in &materializable_val {
                if (duplicable & (1u64 << kid)) != 0 {
                    continue;
                }
                let KeyInfo::Val { vid } = key_infos[kid as usize] else {
                    unreachable!("expected val key info")
                };
                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(cost.cost_load(vid)),
                    entry.state,
                    Step::LoadVal(kid),
                    &mut consider_ctx,
                );
            }
        }
    }

    if debug {
        eprintln!(
            "repair_normalize_search: exhausted search (best_states={} upper_bound={upper_bound:?})",
            best.len()
        );
    }

    plan_cache().lock().unwrap().insert(
        cache_key,
        incumbent_steps
            .as_ref()
            .map_or(PlanCacheVal::None, |steps| {
                PlanCacheVal::Steps(steps.clone())
            }),
    );

    incumbent_steps.map(|steps| NormalizePlan {
        cost: cost_for_steps(&steps, &key_infos, cost),
        steps,
        key_infos,
        goal_keys,
    })
}

struct OperandPrepProblem {
    key_infos: Vec<KeyInfo>,
    goal_keys: Vec<u8>,
    goal_counts: [u8; 64],
    preserve_mask: u64,
    last_use_mask: u64,
    materializable_imm: Vec<u8>,
    materializable_val: Vec<u8>,
    start_state: PrepState,
    goal_state: PackedState,
}

fn build_operand_prep_problem(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    args: &[ValueId],
    consume_last_use: &BitSet<ValueId>,
    cfg: SearchCfg,
) -> Option<OperandPrepProblem> {
    let start_limit = stack.len_above_func_ret();
    let window_len = start_limit.min(cfg.max_len);

    let mut key_ids: FxHashMap<Key, u8> = FxHashMap::default();
    let mut key_infos: Vec<KeyInfo> = Vec::new();

    let mut goal_keys: Vec<u8> = Vec::with_capacity(args.len());
    let mut goal_counts: [u8; 64] = [0u8; 64];
    let mut preserve_mask: u64 = 0;
    let mut last_use_mask: u64 = 0;

    let mut materializable_imm: Vec<u8> = Vec::new();
    let mut materializable_val: Vec<u8> = Vec::new();
    let mut seen_push: u64 = 0;
    let mut seen_load: u64 = 0;

    for &v in args {
        let key = canonical_key(ctx, v);
        let kid = intern_key(ctx, key, v, &mut key_ids, &mut key_infos)?;
        goal_keys.push(kid);
        goal_counts[kid as usize] = goal_counts[kid as usize].saturating_add(1);
        if consume_last_use.contains(v) {
            last_use_mask |= 1u64 << kid;
        }

        if !ctx.func.dfg.value_is_imm(v) && !consume_last_use.contains(v) {
            preserve_mask |= 1u64 << kid;
        }

        if ctx.func.dfg.value_is_imm(v) {
            if (seen_push & (1u64 << kid)) == 0 {
                seen_push |= 1u64 << kid;
                materializable_imm.push(kid);
            }
        } else if (seen_load & (1u64 << kid)) == 0 {
            seen_load |= 1u64 << kid;
            materializable_val.push(kid);
        }
    }

    let mut start_keys: Vec<u8> = Vec::with_capacity(window_len);
    for depth in 0..window_len {
        let Some(StackItem::Value(v)) = stack.item_at(depth) else {
            return None;
        };
        let key = canonical_key(ctx, *v);
        let kid = intern_key(ctx, key, *v, &mut key_ids, &mut key_infos)?;
        start_keys.push(kid);
    }

    if key_infos.len() > 64 {
        return None;
    }

    let start_window = PackedState::from_ids(&start_keys)?;

    let mut tail_present: u64 = 0;
    if preserve_mask != 0 && start_limit > window_len {
        for depth in window_len..start_limit {
            let Some(StackItem::Value(v)) = stack.item_at(depth) else {
                continue;
            };
            let key = canonical_key(ctx, *v);
            let Some(&kid) = key_ids.get(&key) else {
                continue;
            };
            let bit = 1u64 << kid;
            if (preserve_mask & bit) != 0 {
                tail_present |= bit;
                if tail_present == preserve_mask {
                    break;
                }
            }
        }
    }

    Some(OperandPrepProblem {
        goal_state: PackedState::from_ids(&goal_keys)?,
        key_infos,
        goal_keys,
        goal_counts,
        preserve_mask,
        last_use_mask,
        materializable_imm,
        materializable_val,
        start_state: PrepState {
            window: start_window,
            tail: tail_present,
            mem: 0,
        },
    })
}

fn operand_prep_cache_key(
    ctx: &StackifyContext<'_>,
    problem: &OperandPrepProblem,
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> PlanCacheKey {
    PlanCacheKey {
        mode: 2,
        func_ptr: ctx.func as *const _ as usize,
        dup_max: cfg.dup_max as u8,
        swap_max: cfg.swap_max as u8,
        max_len: cfg.max_len as u8,
        max_expansions: cfg.max_expansions as u32,
        cost_hash: compute_cost_hash(cost, &problem.key_infos, cfg),
        start: problem.start_state.window,
        goal: problem.goal_state,
        ctx: PackedState::EMPTY,
        ctx_bits0: problem.preserve_mask,
        ctx_bits1: problem.last_use_mask,
        ctx_bits2: problem.start_state.tail,
    }
}

fn operand_prep_push0_cost(
    problem: &OperandPrepProblem,
    cost: &impl CostModel,
) -> (Option<u8>, Option<Cost>) {
    let push0_kid = problem.materializable_imm.iter().copied().find(|&kid| {
        matches!(
            problem.key_infos[kid as usize],
            KeyInfo::Imm { canon, .. } if canon.is_zero()
        )
    });
    let push0_cost = push0_kid.map(|kid| {
        let KeyInfo::Imm { canon, .. } = problem.key_infos[kid as usize] else {
            unreachable!("expected imm key info")
        };
        cost.cost_push_imm(canon)
    });
    (push0_kid, push0_cost)
}

fn build_operand_prep_baseline_upper_bound(
    ctx: &StackifyContext<'_>,
    args: &[ValueId],
    problem: &OperandPrepProblem,
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> Option<(Vec<Step>, Cost)> {
    let surplus_last_use_penalty = cost.cost_pop().saturating_add(cost.cost_swap(1));
    let mut baseline_state = problem.start_state;
    let mut baseline_steps: Vec<Step> = Vec::new();
    let mut baseline_cost = Cost::default();
    let mut prepared: usize = 0;
    let mut consumed_from_stack: u64 = 0;

    for (idx, &v) in args.iter().enumerate().rev() {
        let kid = problem.goal_keys[idx];
        let bit = 1u64 << kid;
        if ctx.func.dfg.value_is_imm(v) {
            baseline_steps.push(Step::PushImm(kid));
            let next_state = prep_insert(
                baseline_state,
                kid,
                problem.preserve_mask,
                false,
                cfg.max_len,
            );
            baseline_cost = baseline_cost.saturating_add(operand_prep_insert_cost(
                baseline_state,
                next_state,
                kid,
                &problem.goal_counts,
                problem.last_use_mask,
                cost.cost_push_imm(
                    ctx.func
                        .dfg
                        .value_imm(v)
                        .expect("imm value missing payload")
                        .as_i256(),
                ),
                surplus_last_use_penalty,
            ));
            baseline_state = next_state;
            prepared += 1;
            continue;
        }

        if (problem.last_use_mask & bit) != 0
            && (consumed_from_stack & bit) == 0
            && baseline_state.window.len() != 0
        {
            let max_pos = (baseline_state.window.len() - 1).min(cfg.swap_max.saturating_sub(1));
            let mut found: Option<usize> = None;
            if prepared <= max_pos {
                for pos in prepared..=max_pos {
                    if baseline_state.window.get(pos) == kid {
                        found = Some(pos);
                        break;
                    }
                }
            }
            if let Some(pos) = found
                && pos <= super::super::CONSUME_LAST_USE_MAX_SWAPS
            {
                for d in 1..=pos {
                    baseline_steps.push(Step::Swap(d as u8));
                    baseline_cost = baseline_cost.saturating_add(cost.cost_swap(d as u8));
                    baseline_state.window = baseline_state.window.swap(d);
                }
                consumed_from_stack |= bit;
                prepared += 1;
                continue;
            }
        }

        let source = copy_source_choices_for_kid(
            baseline_state.window.len(),
            |pos| baseline_state.window.get(pos),
            &[],
            &problem.key_infos,
            cost,
            cfg,
            kid,
        )
        .best_direct_insert();
        baseline_steps.push(match source {
            CopySourceCandidate::CurrentDup { pos, .. } => Step::Dup(pos as u8),
            CopySourceCandidate::PushImm { .. } => Step::PushImm(kid),
            CopySourceCandidate::LoadVal { .. } => Step::LoadVal(kid),
            CopySourceCandidate::CurrentSwapDup { .. } | CopySourceCandidate::SuffixDup { .. } => {
                unreachable!("operand prep baseline only uses direct dup or materialization")
            }
        });
        let next_state = prep_insert(
            baseline_state,
            kid,
            problem.preserve_mask,
            matches!(source, CopySourceCandidate::LoadVal { .. }),
            cfg.max_len,
        );
        baseline_cost = baseline_cost.saturating_add(operand_prep_insert_cost(
            baseline_state,
            next_state,
            kid,
            &problem.goal_counts,
            problem.last_use_mask,
            source.cost(),
            surplus_last_use_penalty,
        ));
        baseline_state = next_state;
        prepared += 1;
    }

    operand_prep_goal(
        baseline_state,
        &problem.goal_keys,
        problem.preserve_mask,
        &problem.goal_counts,
    )
    .then_some((baseline_steps, baseline_cost))
}

fn operand_prep_goal_run_anywhere(state: PrepState, goal_keys: &[u8]) -> (usize, usize, usize) {
    let window_len = state.window.len().min(goal_keys.len());
    if window_len == 0 {
        return (0, goal_keys.len(), usize::MAX);
    }

    let mut best = (0usize, goal_keys.len(), usize::MAX);
    for pos in 0..window_len {
        for start in 0..goal_keys.len() {
            if state.window.get(pos) != goal_keys[start] {
                continue;
            }

            let mut len = 1usize;
            while pos + len < window_len
                && start + len < goal_keys.len()
                && state.window.get(pos + len) == goal_keys[start + len]
            {
                len += 1;
            }

            if len > best.0
                || (len == best.0 && (pos < best.2 || (pos == best.2 && start < best.1)))
            {
                best = (len, start, pos);
            }
        }
    }
    best
}

fn operand_prep_missing_count(
    state: PrepState,
    goal_counts: &[u8; 64],
    preserve_mask: u64,
) -> usize {
    let mut win_counts = [0u8; 64];
    for idx in 0..state.window.len() {
        let kid = state.window.get(idx) as usize;
        win_counts[kid] = win_counts[kid].saturating_add(1);
    }

    let mut missing = 0usize;
    for (kid, &need_operands) in goal_counts.iter().enumerate() {
        let bit = 1u64 << kid;
        let preserve_extra = usize::from((preserve_mask & bit) != 0 && (state.mem & bit) == 0);
        let need_total = need_operands as usize + preserve_extra;
        let have_total = win_counts[kid] as usize + usize::from((state.tail & bit) != 0);
        missing += need_total.saturating_sub(have_total);
    }
    missing
}

#[derive(Clone)]
struct PrepGreedyNode {
    state: PrepState,
    steps: Vec<Step>,
    cost: Cost,
    last_step: Option<Step>,
    run_len: usize,
    run_start: usize,
    run_pos: usize,
    run_reaches_tail: bool,
    missing: usize,
}

fn prep_greedy_node(
    state: PrepState,
    steps: Vec<Step>,
    cost: Cost,
    last_step: Option<Step>,
    goal_keys: &[u8],
    goal_counts: &[u8; 64],
    preserve_mask: u64,
) -> PrepGreedyNode {
    let (run_len, run_start, run_pos) = operand_prep_goal_run_anywhere(state, goal_keys);
    PrepGreedyNode {
        state,
        steps,
        cost,
        last_step,
        run_len,
        run_start,
        run_pos,
        run_reaches_tail: run_len != 0 && run_start + run_len == goal_keys.len(),
        missing: operand_prep_missing_count(state, goal_counts, preserve_mask),
    }
}

fn prep_greedy_node_cmp(lhs: &PrepGreedyNode, rhs: &PrepGreedyNode) -> Ordering {
    rhs.run_len
        .cmp(&lhs.run_len)
        .then_with(|| rhs.run_reaches_tail.cmp(&lhs.run_reaches_tail))
        .then_with(|| lhs.run_pos.cmp(&rhs.run_pos))
        .then_with(|| lhs.run_start.cmp(&rhs.run_start))
        .then_with(|| lhs.missing.cmp(&rhs.missing))
        .then_with(|| lhs.cost.cmp(&rhs.cost))
        .then_with(|| lhs.state.cmp(&rhs.state))
}

fn prep_greedy_node_better(lhs: &PrepGreedyNode, rhs: &PrepGreedyNode) -> bool {
    prep_greedy_node_cmp(lhs, rhs).is_lt()
}

fn build_greedy_operand_prep_upper_bound(
    problem: &OperandPrepProblem,
    cost: &impl CostModel,
    cfg: SearchCfg,
    upper_bound: Cost,
) -> Option<(Vec<Step>, Cost)> {
    if operand_prep_goal(
        problem.start_state,
        &problem.goal_keys,
        problem.preserve_mask,
        &problem.goal_counts,
    ) {
        return Some((Vec::new(), Cost::default()));
    }

    let last_use_count = problem.last_use_mask.count_ones() as usize;
    if cfg.max_len <= cfg.swap_max && last_use_count < 4 {
        return None;
    }

    let (push0_kid, push0_cost) = operand_prep_push0_cost(problem, cost);
    let surplus_last_use_penalty = cost.cost_pop().saturating_add(cost.cost_swap(1));
    let max_depth = problem.goal_keys.len().saturating_add(cfg.swap_max).min(24);
    let beam_width = 192usize;
    let mut frontier = vec![prep_greedy_node(
        problem.start_state,
        Vec::new(),
        Cost::default(),
        None,
        &problem.goal_keys,
        &problem.goal_counts,
        problem.preserve_mask,
    )];
    let mut best_goal: Option<(Vec<Step>, Cost)> = None;

    for _ in 0..max_depth {
        let mut next_frontier: FxHashMap<PrepState, PrepGreedyNode> = FxHashMap::default();

        for node in frontier {
            if operand_prep_goal(
                node.state,
                &problem.goal_keys,
                problem.preserve_mask,
                &problem.goal_counts,
            ) {
                if best_goal
                    .as_ref()
                    .map(|(_, best_cost)| node.cost < *best_cost)
                    .unwrap_or(true)
                {
                    best_goal = Some((node.steps.clone(), node.cost));
                }
                continue;
            }

            if node.cost >= upper_bound
                || best_goal
                    .as_ref()
                    .map(|(_, best_cost)| node.cost >= *best_cost)
                    .unwrap_or(false)
            {
                continue;
            }

            let cur_len = node.state.window.len();
            let mut dup_cost_for_kid = [Cost {
                gas: u32::MAX,
                bytes: u32::MAX,
            }; 64];
            let mut duplicable: u64 = 0;
            if cfg.dup_max != 0 && cur_len != 0 {
                let max_pos = (cur_len - 1).min(cfg.dup_max.saturating_sub(1));
                for pos in 0..=max_pos {
                    let kid = node.state.window.get(pos) as usize;
                    duplicable |= 1u64 << kid;
                    dup_cost_for_kid[kid] = dup_cost_for_kid[kid].min(cost.cost_dup(pos as u8));
                }
            }

            let mut consider = |state: PrepState, next_cost: Cost, step: Step| {
                if next_cost >= upper_bound
                    || best_goal
                        .as_ref()
                        .map(|(_, best_cost)| next_cost >= *best_cost)
                        .unwrap_or(false)
                {
                    return;
                }

                let mut steps = node.steps.clone();
                steps.push(step);
                let candidate = prep_greedy_node(
                    state,
                    steps,
                    next_cost,
                    Some(step),
                    &problem.goal_keys,
                    &problem.goal_counts,
                    problem.preserve_mask,
                );
                if let Some(existing) = next_frontier.get(&state)
                    && !prep_greedy_node_better(&candidate, existing)
                {
                    return;
                }
                next_frontier.insert(state, candidate);
            };

            if cur_len >= 2 {
                let max_depth = cur_len
                    .saturating_sub(1)
                    .min(cfg.swap_max.saturating_sub(1));
                for depth in 1..=max_depth {
                    if matches!(node.last_step, Some(Step::Swap(d)) if d as usize == depth) {
                        continue;
                    }
                    if node.state.window.get(0) == node.state.window.get(depth) {
                        continue;
                    }

                    consider(
                        PrepState {
                            window: node.state.window.swap(depth),
                            ..node.state
                        },
                        node.cost.saturating_add(cost.cost_swap(depth as u8)),
                        Step::Swap(depth as u8),
                    );
                }
            }

            if cfg.dup_max != 0 && cur_len != 0 {
                let max_pos = (cur_len - 1).min(cfg.dup_max.saturating_sub(1));
                let mut seen_kids: u64 = 0;
                for pos in 0..=max_pos {
                    let kid = node.state.window.get(pos);
                    if problem.goal_counts[kid as usize] == 0 {
                        continue;
                    }
                    let bit = 1u64 << kid;
                    if (seen_kids & bit) != 0 {
                        continue;
                    }
                    seen_kids |= bit;

                    if Some(kid) == push0_kid
                        && let Some(push0_cost) = push0_cost
                        && push0_cost < dup_cost_for_kid[kid as usize]
                    {
                        continue;
                    }

                    let next =
                        prep_insert(node.state, kid, problem.preserve_mask, false, cfg.max_len);
                    consider(
                        next,
                        node.cost.saturating_add(operand_prep_insert_cost(
                            node.state,
                            next,
                            kid,
                            &problem.goal_counts,
                            problem.last_use_mask,
                            cost.cost_dup(pos as u8),
                            surplus_last_use_penalty,
                        )),
                        Step::Dup(pos as u8),
                    );
                }
            }

            if let (Some(kid), Some(push0_cost)) = (push0_kid, push0_cost) {
                let bit = 1u64 << kid;
                let dominated =
                    (duplicable & bit) != 0 && push0_cost >= dup_cost_for_kid[kid as usize];
                if !dominated {
                    let next =
                        prep_insert(node.state, kid, problem.preserve_mask, false, cfg.max_len);
                    consider(
                        next,
                        node.cost.saturating_add(operand_prep_insert_cost(
                            node.state,
                            next,
                            kid,
                            &problem.goal_counts,
                            problem.last_use_mask,
                            push0_cost,
                            surplus_last_use_penalty,
                        )),
                        Step::PushImm(kid),
                    );
                }
            }

            for &kid in &problem.materializable_imm {
                if Some(kid) == push0_kid {
                    continue;
                }
                let KeyInfo::Imm { canon, .. } = problem.key_infos[kid as usize] else {
                    unreachable!("expected imm key info")
                };
                let push_cost = cost.cost_push_imm(canon);
                let bit = 1u64 << kid;
                let dominated =
                    (duplicable & bit) != 0 && push_cost >= dup_cost_for_kid[kid as usize];
                if dominated {
                    continue;
                }

                let next = prep_insert(node.state, kid, problem.preserve_mask, false, cfg.max_len);
                consider(
                    next,
                    node.cost.saturating_add(operand_prep_insert_cost(
                        node.state,
                        next,
                        kid,
                        &problem.goal_counts,
                        problem.last_use_mask,
                        push_cost,
                        surplus_last_use_penalty,
                    )),
                    Step::PushImm(kid),
                );
            }

            for &kid in &problem.materializable_val {
                let bit = 1u64 << kid;
                let set_mem = (problem.preserve_mask & bit) != 0;
                let KeyInfo::Val { vid } = problem.key_infos[kid as usize] else {
                    unreachable!("expected val key info")
                };
                let next =
                    prep_insert(node.state, kid, problem.preserve_mask, set_mem, cfg.max_len);
                consider(
                    next,
                    node.cost.saturating_add(operand_prep_insert_cost(
                        node.state,
                        next,
                        kid,
                        &problem.goal_counts,
                        problem.last_use_mask,
                        cost.cost_load(vid),
                        surplus_last_use_penalty,
                    )),
                    Step::LoadVal(kid),
                );
            }
        }

        if next_frontier.is_empty() {
            break;
        }

        frontier = next_frontier.into_values().collect();
        frontier.sort_unstable_by(prep_greedy_node_cmp);
        frontier.truncate(beam_width);
    }

    best_goal
}

pub(super) fn solve_optimal_operand_prep_plan(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    args: &[ValueId],
    consume_last_use: &BitSet<ValueId>,
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> Option<NormalizePlan> {
    let debug = normalize_search_debug_enabled();

    if args.is_empty() {
        return Some(NormalizePlan {
            cost: Cost::default(),
            steps: Vec::new(),
            key_infos: Vec::new(),
            goal_keys: Vec::new(),
        });
    }

    if cfg.max_len > 21 {
        if debug {
            eprintln!("operand_prep_search: reject max_len={}", cfg.max_len);
        }
        return None;
    }
    if args.len() > cfg.max_len {
        if debug {
            eprintln!(
                "operand_prep_search: reject args_len={} max_len={}",
                args.len(),
                cfg.max_len
            );
        }
        return None;
    }

    let problem = build_operand_prep_problem(ctx, stack, args, consume_last_use, cfg)?;
    let cache_key = operand_prep_cache_key(ctx, &problem, cost, cfg);

    if let Some(hit) = {
        let cache = plan_cache().lock().unwrap();
        cache.get(&cache_key).cloned()
    } {
        if debug {
            eprintln!("operand_prep_search: cache hit");
        }
        return match hit {
            PlanCacheVal::None => None,
            PlanCacheVal::Steps(steps) => Some(NormalizePlan {
                cost: cost_for_steps(&steps, &problem.key_infos, cost),
                steps,
                key_infos: problem.key_infos,
                goal_keys: problem.goal_keys,
            }),
        };
    }

    if operand_prep_goal(
        problem.start_state,
        &problem.goal_keys,
        problem.preserve_mask,
        &problem.goal_counts,
    ) {
        plan_cache()
            .lock()
            .unwrap()
            .insert(cache_key, PlanCacheVal::Steps(Vec::new()));
        return Some(NormalizePlan {
            cost: Cost::default(),
            steps: Vec::new(),
            key_infos: problem.key_infos,
            goal_keys: problem.goal_keys,
        });
    }

    let (push0_kid, push0_cost) = operand_prep_push0_cost(&problem, cost);
    let pop_cost = cost.cost_pop();
    let surplus_last_use_penalty = pop_cost.saturating_add(cost.cost_swap(1));
    let Some((baseline_steps, baseline_cost)) =
        build_operand_prep_baseline_upper_bound(ctx, args, &problem, cost, cfg)
    else {
        if debug {
            eprintln!("operand_prep_search: baseline plan failed goal check");
        }
        plan_cache()
            .lock()
            .unwrap()
            .insert(cache_key, PlanCacheVal::None);
        return None;
    };

    let high_arity_consuming = args.len() > cfg.swap_max
        && args.iter().all(|&v| consume_last_use.contains(v))
        && problem.preserve_mask == 0;

    let mut upper_bound = baseline_cost;
    let mut incumbent_steps: Vec<Step> = baseline_steps;
    let mut incumbent_cost = upper_bound;

    if let Some((steps, greedy_cost)) =
        build_greedy_operand_prep_upper_bound(&problem, cost, cfg, upper_bound)
        && greedy_cost < upper_bound
    {
        if debug {
            eprintln!(
                "operand_prep_search: upper_bound improved by greedy plan: ub={upper_bound:?} greedy={greedy_cost:?}"
            );
        }
        upper_bound = greedy_cost;
        incumbent_steps = steps;
        incumbent_cost = greedy_cost;
    }

    if high_arity_consuming {
        plan_cache()
            .lock()
            .unwrap()
            .insert(cache_key, PlanCacheVal::Steps(incumbent_steps.clone()));

        return Some(NormalizePlan {
            cost: incumbent_cost,
            steps: incumbent_steps,
            key_infos: problem.key_infos,
            goal_keys: problem.goal_keys,
        });
    }

    let dup_gas_lb = minimal_dup_gas(cost, cfg.dup_max);
    let start_h = heuristic_operand_prep(
        problem.start_state,
        &problem.goal_counts,
        problem.preserve_mask,
        dup_gas_lb,
        &problem.key_infos,
        cost,
    );

    let mut best: FxHashMap<PrepState, Cost> = FxHashMap::default();
    best.insert(problem.start_state, Cost::default());

    let mut parent: FxHashMap<PrepState, (PrepState, Step)> = FxHashMap::default();

    let mut open: BinaryHeap<PrepQueueEntry> = BinaryHeap::new();
    open.push(PrepQueueEntry {
        f: start_h,
        g: Cost::default(),
        state: problem.start_state,
    });

    let mut expansions: usize = 0;
    while let Some(entry) = open.pop() {
        let Some(&g) = best.get(&entry.state) else {
            continue;
        };
        if entry.g != g {
            continue;
        }

        if operand_prep_goal(
            entry.state,
            &problem.goal_keys,
            problem.preserve_mask,
            &problem.goal_counts,
        ) {
            let mut steps: Vec<Step> = Vec::new();
            let mut cur = entry.state;
            while cur != problem.start_state {
                let &(prev, step) = parent.get(&cur)?;
                steps.push(step);
                cur = prev;
            }
            steps.reverse();
            if g < upper_bound {
                upper_bound = g;
                incumbent_steps = steps;
                incumbent_cost = g;
            }
            continue;
        }

        if should_prune(entry.f, upper_bound, true) {
            break;
        }

        let max_states = 400_000usize;
        if best.len() > max_states || open.len() > max_states {
            if debug {
                eprintln!(
                    "operand_prep_search: exceeded max_states={} (best_states={} open={})",
                    max_states,
                    best.len(),
                    open.len()
                );
            }
            break;
        }

        expansions += 1;
        if expansions > cfg.max_expansions {
            if debug {
                eprintln!(
                    "operand_prep_search: exceeded max_expansions={} (best_states={} open={})",
                    cfg.max_expansions,
                    best.len(),
                    open.len()
                );
            }
            break;
        }

        let prev_step = parent.get(&entry.state).map(|(_, s)| *s);

        let cur_len = entry.state.window.len();

        let mut dup_cost_for_kid = [Cost {
            gas: u32::MAX,
            bytes: u32::MAX,
        }; 64];
        let mut duplicable: u64 = 0;
        if cfg.dup_max != 0 && cur_len != 0 {
            let max_pos = (cur_len - 1).min(cfg.dup_max.saturating_sub(1));
            for pos in 0..=max_pos {
                let kid = entry.state.window.get(pos) as usize;
                duplicable |= 1u64 << kid;
                dup_cost_for_kid[kid] = dup_cost_for_kid[kid].min(cost.cost_dup(pos as u8));
            }
        }

        let mut consider_ctx = PrepConsiderCtx {
            goal_counts: &problem.goal_counts,
            preserve_mask: problem.preserve_mask,
            dup_gas: dup_gas_lb,
            key_infos: &problem.key_infos,
            cost,
            upper_bound,
            best: &mut best,
            parent: &mut parent,
            open: &mut open,
        };

        if cur_len >= 2 {
            let max_depth = cur_len
                .saturating_sub(1)
                .min(cfg.swap_max.saturating_sub(1));
            for depth in 1..=max_depth {
                if matches!(prev_step, Some(Step::Swap(d)) if d as usize == depth) {
                    continue;
                }
                if entry.state.window.get(0) == entry.state.window.get(depth) {
                    continue;
                }
                let next = PrepState {
                    window: entry.state.window.swap(depth),
                    ..entry.state
                };
                consider_prep_succ(
                    next,
                    g.saturating_add(cost.cost_swap(depth as u8)),
                    entry.state,
                    Step::Swap(depth as u8),
                    &mut consider_ctx,
                );
            }
        }

        if cfg.dup_max != 0 && cur_len != 0 {
            let max_pos = (cur_len - 1).min(cfg.dup_max.saturating_sub(1));
            let mut seen: u64 = 0;
            for pos in 0..=max_pos {
                let kid = entry.state.window.get(pos);
                if problem.goal_counts[kid as usize] == 0 {
                    continue;
                }
                let bit = 1u64 << kid;
                if (seen & bit) != 0 {
                    continue;
                }
                seen |= bit;

                if Some(kid) == push0_kid
                    && let Some(push0_cost) = push0_cost
                    && push0_cost < dup_cost_for_kid[kid as usize]
                {
                    continue;
                }

                let next = prep_insert(entry.state, kid, problem.preserve_mask, false, cfg.max_len);
                consider_prep_succ(
                    next,
                    g.saturating_add(operand_prep_insert_cost(
                        entry.state,
                        next,
                        kid,
                        &problem.goal_counts,
                        problem.last_use_mask,
                        cost.cost_dup(pos as u8),
                        surplus_last_use_penalty,
                    )),
                    entry.state,
                    Step::Dup(pos as u8),
                    &mut consider_ctx,
                );
            }
        }

        if let (Some(kid), Some(push0_cost)) = (push0_kid, push0_cost) {
            let bit = 1u64 << kid;
            let dominated = (duplicable & bit) != 0 && push0_cost >= dup_cost_for_kid[kid as usize];
            if !dominated {
                let next = prep_insert(entry.state, kid, problem.preserve_mask, false, cfg.max_len);
                consider_prep_succ(
                    next,
                    g.saturating_add(operand_prep_insert_cost(
                        entry.state,
                        next,
                        kid,
                        &problem.goal_counts,
                        problem.last_use_mask,
                        push0_cost,
                        surplus_last_use_penalty,
                    )),
                    entry.state,
                    Step::PushImm(kid),
                    &mut consider_ctx,
                );
            }
        }

        for &kid in &problem.materializable_imm {
            if Some(kid) == push0_kid {
                continue;
            }
            let KeyInfo::Imm { canon, .. } = problem.key_infos[kid as usize] else {
                unreachable!("expected imm key info")
            };
            let push_cost = cost.cost_push_imm(canon);
            let bit = 1u64 << kid;
            let dominated = (duplicable & bit) != 0 && push_cost >= dup_cost_for_kid[kid as usize];
            if dominated {
                continue;
            }

            let next = prep_insert(entry.state, kid, problem.preserve_mask, false, cfg.max_len);
            consider_prep_succ(
                next,
                g.saturating_add(operand_prep_insert_cost(
                    entry.state,
                    next,
                    kid,
                    &problem.goal_counts,
                    problem.last_use_mask,
                    push_cost,
                    surplus_last_use_penalty,
                )),
                entry.state,
                Step::PushImm(kid),
                &mut consider_ctx,
            );
        }

        for &kid in &problem.materializable_val {
            let bit = 1u64 << kid;
            let set_mem = (problem.preserve_mask & bit) != 0;
            let KeyInfo::Val { vid } = problem.key_infos[kid as usize] else {
                unreachable!("expected val key info")
            };
            let next = prep_insert(
                entry.state,
                kid,
                problem.preserve_mask,
                set_mem,
                cfg.max_len,
            );
            consider_prep_succ(
                next,
                g.saturating_add(operand_prep_insert_cost(
                    entry.state,
                    next,
                    kid,
                    &problem.goal_counts,
                    problem.last_use_mask,
                    cost.cost_load(vid),
                    surplus_last_use_penalty,
                )),
                entry.state,
                Step::LoadVal(kid),
                &mut consider_ctx,
            );
        }
    }

    plan_cache()
        .lock()
        .unwrap()
        .insert(cache_key, PlanCacheVal::Steps(incumbent_steps.clone()));

    Some(NormalizePlan {
        cost: incumbent_cost,
        steps: incumbent_steps,
        key_infos: problem.key_infos,
        goal_keys: problem.goal_keys,
    })
}

pub(super) fn rebuild_operand_prep_plan(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    args: &[ValueId],
    consume_last_use: &BitSet<ValueId>,
    cost: &impl CostModel,
    cfg: SearchCfg,
    steps: Vec<Step>,
) -> Option<NormalizePlan> {
    if args.is_empty() {
        return Some(NormalizePlan {
            cost: Cost::default(),
            steps,
            key_infos: Vec::new(),
            goal_keys: Vec::new(),
        });
    }

    let problem = build_operand_prep_problem(ctx, stack, args, consume_last_use, cfg)?;
    Some(NormalizePlan {
        cost: cost_for_steps(&steps, &problem.key_infos, cost),
        steps,
        key_infos: problem.key_infos,
        goal_keys: problem.goal_keys,
    })
}

fn canonical_key(ctx: &StackifyContext<'_>, v: ValueId) -> Key {
    if ctx.func.dfg.value_is_imm(v) {
        let imm = ctx
            .func
            .dfg
            .value_imm(v)
            .expect("imm value missing payload");
        Key::Imm(imm.as_i256())
    } else {
        Key::Val(v)
    }
}

fn intern_key(
    ctx: &StackifyContext<'_>,
    key: Key,
    rep_vid: ValueId,
    ids: &mut FxHashMap<Key, u8>,
    infos: &mut Vec<KeyInfo>,
) -> Option<u8> {
    if let Some(&kid) = ids.get(&key) {
        return Some(kid);
    }

    if infos.len() >= 64 {
        return None;
    }

    let kid = infos.len() as u8;
    ids.insert(key, kid);

    let info = match key {
        Key::Imm(canon) => {
            let rep_imm = ctx
                .func
                .dfg
                .value_imm(rep_vid)
                .expect("imm value missing payload");
            KeyInfo::Imm {
                canon,
                rep_vid,
                rep_imm,
            }
        }
        Key::Val(vid) => KeyInfo::Val { vid },
    };
    infos.push(info);
    Some(kid)
}

fn estimate_flush_rebuild_cost(
    ctx: &StackifyContext<'_>,
    stack: &SymStack,
    desired: &[ValueId],
    cost: &impl CostModel,
) -> Cost {
    let base_len = stack.common_suffix_len(desired);
    let mut total = Cost::default();

    let pop_count = stack.len_above_func_ret().saturating_sub(base_len);
    for _ in 0..pop_count {
        total = total.saturating_add(cost.cost_pop());
    }

    for &v in &desired[..desired.len().saturating_sub(base_len)] {
        if ctx.func.dfg.value_is_imm(v) {
            let imm = ctx
                .func
                .dfg
                .value_imm(v)
                .expect("imm value missing payload")
                .as_i256();
            total = total.saturating_add(cost.cost_push_imm(imm));
        } else {
            total = total.saturating_add(cost.cost_load(v));
        }
    }

    total
}

fn reconstruct_steps(
    start: PackedState,
    goal: PackedState,
    parent: &FxHashMap<PackedState, (PackedState, Step)>,
) -> Option<Vec<Step>> {
    let mut steps: Vec<Step> = Vec::new();
    let mut cur = goal;
    while cur != start {
        let &(prev, step) = parent.get(&cur)?;
        steps.push(step);
        cur = prev;
    }
    steps.reverse();
    Some(steps)
}

fn compute_goal_counts(goal_keys: &[u8]) -> [u8; 64] {
    let mut counts = [0u8; 64];
    for &kid in goal_keys {
        debug_assert!(kid < 64);
        counts[kid as usize] = counts[kid as usize].saturating_add(1);
    }
    counts
}

fn compute_counts(keys: &[u8]) -> [u8; 64] {
    let mut counts = [0u8; 64];
    for &kid in keys {
        debug_assert!(kid < 64);
        counts[kid as usize] = counts[kid as usize].saturating_add(1);
    }
    counts
}

fn minimal_dup_gas(cost: &impl CostModel, dup_max: usize) -> u32 {
    if dup_max == 0 {
        return u32::MAX;
    }

    let mut best = cost.cost_dup(0).gas;
    for pos in 1..dup_max {
        best = best.min(cost.cost_dup(pos as u8).gas);
    }
    best
}

pub(super) fn cost_for_steps(steps: &[Step], key_infos: &[KeyInfo], cost: &impl CostModel) -> Cost {
    steps.iter().fold(Cost::default(), |acc, step| {
        let c = match *step {
            Step::Pop => cost.cost_pop(),
            Step::Dup(pos) => cost.cost_dup(pos),
            Step::Swap(depth) => cost.cost_swap(depth),
            Step::PushImm(kid) => {
                let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
                    unreachable!("expected imm key info")
                };
                cost.cost_push_imm(canon)
            }
            Step::LoadVal(kid) => {
                let KeyInfo::Val { vid } = key_infos[kid as usize] else {
                    unreachable!("expected val key info")
                };
                cost.cost_load(vid)
            }
        };
        acc.saturating_add(c)
    })
}

fn apply_step_to_vec(cur: &mut Vec<u8>, step: Step) {
    match step {
        Step::Pop => {
            cur.remove(0);
        }
        Step::Dup(pos) => {
            let kid = cur[pos as usize];
            cur.insert(0, kid);
        }
        Step::Swap(depth) => {
            cur.swap(0, depth as usize);
        }
        Step::PushImm(kid) | Step::LoadVal(kid) => {
            cur.insert(0, kid);
        }
    }
}

fn apply_repair_step_to_vec(cur: &mut Vec<u8>, suffix_ctx_keys: &[u8], step: Step) {
    match step {
        Step::Pop => {
            cur.remove(0);
        }
        Step::Dup(pos) => {
            let pos = pos as usize;
            assert!(
                pos < cur.len() + suffix_ctx_keys.len(),
                "repair dup source out of range: pos={pos} cur_len={} suffix_len={}",
                cur.len(),
                suffix_ctx_keys.len()
            );
            let kid = if pos < cur.len() {
                cur[pos]
            } else {
                suffix_ctx_keys[pos - cur.len()]
            };
            cur.insert(0, kid);
        }
        Step::Swap(depth) => {
            cur.swap(0, depth as usize);
        }
        Step::PushImm(kid) | Step::LoadVal(kid) => {
            cur.insert(0, kid);
        }
    }
}

fn build_star_swap_plan(cur: &mut Vec<u8>, goal: &[u8], swap_max: usize) -> Option<Vec<Step>> {
    if cur.len() != goal.len() {
        return None;
    }
    if cur.len() > swap_max {
        return None;
    }

    if compute_counts(cur) != compute_counts(goal) {
        return None;
    }

    let n = cur.len();
    if n <= 1 {
        return Some(Vec::new());
    }

    let mut goal_pos: Vec<Vec<usize>> = vec![Vec::new(); 64];
    for (idx, &kid) in goal.iter().enumerate() {
        goal_pos[kid as usize].push(idx);
    }

    let mut next_idx = [0usize; 64];
    let mut p: Vec<usize> = vec![0usize; n];
    for (i, &kid) in cur.iter().enumerate() {
        let kid = kid as usize;
        let pos_list = &goal_pos[kid];
        let next = next_idx[kid];
        if next >= pos_list.len() {
            return None;
        }
        p[i] = pos_list[next];
        next_idx[kid] += 1;
    }

    // Generate a minimal star-transposition sequence for `p`:
    // - cycle containing 0: (0 a1 a2 .. ak) => (0 a1)(0 a2)...(0 ak)
    // - other cycle: (a1 a2 .. ak) => (0 a1)(0 a2)...(0 ak)(0 a1)
    let mut visited = vec![false; n];
    let mut steps: Vec<Step> = Vec::new();

    for i in 0..n {
        if visited[i] {
            continue;
        }
        let mut cycle: Vec<usize> = Vec::new();
        let mut cur_idx = i;
        while !visited[cur_idx] {
            visited[cur_idx] = true;
            cycle.push(cur_idx);
            cur_idx = p[cur_idx];
        }

        if cycle.len() <= 1 {
            continue;
        }

        if let Some(z) = cycle.iter().position(|&x| x == 0) {
            cycle.rotate_left(z);
            debug_assert_eq!(cycle[0], 0);
            for &idx in &cycle[1..] {
                if idx >= swap_max {
                    return None;
                }
                steps.push(Step::Swap(idx as u8));
            }
        } else {
            for &idx in &cycle {
                if idx >= swap_max {
                    return None;
                }
                steps.push(Step::Swap(idx as u8));
            }
            let first = cycle[0];
            if first >= swap_max {
                return None;
            }
            steps.push(Step::Swap(first as u8));
        }
    }

    for step in steps.iter().copied() {
        apply_step_to_vec(cur, step);
    }
    if cur.as_slice() != goal {
        return None;
    }

    Some(steps)
}

fn build_delete_tail_under_prefix_upper_bound(
    start_keys: &[u8],
    goal_keys: &[u8],
    cfg: SearchCfg,
) -> Option<Vec<Step>> {
    if goal_keys.len() >= start_keys.len() {
        return None;
    }
    if !start_keys.starts_with(goal_keys) {
        return None;
    }
    if start_keys.len() > cfg.swap_max {
        return None;
    }
    if goal_keys.len() > cfg.swap_max {
        return None;
    }

    let keep = goal_keys.len();
    let mut cur: Vec<u8> = start_keys.to_vec();
    let mut steps: Vec<Step> = Vec::new();

    let mut dead = cur.len().saturating_sub(keep);
    let bury = keep.min(dead);

    for i in 0..bury {
        let cur_len = cur.len();
        let depth = cur_len.saturating_sub(1).saturating_sub(i);
        if depth == 0 || depth >= cfg.swap_max {
            return None;
        }
        steps.push(Step::Swap(depth as u8));
        apply_step_to_vec(&mut cur, Step::Swap(depth as u8));
        steps.push(Step::Pop);
        apply_step_to_vec(&mut cur, Step::Pop);
        dead = dead.saturating_sub(1);
    }

    for _ in 0..dead {
        steps.push(Step::Pop);
        apply_step_to_vec(&mut cur, Step::Pop);
    }

    if cur.as_slice() != goal_keys {
        let swap_steps = build_star_swap_plan(&mut cur, goal_keys, cfg.swap_max)?;
        steps.extend(swap_steps);
    }
    (cur.as_slice() == goal_keys).then_some(steps)
}

fn trim_excess_keys<F>(
    cur: &mut Vec<u8>,
    cur_counts: &mut [u8; 64],
    goal_counts: &[u8; 64],
    swap_max: usize,
    steps: &mut Vec<Step>,
    mut apply_step: F,
) -> Option<()>
where
    F: FnMut(&mut Vec<u8>, Step),
{
    while let Some((pos, kid)) = cur
        .iter()
        .copied()
        .enumerate()
        .find(|(_, kid)| cur_counts[*kid as usize] > goal_counts[*kid as usize])
    {
        if pos != 0 {
            if pos >= swap_max {
                return None;
            }
            let step = Step::Swap(pos as u8);
            steps.push(step);
            apply_step(cur, step);
        }

        steps.push(Step::Pop);
        apply_step(cur, Step::Pop);
        cur_counts[kid as usize] = cur_counts[kid as usize].saturating_sub(1);
    }

    Some(())
}

fn finish_count_fixup_plan(
    cur: &mut Vec<u8>,
    cur_counts: &[u8; 64],
    goal_keys: &[u8],
    goal_counts: &[u8; 64],
    swap_max: usize,
    steps: &mut Vec<Step>,
) -> Option<()> {
    if cur.len() != goal_keys.len() || cur_counts != goal_counts {
        return None;
    }

    steps.extend(build_star_swap_plan(cur, goal_keys, swap_max)?);
    (cur.as_slice() == goal_keys).then_some(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CopySourceCandidate {
    CurrentDup { kid: u8, pos: usize, cost: Cost },
    CurrentSwapDup { kid: u8, pos: usize, cost: Cost },
    SuffixDup { kid: u8, off: usize, cost: Cost },
    PushImm { kid: u8, cost: Cost },
    LoadVal { kid: u8, cost: Cost },
}

impl CopySourceCandidate {
    fn kid(self) -> u8 {
        match self {
            Self::CurrentDup { kid, .. }
            | Self::CurrentSwapDup { kid, .. }
            | Self::SuffixDup { kid, .. }
            | Self::PushImm { kid, .. }
            | Self::LoadVal { kid, .. } => kid,
        }
    }

    fn cost(self) -> Cost {
        match self {
            Self::CurrentDup { cost, .. }
            | Self::CurrentSwapDup { cost, .. }
            | Self::SuffixDup { cost, .. }
            | Self::PushImm { cost, .. }
            | Self::LoadVal { cost, .. } => cost,
        }
    }

    fn priority(self) -> u8 {
        match self {
            Self::CurrentDup { .. } => 0,
            Self::CurrentSwapDup { .. } => 1,
            Self::SuffixDup { .. } => 2,
            Self::PushImm { .. } => 3,
            Self::LoadVal { .. } => 4,
        }
    }

    fn suffix_margin(self, cur_len: usize, dup_max: usize) -> Option<usize> {
        let Self::SuffixDup { off, .. } = self else {
            return None;
        };
        Some(dup_max - (cur_len + off))
    }

    fn suffix_off(self) -> Option<usize> {
        let Self::SuffixDup { off, .. } = self else {
            return None;
        };
        Some(off)
    }

    fn cmp_general(lhs: &Self, rhs: &Self) -> Ordering {
        lhs.cost()
            .cmp(&rhs.cost())
            .then_with(|| lhs.priority().cmp(&rhs.priority()))
            .then_with(|| lhs.kid().cmp(&rhs.kid()))
    }

    fn cmp_within_source(lhs: &Self, rhs: &Self) -> Ordering {
        match (*lhs, *rhs) {
            (
                Self::CurrentDup {
                    cost: lhs_cost,
                    pos: lhs_pos,
                    ..
                },
                Self::CurrentDup {
                    cost: rhs_cost,
                    pos: rhs_pos,
                    ..
                },
            )
            | (
                Self::CurrentSwapDup {
                    cost: lhs_cost,
                    pos: lhs_pos,
                    ..
                },
                Self::CurrentSwapDup {
                    cost: rhs_cost,
                    pos: rhs_pos,
                    ..
                },
            ) => lhs_cost.cmp(&rhs_cost).then_with(|| lhs_pos.cmp(&rhs_pos)),
            (
                Self::SuffixDup {
                    cost: lhs_cost,
                    off: lhs_off,
                    ..
                },
                Self::SuffixDup {
                    cost: rhs_cost,
                    off: rhs_off,
                    ..
                },
            ) => lhs_cost.cmp(&rhs_cost).then_with(|| rhs_off.cmp(&lhs_off)),
            _ => unreachable!("cross-source comparison"),
        }
    }

    fn cmp_suffix_urgency(lhs: &Self, rhs: &Self, cur_len: usize, dup_max: usize) -> Ordering {
        lhs.suffix_margin(cur_len, dup_max)
            .cmp(&rhs.suffix_margin(cur_len, dup_max))
            .then_with(|| rhs.suffix_off().cmp(&lhs.suffix_off()))
            .then_with(|| Self::cmp_general(lhs, rhs))
    }
}

#[derive(Clone, Copy, Debug)]
struct CopySourceChoices {
    current_dup: Option<CopySourceCandidate>,
    current_swap_dup: Option<CopySourceCandidate>,
    suffix_dup: Option<CopySourceCandidate>,
    materialize: CopySourceCandidate,
}

impl CopySourceChoices {
    fn best(self) -> CopySourceCandidate {
        [
            self.current_dup,
            self.current_swap_dup,
            self.suffix_dup,
            Some(self.materialize),
        ]
        .into_iter()
        .flatten()
        .min_by(CopySourceCandidate::cmp_general)
        .expect("materialization candidate missing")
    }

    fn urgent_suffix(self) -> Option<CopySourceCandidate> {
        if self.current_dup.is_none() && self.current_swap_dup.is_none() {
            self.suffix_dup
        } else {
            None
        }
    }

    fn best_direct_insert(self) -> CopySourceCandidate {
        self.current_dup.unwrap_or(self.materialize)
    }
}

fn best_current_dup_candidate<C: CostModel, F: Fn(usize) -> u8 + Copy>(
    current_len: usize,
    current_key_at: F,
    kid: u8,
    cost: &C,
    dup_max: usize,
) -> Option<CopySourceCandidate> {
    if dup_max == 0 {
        return None;
    }

    (0..current_len.min(dup_max))
        .filter(|&pos| current_key_at(pos) == kid)
        .map(|pos| CopySourceCandidate::CurrentDup {
            kid,
            pos,
            cost: cost.cost_dup(pos as u8),
        })
        .min_by(CopySourceCandidate::cmp_within_source)
}

fn best_current_swap_dup_candidate<C: CostModel, F: Fn(usize) -> u8 + Copy>(
    current_len: usize,
    current_key_at: F,
    kid: u8,
    cost: &C,
    cfg: SearchCfg,
) -> Option<CopySourceCandidate> {
    if cfg.dup_max == 0 {
        return None;
    }

    (cfg.dup_max.min(current_len)..current_len.min(cfg.swap_max))
        .filter(|&pos| current_key_at(pos) == kid)
        .map(|pos| CopySourceCandidate::CurrentSwapDup {
            kid,
            pos,
            cost: cost.cost_swap(pos as u8).saturating_add(cost.cost_dup(0)),
        })
        .min_by(CopySourceCandidate::cmp_within_source)
}

fn best_suffix_dup_candidate<C: CostModel>(
    current_len: usize,
    suffix_ctx_keys: &[u8],
    kid: u8,
    cost: &C,
    dup_max: usize,
) -> Option<CopySourceCandidate> {
    if dup_max == 0 {
        return None;
    }

    suffix_ctx_keys
        .iter()
        .enumerate()
        .filter(|(off, suffix_kid)| **suffix_kid == kid && current_len + *off < dup_max)
        .map(|(off, _)| CopySourceCandidate::SuffixDup {
            kid,
            off,
            cost: cost.cost_dup((current_len + off) as u8),
        })
        .min_by(CopySourceCandidate::cmp_within_source)
}

fn materialize_copy_source<C: CostModel>(
    key_infos: &[KeyInfo],
    cost: &C,
    kid: u8,
) -> CopySourceCandidate {
    match key_infos[kid as usize] {
        KeyInfo::Imm { canon, .. } => CopySourceCandidate::PushImm {
            kid,
            cost: cost.cost_push_imm(canon),
        },
        KeyInfo::Val { vid } => CopySourceCandidate::LoadVal {
            kid,
            cost: cost.cost_load(vid),
        },
    }
}

fn copy_source_choices_for_kid<C: CostModel, F: Fn(usize) -> u8 + Copy>(
    current_len: usize,
    current_key_at: F,
    suffix_ctx_keys: &[u8],
    key_infos: &[KeyInfo],
    cost: &C,
    cfg: SearchCfg,
    kid: u8,
) -> CopySourceChoices {
    let current_dup =
        best_current_dup_candidate(current_len, current_key_at, kid, cost, cfg.dup_max);
    let current_swap_dup = current_dup
        .is_none()
        .then(|| best_current_swap_dup_candidate(current_len, current_key_at, kid, cost, cfg))
        .flatten();
    CopySourceChoices {
        current_dup,
        current_swap_dup,
        suffix_dup: best_suffix_dup_candidate(current_len, suffix_ctx_keys, kid, cost, cfg.dup_max),
        materialize: materialize_copy_source(key_infos, cost, kid),
    }
}

#[derive(Clone, Debug)]
struct RepairTrimChoice {
    next: Vec<u8>,
    pos: usize,
    kid: u8,
    suffix_len: usize,
    immediate_cost: Cost,
    future_copy_cost: Cost,
}

impl RepairTrimChoice {
    fn total_cost(&self) -> Cost {
        self.immediate_cost.saturating_add(self.future_copy_cost)
    }

    fn cmp(lhs: &Self, rhs: &Self) -> Ordering {
        lhs.suffix_len
            .cmp(&rhs.suffix_len)
            .reverse()
            .then_with(|| lhs.total_cost().cmp(&rhs.total_cost()))
            .then_with(|| lhs.immediate_cost.cmp(&rhs.immediate_cost))
            .then_with(|| lhs.pos.cmp(&rhs.pos))
            .then_with(|| lhs.kid.cmp(&rhs.kid))
    }
}

struct RepairGreedyEnv<'a, C> {
    goal_keys: &'a [u8],
    goal_counts: &'a [u8; 64],
    suffix_ctx_keys: &'a [u8],
    key_infos: &'a [KeyInfo],
    cost: &'a C,
    cfg: SearchCfg,
}

fn repair_best_candidate_for_kid<C: CostModel>(
    cur: &[u8],
    env: &RepairGreedyEnv<'_, C>,
    kid: u8,
) -> Option<(CopySourceCandidate, Option<CopySourceCandidate>)> {
    let sources = copy_source_choices_for_kid(
        cur.len(),
        |pos| cur[pos],
        env.suffix_ctx_keys,
        env.key_infos,
        env.cost,
        env.cfg,
        kid,
    );
    Some((sources.best(), sources.urgent_suffix()))
}

fn best_copy_cost_in_state<C: CostModel>(
    cur: &[u8],
    env: &RepairGreedyEnv<'_, C>,
    kid: u8,
) -> Option<Cost> {
    if env.goal_counts[kid as usize] == 0 {
        return Some(Cost::default());
    }
    repair_best_candidate_for_kid(cur, env, kid).map(|(candidate, _)| candidate.cost())
}

fn trim_repair_excess_keys<C: CostModel>(
    cur: &mut Vec<u8>,
    cur_counts: &mut [u8; 64],
    env: &RepairGreedyEnv<'_, C>,
    steps: &mut Vec<Step>,
) -> Option<()> {
    while cur
        .iter()
        .copied()
        .any(|kid| cur_counts[kid as usize] > env.goal_counts[kid as usize])
    {
        let mut best: Option<RepairTrimChoice> = None;

        for (pos, kid) in cur.iter().copied().enumerate() {
            if cur_counts[kid as usize] <= env.goal_counts[kid as usize] {
                continue;
            }
            if pos >= env.cfg.swap_max {
                continue;
            }

            let mut next = cur.clone();
            let immediate_cost = if pos == 0 {
                apply_repair_step_to_vec(&mut next, env.suffix_ctx_keys, Step::Pop);
                env.cost.cost_pop()
            } else {
                apply_repair_step_to_vec(&mut next, env.suffix_ctx_keys, Step::Swap(pos as u8));
                apply_repair_step_to_vec(&mut next, env.suffix_ctx_keys, Step::Pop);
                env.cost
                    .cost_swap(pos as u8)
                    .saturating_add(env.cost.cost_pop())
            };
            let future_copy_cost = best_copy_cost_in_state(&next, env, kid)?;
            let choice = RepairTrimChoice {
                suffix_len: common_suffix_len_keys(&next, env.goal_keys),
                immediate_cost,
                future_copy_cost,
                next,
                pos,
                kid,
            };

            if best
                .as_ref()
                .map(|best| RepairTrimChoice::cmp(&choice, best).is_lt())
                .unwrap_or(true)
            {
                best = Some(choice);
            }
        }

        let choice = best?;
        if choice.pos != 0 {
            steps.push(Step::Swap(choice.pos as u8));
        }
        steps.push(Step::Pop);
        *cur = choice.next;
        cur_counts[choice.kid as usize] = cur_counts[choice.kid as usize].saturating_sub(1);
    }

    Some(())
}

fn apply_repair_candidate(
    cur: &mut Vec<u8>,
    suffix_ctx_keys: &[u8],
    steps: &mut Vec<Step>,
    candidate: CopySourceCandidate,
) -> u8 {
    let kid = candidate.kid();
    match candidate {
        CopySourceCandidate::CurrentDup { pos, .. } => {
            let step = Step::Dup(pos as u8);
            steps.push(step);
            apply_repair_step_to_vec(cur, suffix_ctx_keys, step);
        }
        CopySourceCandidate::CurrentSwapDup { pos, .. } => {
            let step = Step::Swap(pos as u8);
            steps.push(step);
            apply_repair_step_to_vec(cur, suffix_ctx_keys, step);
            steps.push(Step::Dup(0));
            apply_repair_step_to_vec(cur, suffix_ctx_keys, Step::Dup(0));
        }
        CopySourceCandidate::SuffixDup { off, .. } => {
            let pos = cur.len() + off;
            let step = Step::Dup(pos as u8);
            steps.push(step);
            apply_repair_step_to_vec(cur, suffix_ctx_keys, step);
        }
        CopySourceCandidate::PushImm { .. } => {
            let step = Step::PushImm(kid);
            steps.push(step);
            apply_repair_step_to_vec(cur, suffix_ctx_keys, step);
        }
        CopySourceCandidate::LoadVal { .. } => {
            let step = Step::LoadVal(kid);
            steps.push(step);
            apply_repair_step_to_vec(cur, suffix_ctx_keys, step);
        }
    }
    kid
}

fn build_greedy_repair_prefix_upper_bound(
    start_keys: &[u8],
    goal_keys: &[u8],
    suffix_ctx_keys: &[u8],
    key_infos: &[KeyInfo],
    cost: &impl CostModel,
    cfg: SearchCfg,
) -> Option<Vec<Step>> {
    if start_keys.len() > cfg.swap_max
        || goal_keys.len() > cfg.swap_max
        || goal_keys.len() > cfg.max_len
    {
        return None;
    }

    let goal_counts = compute_goal_counts(goal_keys);
    let mut cur = start_keys.to_vec();
    let mut cur_counts = compute_counts(&cur);
    let mut steps = Vec::new();
    let env = RepairGreedyEnv {
        goal_keys,
        goal_counts: &goal_counts,
        suffix_ctx_keys,
        key_infos,
        cost,
        cfg,
    };

    trim_repair_excess_keys(&mut cur, &mut cur_counts, &env, &mut steps)?;

    while cur_counts != goal_counts {
        if cur.len() >= cfg.max_len {
            return None;
        }

        let mut urgent_suffix_candidate: Option<CopySourceCandidate> = None;
        let matched_suffix = common_suffix_len_keys(&cur, goal_keys);
        let target_idx = goal_keys.len().checked_sub(matched_suffix + 1)?;
        let target_kid = goal_keys[target_idx];
        if cur_counts[target_kid as usize] >= goal_counts[target_kid as usize] {
            return None;
        }
        let mut target_candidate: Option<CopySourceCandidate> = None;

        for (kid, &want) in goal_counts.iter().enumerate() {
            if cur_counts[kid] >= want {
                continue;
            }

            let kid = kid as u8;
            let (candidate, urgent_suffix) = repair_best_candidate_for_kid(&cur, &env, kid)?;

            if kid == target_kid {
                target_candidate = Some(candidate);
            }

            if let Some(urgent_suffix) = urgent_suffix
                && urgent_suffix_candidate
                    .map(|best| {
                        CopySourceCandidate::cmp_suffix_urgency(
                            &urgent_suffix,
                            &best,
                            cur.len(),
                            cfg.dup_max,
                        )
                        .is_lt()
                    })
                    .unwrap_or(true)
            {
                urgent_suffix_candidate = Some(urgent_suffix);
            }
        }

        let candidate = urgent_suffix_candidate.or(target_candidate)?;
        let kid = apply_repair_candidate(&mut cur, suffix_ctx_keys, &mut steps, candidate);
        cur_counts[kid as usize] = cur_counts[kid as usize].saturating_add(1);
    }

    finish_count_fixup_plan(
        &mut cur,
        &cur_counts,
        goal_keys,
        &goal_counts,
        cfg.swap_max,
        &mut steps,
    )?;
    Some(steps)
}

fn build_dup_and_star_swap_upper_bound(
    start_keys: &[u8],
    goal_keys: &[u8],
    goal_counts: &[u8; 64],
    cfg: SearchCfg,
) -> Option<Vec<Step>> {
    if goal_keys.len() > cfg.max_len {
        return None;
    }

    let mut cur: Vec<u8> = start_keys.to_vec();
    let mut cur_counts = compute_counts(&cur);

    // This upper-bound builder only handles cases where every required key already exists
    // (so we never need PUSH/LOAD).
    for (kid, &want) in goal_counts.iter().enumerate() {
        if want != 0 && cur_counts[kid] == 0 {
            return None;
        }
    }

    let mut steps: Vec<Step> = Vec::new();

    trim_excess_keys(
        &mut cur,
        &mut cur_counts,
        goal_counts,
        cfg.swap_max,
        &mut steps,
        apply_step_to_vec,
    )?;

    // 2) Duplicate keys to satisfy any remaining deficits.
    if cfg.dup_max == 0 {
        return None;
    }
    for (kid, &want) in goal_counts.iter().enumerate() {
        let mut have = cur_counts[kid];
        while have < want {
            if cur.len() >= cfg.max_len {
                return None;
            }

            let pos = cur
                .iter()
                .position(|&x| x == kid as u8)
                .expect("deficit key missing from vector");

            if pos < cfg.dup_max {
                steps.push(Step::Dup(pos as u8));
                apply_step_to_vec(&mut cur, Step::Dup(pos as u8));
            } else {
                // Only reachable when `pos == 16` and `dup_max == 16`.
                if pos >= cfg.swap_max {
                    return None;
                }
                steps.push(Step::Swap(pos as u8));
                apply_step_to_vec(&mut cur, Step::Swap(pos as u8));
                steps.push(Step::Dup(0));
                apply_step_to_vec(&mut cur, Step::Dup(0));
            }

            have += 1;
            cur_counts[kid] = have;
        }
    }

    finish_count_fixup_plan(
        &mut cur,
        &cur_counts,
        goal_keys,
        goal_counts,
        cfg.swap_max,
        &mut steps,
    )?;
    debug_assert_eq!(cur.as_slice(), goal_keys);
    Some(steps)
}

fn materialize_cost_gas(kid: u8, key_infos: &[KeyInfo], cost: &impl CostModel) -> u32 {
    match key_infos[kid as usize] {
        KeyInfo::Imm { canon, .. } => cost.cost_push_imm(canon).gas,
        KeyInfo::Val { vid } => cost.cost_load(vid).gas,
    }
}

fn heuristic_with_ctx(
    state: PackedState,
    goal_counts: &[u8; 64],
    ctx_present: u64,
    pop_gas: u32,
    dup_gas: u32,
    key_infos: &[KeyInfo],
    cost: &impl CostModel,
) -> Cost {
    let mut cur_counts = [0u8; 64];
    for i in 0..state.len() {
        let kid = state.get(i) as usize;
        cur_counts[kid] = cur_counts[kid].saturating_add(1);
    }

    // Admissible lower bound for remaining *gas*:
    // - pop all surplus keys
    // - materialize/dup missing keys, with a "bootstrap" materialization only when the key is
    //   absent from both the current state and the (reachable) frozen context.
    let mut gas = 0u32;
    for (kid, &want) in goal_counts.iter().enumerate() {
        let have = cur_counts[kid];

        if have > want {
            gas = gas.saturating_add(pop_gas.saturating_mul((have - want) as u32));
            continue;
        }
        if have == want {
            continue;
        }

        let def = (want - have) as u32;
        let mat = materialize_cost_gas(kid as u8, key_infos, cost);
        let per_copy = mat.min(dup_gas);

        if have == 0 && (ctx_present & (1u64 << kid)) == 0 {
            gas = gas.saturating_add(mat);
            if def > 1 {
                gas = gas.saturating_add(per_copy.saturating_mul(def - 1));
            }
        } else {
            gas = gas.saturating_add(per_copy.saturating_mul(def));
        }
    }

    Cost { gas, bytes: 0 }
}

fn heuristic(
    state: PackedState,
    goal_counts: &[u8; 64],
    pop_gas: u32,
    dup_gas: u32,
    key_infos: &[KeyInfo],
    cost: &impl CostModel,
) -> Cost {
    heuristic_with_ctx(state, goal_counts, 0, pop_gas, dup_gas, key_infos, cost)
}

fn prep_insert(
    mut state: PrepState,
    kid: u8,
    preserve_mask: u64,
    set_mem: bool,
    max_len: usize,
) -> PrepState {
    debug_assert!(max_len != 0, "operand_prep_search max_len must be non-zero");

    let bit = 1u64 << kid;
    if set_mem && (preserve_mask & bit) != 0 {
        state.mem |= bit;
    }

    let dropped = if state.window.len() == max_len {
        Some(state.window.get(max_len - 1))
    } else {
        None
    };

    let window = if state.window.len() < max_len {
        state.window.push(kid)
    } else {
        // Insert at the top, shifting everything down by one and dropping the last slot,
        // while keeping the packed representation within bounds.
        let keep_len = max_len.saturating_sub(1);
        let keep_bits = PackedState::SLOT_BITS * keep_len as u32;
        let keep_mask = if keep_bits == 0 {
            0u128
        } else {
            (1u128 << keep_bits) - 1
        };
        let data = ((state.window.data & keep_mask) << PackedState::SLOT_BITS) | kid as u128;
        PackedState {
            len: max_len as u8,
            data,
        }
    };

    let mut tail = state.tail;
    if let Some(dropped) = dropped {
        let bit = 1u64 << dropped;
        if (preserve_mask & bit) != 0 && (state.mem & bit) == 0 {
            tail |= bit;
        }
    }

    tail &= preserve_mask;
    tail &= !state.mem;
    state.mem &= preserve_mask;

    state.window = window;
    state.tail = tail;
    state
}

fn prep_copy_count(state: PrepState, kid: u8) -> u8 {
    let mut count = u8::from((state.tail & (1u64 << kid)) != 0);
    for idx in 0..state.window.len() {
        if state.window.get(idx) == kid {
            count = count.saturating_add(1);
        }
    }
    count
}

fn operand_prep_insert_cost(
    state: PrepState,
    next: PrepState,
    kid: u8,
    goal_counts: &[u8; 64],
    last_use_mask: u64,
    base: Cost,
    surplus_last_use_penalty: Cost,
) -> Cost {
    let bit = 1u64 << kid;
    if (last_use_mask & bit) == 0 {
        return base;
    }

    let need = goal_counts[kid as usize];
    let before = prep_copy_count(state, kid);
    let after = prep_copy_count(next, kid);
    if before >= need && after > before {
        return base.saturating_add(surplus_last_use_penalty);
    }

    base
}

fn operand_prep_goal(
    state: PrepState,
    goal_keys: &[u8],
    preserve_mask: u64,
    goal_counts: &[u8; 64],
) -> bool {
    if state.window.len() < goal_keys.len() {
        return false;
    }
    for (idx, &kid) in goal_keys.iter().enumerate() {
        if state.window.get(idx) != kid {
            return false;
        }
    }

    if preserve_mask == 0 {
        return true;
    }

    let mut win_counts = [0u8; 64];
    for i in 0..state.window.len() {
        let kid = state.window.get(i) as usize;
        win_counts[kid] = win_counts[kid].saturating_add(1);
    }

    let mut mask = preserve_mask;
    while mask != 0 {
        let kid = mask.trailing_zeros() as usize;
        mask &= mask - 1;
        let bit = 1u64 << kid;

        if (state.mem & bit) != 0 {
            continue;
        }

        let want = goal_counts[kid].saturating_add(1);
        let have = win_counts[kid].saturating_add(u8::from((state.tail & bit) != 0));
        if have < want {
            return false;
        }
    }

    true
}

fn heuristic_operand_prep<C: CostModel>(
    state: PrepState,
    goal_counts: &[u8; 64],
    preserve_mask: u64,
    dup_gas: u32,
    key_infos: &[KeyInfo],
    cost: &C,
) -> Cost {
    let mut win_counts = [0u8; 64];
    for i in 0..state.window.len() {
        let kid = state.window.get(i) as usize;
        win_counts[kid] = win_counts[kid].saturating_add(1);
    }

    let mut gas = 0u32;
    for (kid, &need_operands) in goal_counts.iter().enumerate() {
        if need_operands == 0 {
            continue;
        }

        let bit = 1u64 << kid;
        let preserve_extra = u8::from((preserve_mask & bit) != 0 && (state.mem & bit) == 0);
        let need_total = need_operands.saturating_add(preserve_extra);

        let have_window = win_counts[kid];
        let have_total = have_window.saturating_add(u8::from((state.tail & bit) != 0));

        let missing_operands = need_operands.saturating_sub(have_window);
        let missing_total = need_total.saturating_sub(have_total);
        let missing = missing_operands.max(missing_total) as u32;

        if missing == 0 {
            continue;
        }

        let mat = materialize_cost_gas(kid as u8, key_infos, cost);
        let per_copy = mat.min(dup_gas);
        if have_window == 0 {
            gas = gas.saturating_add(mat);
            if missing > 1 {
                gas = gas.saturating_add(per_copy.saturating_mul(missing - 1));
            }
        } else {
            gas = gas.saturating_add(per_copy.saturating_mul(missing));
        }
    }

    Cost { gas, bytes: 0 }
}

struct PrepConsiderCtx<'a, C: CostModel> {
    goal_counts: &'a [u8; 64],
    preserve_mask: u64,
    dup_gas: u32,
    key_infos: &'a [KeyInfo],
    cost: &'a C,
    upper_bound: Cost,
    best: &'a mut FxHashMap<PrepState, Cost>,
    parent: &'a mut FxHashMap<PrepState, (PrepState, Step)>,
    open: &'a mut BinaryHeap<PrepQueueEntry>,
}

fn consider_prep_succ<C: CostModel>(
    state: PrepState,
    g: Cost,
    parent_state: PrepState,
    step: Step,
    ctx: &mut PrepConsiderCtx<'_, C>,
) {
    let h = heuristic_operand_prep(
        state,
        ctx.goal_counts,
        ctx.preserve_mask,
        ctx.dup_gas,
        ctx.key_infos,
        ctx.cost,
    );
    let f = g.saturating_add(h);
    if should_prune(f, ctx.upper_bound, true) {
        return;
    }

    let should_update = match ctx.best.get(&state) {
        None => true,
        Some(&prev) => g < prev,
    };
    if !should_update {
        return;
    }

    ctx.best.insert(state, g);
    ctx.parent.insert(state, (parent_state, step));
    ctx.open.push(PrepQueueEntry { f, g, state });
}

struct ConsiderCtx<'a, C: CostModel> {
    goal_counts: &'a [u8; 64],
    ctx_present: u64,
    pop_gas: u32,
    dup_gas: u32,
    key_infos: &'a [KeyInfo],
    cost: &'a C,
    upper_bound: Cost,
    have_incumbent: bool,
    best: &'a mut FxHashMap<PackedState, Cost>,
    parent: &'a mut FxHashMap<PackedState, (PackedState, Step)>,
    open: &'a mut BinaryHeap<QueueEntry>,
}

fn consider_succ<C: CostModel>(
    state: PackedState,
    g: Cost,
    parent_state: PackedState,
    step: Step,
    ctx: &mut ConsiderCtx<'_, C>,
) {
    let h = heuristic_with_ctx(
        state,
        ctx.goal_counts,
        ctx.ctx_present,
        ctx.pop_gas,
        ctx.dup_gas,
        ctx.key_infos,
        ctx.cost,
    );
    let f = g.saturating_add(h);
    if should_prune(f, ctx.upper_bound, ctx.have_incumbent) {
        return;
    }

    let should_update = match ctx.best.get(&state) {
        None => true,
        Some(&prev) => g < prev,
    };
    if !should_update {
        return;
    }

    ctx.best.insert(state, g);
    ctx.parent.insert(state, (parent_state, step));
    ctx.open.push(QueueEntry { f, g, state });
}

fn minimal_push_bytes(val: I256) -> usize {
    let bytes = val.to_u256().to_big_endian();
    let is_neg = (bytes[0] & 0x80) != 0;
    let skip = if is_neg { 0xff } else { 0x00 };

    let mut idx = 0usize;
    while idx < bytes.len() && bytes[idx] == skip {
        idx += 1;
    }

    let mut len = bytes.len().saturating_sub(idx);

    // Negative numbers need a leading 1 bit for SIGNEXTEND.
    if is_neg && bytes.get(idx).map(|b| *b < 0x80).unwrap_or(true) {
        len += 1;
    }

    len.max(1)
}

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(super) fn replay_normalize_step(&mut self, step: Step, key_infos: &[KeyInfo]) -> bool {
        match step {
            Step::Pop => self.stack.pop(self.actions),
            Step::Swap(d) => self.stack.swap(d as usize, self.actions),
            Step::Dup(p) => self.stack.dup(p as usize, self.actions),
            Step::PushImm(kid) => {
                let KeyInfo::Imm {
                    rep_vid, rep_imm, ..
                } = key_infos[kid as usize]
                else {
                    return false;
                };
                self.stack.push_imm(rep_vid, rep_imm, self.actions);
            }
            Step::LoadVal(kid) => {
                let KeyInfo::Val { vid } = key_infos[kid as usize] else {
                    return false;
                };
                self.push_value_from_spill_slot_or_mark(vid, vid);
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cfg_scc::CfgSccAnalysis,
        domtree::DomTree,
        liveness::Liveness,
        stackalloc::stackify::{
            builder::StackifyReachability,
            planner::{MemPlan, Planner, test_utils::build_stackify_test_context},
            slots::{FreeSlotPools, SpillSlotPools},
            spill::SpillSet,
            sym_stack::SymStack,
        },
    };
    use cranelift_entity::SecondaryMap;
    use sonatina_ir::{I256, Immediate, Type, ValueId, cfg::ControlFlowGraph};
    use sonatina_parser::parse_module;

    fn consider_brute_succ(
        state: PackedState,
        g: Cost,
        best: &mut FxHashMap<PackedState, Cost>,
        open: &mut BinaryHeap<QueueEntry>,
    ) {
        let should_update = match best.get(&state) {
            None => true,
            Some(&prev) => g < prev,
        };
        if !should_update {
            return;
        }

        best.insert(state, g);
        open.push(QueueEntry { f: g, g, state });
    }

    fn brute_force_optimal_cost(
        start: PackedState,
        goal: PackedState,
        key_infos: &[KeyInfo],
        materializable_imm: &[u8],
        materializable_val: &[u8],
        cost: &impl CostModel,
        cfg: SearchCfg,
    ) -> Option<Cost> {
        let mut best: FxHashMap<PackedState, Cost> = FxHashMap::default();
        best.insert(start, Cost::default());

        let mut open: BinaryHeap<QueueEntry> = BinaryHeap::new();
        open.push(QueueEntry {
            f: Cost::default(),
            g: Cost::default(),
            state: start,
        });

        while let Some(entry) = open.pop() {
            let Some(&g) = best.get(&entry.state) else {
                continue;
            };
            if entry.g != g {
                continue;
            }

            if entry.state == goal {
                return Some(g);
            }

            let len = entry.state.len();

            if len != 0 {
                consider_brute_succ(
                    entry.state.pop(),
                    g.saturating_add(cost.cost_pop()),
                    &mut best,
                    &mut open,
                );
            }

            if len >= 2 {
                let max_depth = len.saturating_sub(1).min(cfg.swap_max.saturating_sub(1));
                for depth in 1..=max_depth {
                    consider_brute_succ(
                        entry.state.swap(depth),
                        g.saturating_add(cost.cost_swap(depth as u8)),
                        &mut best,
                        &mut open,
                    );
                }
            }

            if len != 0 && cfg.dup_max != 0 && len < cfg.max_len {
                let max_pos = len.saturating_sub(1).min(cfg.dup_max.saturating_sub(1));
                for pos in 0..=max_pos {
                    consider_brute_succ(
                        entry.state.dup(pos),
                        g.saturating_add(cost.cost_dup(pos as u8)),
                        &mut best,
                        &mut open,
                    );
                }
            }

            if len < cfg.max_len {
                for &kid in materializable_imm {
                    let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
                        panic!("expected imm key info");
                    };
                    consider_brute_succ(
                        entry.state.push(kid),
                        g.saturating_add(cost.cost_push_imm(canon)),
                        &mut best,
                        &mut open,
                    );
                }

                for &kid in materializable_val {
                    let KeyInfo::Val { vid } = key_infos[kid as usize] else {
                        panic!("expected val key info");
                    };
                    consider_brute_succ(
                        entry.state.push(kid),
                        g.saturating_add(cost.cost_load(vid)),
                        &mut best,
                        &mut open,
                    );
                }
            }
        }

        None
    }

    fn stack_matches_exact(stack: &SymStack, desired: &[ValueId]) -> bool {
        let limit = stack.len_above_func_ret();
        limit == desired.len()
            && stack
                .iter()
                .take(limit)
                .zip(desired.iter().copied())
                .all(|(item, v)| item == &StackItem::Value(v))
    }

    fn replay_plan(stack: &SymStack, plan: &NormalizePlan) -> SymStack {
        let mut replayed = stack.clone();
        let mut actions = crate::stackalloc::Actions::new();
        for &step in &plan.steps {
            match step {
                Step::Pop => replayed.pop(&mut actions),
                Step::Swap(d) => replayed.swap(d as usize, &mut actions),
                Step::Dup(p) => replayed.dup(p as usize, &mut actions),
                Step::PushImm(kid) => {
                    let KeyInfo::Imm {
                        rep_vid, rep_imm, ..
                    } = plan.key_infos[kid as usize]
                    else {
                        panic!("expected imm key info");
                    };
                    replayed.push_imm(rep_vid, rep_imm, &mut actions);
                }
                Step::LoadVal(kid) => {
                    let KeyInfo::Val { vid } = plan.key_infos[kid as usize] else {
                        panic!("expected val key info");
                    };
                    replayed.push_value(vid);
                }
            }
        }
        replayed
    }

    #[test]
    fn immediate_reuse_across_value_ids() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let v0 = func.dfg.make_imm_value(Immediate::I8(0));
            let v1 = func.dfg.make_imm_value(Immediate::I256(I256::zero()));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(v0);
            let desired = [v1];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 50_000,
            };

            let plan = solve_optimal_normalize_plan(&ctx, &stack, &desired, &cost, search_cfg)
                .expect("no plan");
            assert!(
                plan.steps.is_empty(),
                "expected 0-step plan, got {:?}",
                plan.steps
            );

            let mut replayed = stack.clone();
            for (depth, &want) in desired.iter().enumerate() {
                if ctx.func.dfg.value_is_imm(want) {
                    let want_imm = ctx.func.dfg.value_imm(want).unwrap().as_i256();
                    let StackItem::Value(cur) = *replayed.item_at(depth).unwrap() else {
                        panic!("expected value on stack");
                    };
                    let cur_imm = ctx.func.dfg.value_imm(cur).unwrap().as_i256();
                    assert_eq!(cur_imm, want_imm, "canonical immediate mismatch");
                    replayed.rename_value_at_depth(depth, want);
                }
            }

            assert!(stack_matches_exact(&replayed, &desired));
        });
    }

    #[test]
    fn repair_solver_can_dup_from_frozen_suffix_on_long_stacks() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            // Build a long stack with a large shared suffix and a small repair region:
            //   start:  [p0..p4, s0..s24]
            //   goal:   [s0, p0..p4, s0..s24]
            // where the shared suffix is [s0..s24] (25 items) and the repair region is <= SWAP17.
            let mut prefix: Vec<ValueId> = Vec::new();
            for _ in 0..5 {
                prefix.push(func.dfg.make_undef_value(sonatina_ir::Type::I256));
            }

            let mut suffix: Vec<ValueId> = Vec::new();
            for _ in 0..25 {
                suffix.push(func.dfg.make_undef_value(sonatina_ir::Type::I256));
            }

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            for &v in suffix.iter().rev() {
                stack.push_value(v);
            }
            for &v in prefix.iter().rev() {
                stack.push_value(v);
            }

            let mut desired: Vec<ValueId> = Vec::new();
            desired.push(suffix[0]);
            desired.extend(prefix.iter().copied());
            desired.extend(suffix.iter().copied());

            let base_len = suffix.len();
            assert_eq!(
                stack.len_above_func_ret(),
                prefix.len() + suffix.len(),
                "unexpected start stack len"
            );
            assert_eq!(
                desired.len(),
                prefix.len() + suffix.len() + 1,
                "unexpected desired stack len"
            );

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 50_000,
            };

            let plan = solve_optimal_repair_normalize_plan(
                &ctx,
                &stack,
                desired.as_slice(),
                base_len,
                &cost,
                search_cfg,
            )
            .expect("expected repair plan");

            assert!(
                plan.steps.iter().any(|s| matches!(s, Step::Dup(_))),
                "expected plan to use DUP from frozen suffix: {:?}",
                plan.steps
            );
            assert!(
                !plan.steps.iter().any(|s| matches!(s, Step::LoadVal(_))),
                "expected plan to avoid LOAD: {:?}",
                plan.steps
            );

            let replayed = replay_plan(&stack, &plan);

            assert!(stack_matches_exact(&replayed, desired.as_slice()));
        });
    }

    #[test]
    fn repair_greedy_builder_inserts_missing_keys_from_goal_suffix() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let top = func.dfg.make_imm_value(Immediate::I8(9));
            let bottom = func.dfg.make_imm_value(Immediate::I8(7));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let stack = SymStack::entry_stack(func, false);
            let desired = [top, bottom];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 0,
            };

            let plan = solve_optimal_repair_prefix_plan(
                &ctx,
                &stack,
                &desired,
                0,
                &cost,
                search_cfg,
            )
            .expect("expected greedy repair plan");

            assert!(
                matches!(
                    plan.steps.as_slice(),
                    [Step::PushImm(first), Step::PushImm(second)]
                        if *first == plan.goal_keys[1] && *second == plan.goal_keys[0]
                ),
                "expected back-to-front PUSH order with no cleanup swap: {:?}",
                plan.steps
            );
            let baseline = [
                Step::PushImm(plan.goal_keys[0]),
                Step::PushImm(plan.goal_keys[1]),
                Step::Swap(1),
            ];
            let plan_cost = cost_for_steps(&plan.steps, &plan.key_infos, &cost);
            let baseline_cost = cost_for_steps(&baseline, &plan.key_infos, &cost);
            assert!(
                plan_cost < baseline_cost,
                "expected goal-order insertions to beat top-first insertions: plan={plan_cost:?} baseline={baseline_cost:?}"
            );

            let replayed = replay_plan(&stack, &plan);
            assert!(stack_matches_exact(&replayed, &desired));
        });
    }

    #[test]
    fn repair_greedy_builder_keeps_costly_goal_key_accessible_while_trimming() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let a = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let b = func.dfg.make_undef_value(sonatina_ir::Type::I256);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(a);
            stack.push_value(b);
            stack.push_value(b);
            stack.push_value(a); // [a, b, b, a]

            let desired = [a];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: 2,
                swap_max: ctx.reach.swap_max,
                max_len: 4,
                max_expansions: 0,
            };

            let plan =
                solve_optimal_repair_prefix_plan(&ctx, &stack, &desired, 0, &cost, search_cfg)
                    .expect("expected greedy repair plan");

            assert!(
                matches!(plan.steps.first(), Some(Step::Swap(1)))
                    && matches!(plan.steps.get(1), Some(Step::Pop)),
                "expected trim to remove the cheap surplus before popping the goal key: {:?}",
                plan.steps
            );

            let replayed = replay_plan(&stack, &plan);
            assert!(stack_matches_exact(&replayed, &desired));
        });
    }

    #[test]
    fn repair_greedy_builder_can_dup_from_frozen_suffix_when_search_budget_is_zero() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let mut prefix: Vec<ValueId> = Vec::new();
            for _ in 0..5 {
                prefix.push(func.dfg.make_undef_value(sonatina_ir::Type::I256));
            }

            let mut suffix: Vec<ValueId> = Vec::new();
            for _ in 0..25 {
                suffix.push(func.dfg.make_undef_value(sonatina_ir::Type::I256));
            }

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            for &v in suffix.iter().rev() {
                stack.push_value(v);
            }
            for &v in prefix.iter().rev() {
                stack.push_value(v);
            }

            let mut desired: Vec<ValueId> = Vec::new();
            desired.push(suffix[0]);
            desired.extend(prefix.iter().copied());
            desired.extend(suffix.iter().copied());

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 0,
            };

            let plan = solve_optimal_repair_normalize_plan(
                &ctx,
                &stack,
                desired.as_slice(),
                suffix.len(),
                &cost,
                search_cfg,
            )
            .expect("expected greedy repair plan");

            assert!(
                plan.steps.iter().any(|step| matches!(step, Step::Dup(_))),
                "expected DUP from frozen suffix: {:?}",
                plan.steps
            );
            assert!(
                !plan
                    .steps
                    .iter()
                    .any(|step| matches!(step, Step::LoadVal(_))),
                "expected no LOAD in greedy repair plan: {:?}",
                plan.steps
            );

            let replayed = replay_plan(&stack, &plan);
            assert!(stack_matches_exact(&replayed, desired.as_slice()));
        });
    }

    #[test]
    fn repair_greedy_builder_uses_swap_dup_for_deep_repair_source() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let extra = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let mut mids: Vec<ValueId> = Vec::new();
            for _ in 0..15 {
                mids.push(func.dfg.make_undef_value(sonatina_ir::Type::I256));
            }
            let target = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let suffix = func.dfg.make_undef_value(sonatina_ir::Type::I256);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(suffix);
            stack.push_value(target);
            for &v in mids.iter().rev() {
                stack.push_value(v);
            }
            stack.push_value(extra);

            let mut desired_prefix = Vec::with_capacity(17);
            desired_prefix.push(target);
            desired_prefix.extend(mids.iter().copied());
            desired_prefix.push(target);

            let mut desired_full = desired_prefix.clone();
            desired_full.push(suffix);

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: 4,
                swap_max: 17,
                max_len: 17,
                max_expansions: 0,
            };

            let plan = solve_optimal_repair_prefix_plan(
                &ctx,
                &stack,
                desired_prefix.as_slice(),
                1,
                &cost,
                search_cfg,
            )
            .expect("expected greedy repair plan");

            assert!(
                plan.steps
                    .windows(2)
                    .any(|window| matches!(window, [Step::Swap(15), Step::Dup(0)])),
                "expected SWAP+DUP for deep repair source: {:?}",
                plan.steps
            );
            assert!(
                !plan
                    .steps
                    .iter()
                    .any(|step| matches!(step, Step::PushImm(_) | Step::LoadVal(_))),
                "expected no materialization: {:?}",
                plan.steps
            );

            let replayed = replay_plan(&stack, &plan);
            assert!(stack_matches_exact(&replayed, desired_full.as_slice()));
        });
    }

    #[test]
    fn repair_greedy_builder_materializes_only_true_deficits() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let extra = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let keep = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let reuse = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let suffix_tail = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let missing = func.dfg.make_imm_value(Immediate::I8(7));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(suffix_tail);
            stack.push_value(reuse);
            stack.push_value(keep);
            stack.push_value(extra);

            let desired_prefix = [missing, reuse, keep];
            let desired_full = [missing, reuse, keep, reuse, suffix_tail];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 0,
            };

            let plan = solve_optimal_repair_prefix_plan(
                &ctx,
                &stack,
                &desired_prefix,
                2,
                &cost,
                search_cfg,
            )
            .expect("expected greedy repair plan");

            let materialize_steps = plan
                .steps
                .iter()
                .filter(|step| matches!(step, Step::PushImm(_) | Step::LoadVal(_)))
                .count();
            assert_eq!(
                materialize_steps, 1,
                "unexpected materialization: {:?}",
                plan.steps
            );
            assert!(
                plan.steps.iter().any(|step| matches!(step, Step::Dup(_))),
                "expected suffix DUP: {:?}",
                plan.steps
            );
            assert!(
                !plan
                    .steps
                    .iter()
                    .any(|step| matches!(step, Step::LoadVal(_))),
                "expected PUSH-only materialization: {:?}",
                plan.steps
            );

            let replayed = replay_plan(&stack, &plan);
            assert!(stack_matches_exact(&replayed, &desired_full));
        });
    }

    #[test]
    fn repair_greedy_builder_preserves_frozen_suffix() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let extra = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let keep = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let suffix0 = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let suffix1 = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let suffix2 = func.dfg.make_undef_value(sonatina_ir::Type::I256);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(suffix2);
            stack.push_value(suffix1);
            stack.push_value(suffix0);
            stack.push_value(keep);
            stack.push_value(extra);

            let desired_prefix = [suffix1, keep];
            let desired_full = [suffix1, keep, suffix0, suffix1, suffix2];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 0,
            };

            let plan = solve_optimal_repair_prefix_plan(
                &ctx,
                &stack,
                &desired_prefix,
                3,
                &cost,
                search_cfg,
            )
            .expect("expected greedy repair plan");

            let replayed = replay_plan(&stack, &plan);
            assert!(stack_matches_exact(&replayed, &desired_full));
            for (depth, want) in [suffix0, suffix1, suffix2].into_iter().enumerate() {
                assert_eq!(
                    replayed.item_at(desired_prefix.len() + depth),
                    Some(&StackItem::Value(want)),
                    "frozen suffix changed at depth {}",
                    desired_prefix.len() + depth
                );
            }
        });
    }

    #[test]
    fn solver_returns_push_plan_even_when_equal_to_flush_upper_bound() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm1 = func.dfg.make_imm_value(Immediate::I8(1));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let stack = SymStack::entry_stack(func, false);
            let desired = [imm1];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 50_000,
            };

            let plan = solve_optimal_normalize_plan(&ctx, &stack, &desired, &cost, search_cfg)
                .expect("expected push plan");
            assert!(
                plan.steps.iter().any(|s| matches!(s, Step::PushImm(_))),
                "expected plan to materialize imm: {:?}",
                plan.steps
            );
        });
    }

    #[test]
    fn solver_returns_push0_plan_when_optimal_equals_flush_upper_bound() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let v0 = func.dfg.make_imm_value(Immediate::I8(0));
            let v1 = func.dfg.make_imm_value(Immediate::I256(I256::zero()));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(v0);

            let desired = [v1, v0];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 50_000,
            };

            let plan = solve_optimal_normalize_plan(&ctx, &stack, &desired, &cost, search_cfg)
                .expect("expected push0 plan");
            assert!(
                plan.steps.iter().any(|s| matches!(s, Step::PushImm(_))),
                "expected plan to use PUSH0: {:?}",
                plan.steps
            );

            // Replay the plan and apply the immediate renaming contract to validate exactness.
            let mut replayed = stack.clone();
            let mut actions = crate::stackalloc::Actions::new();
            for &step in &plan.steps {
                match step {
                    Step::Pop => replayed.pop(&mut actions),
                    Step::Swap(d) => replayed.swap(d as usize, &mut actions),
                    Step::Dup(p) => replayed.dup(p as usize, &mut actions),
                    Step::PushImm(kid) => {
                        let KeyInfo::Imm {
                            rep_vid, rep_imm, ..
                        } = plan.key_infos[kid as usize]
                        else {
                            panic!("expected imm key info");
                        };
                        replayed.push_imm(rep_vid, rep_imm, &mut actions);
                    }
                    Step::LoadVal(_) => panic!("unexpected load"),
                }
            }

            for (depth, &want) in desired.iter().enumerate() {
                if ctx.func.dfg.value_is_imm(want) {
                    let want_imm = ctx.func.dfg.value_imm(want).unwrap().as_i256();
                    let StackItem::Value(cur) = *replayed.item_at(depth).unwrap() else {
                        panic!("expected value on stack");
                    };
                    let cur_imm = ctx.func.dfg.value_imm(cur).unwrap().as_i256();
                    assert_eq!(cur_imm, want_imm, "canonical immediate mismatch");
                    replayed.rename_value_at_depth(depth, want);
                }
            }

            assert!(stack_matches_exact(&replayed, &desired));
        });
    }

    #[test]
    fn dup_pop_preferred_over_load_when_expensive() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let x = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let y = func.dfg.make_undef_value(sonatina_ir::Type::I256);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(
                func,
                &cfg,
                &dom,
                &liveness,
                entry,
                scc,
                reach,
            );

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(y);
            stack.push_value(x); // [x, y]

            let desired = [x, x];

            let cost = EstimatedCostModel {
                load_cost: Cost {
                    gas: 1_000,
                    bytes: 1_000,
                },
            };
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 50_000,
            };

            let plan = solve_optimal_normalize_plan(&ctx, &stack, &desired, &cost, search_cfg)
                .expect("no plan");
            assert!(
                plan.steps.iter().any(|s| matches!(s, Step::Dup(_))),
                "expected plan to use DUP: {:?}",
                plan.steps
            );
            assert!(
                plan.steps.iter().any(|s| matches!(s, Step::Pop)),
                "expected plan to use POP: {:?}",
                plan.steps
            );
            assert!(
                !plan.steps.iter().any(|s| matches!(s, Step::LoadVal(_))),
                "expected plan to avoid LOAD: {:?}",
                plan.steps
            );

            let load_plan_cost = cost
                .cost_load(x)
                .saturating_add(cost.cost_swap(2))
                .saturating_add(cost.cost_pop());
            let plan_cost = plan.steps.iter().fold(Cost::default(), |acc, step| {
                let c = match *step {
                    Step::Pop => cost.cost_pop(),
                    Step::Dup(pos) => cost.cost_dup(pos),
                    Step::Swap(depth) => cost.cost_swap(depth),
                    Step::PushImm(kid) => {
                        let KeyInfo::Imm { canon, .. } = plan.key_infos[kid as usize] else {
                            panic!("expected imm key info");
                        };
                        cost.cost_push_imm(canon)
                    }
                    Step::LoadVal(kid) => {
                        let KeyInfo::Val { vid } = plan.key_infos[kid as usize] else {
                            panic!("expected val key info");
                        };
                        cost.cost_load(vid)
                    }
                };
                acc.saturating_add(c)
            });

            assert!(
                plan_cost < load_plan_cost,
                "expected dup/pop plan to beat load plan: plan={plan_cost:?} load={load_plan_cost:?}"
            );

            let mut replayed = stack.clone();
            let mut actions = crate::stackalloc::Actions::new();
            for &step in &plan.steps {
                match step {
                    Step::Pop => replayed.pop(&mut actions),
                    Step::Swap(d) => replayed.swap(d as usize, &mut actions),
                    Step::Dup(p) => replayed.dup(p as usize, &mut actions),
                    Step::PushImm(_) | Step::LoadVal(_) => {
                        panic!("unexpected materialization step: {step:?}");
                    }
                }
            }

            assert!(stack_matches_exact(&replayed, &desired));
        });
    }

    #[test]
    fn permutation_only_sanity() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let a = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let b = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let c = func.dfg.make_undef_value(sonatina_ir::Type::I256);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(c);
            stack.push_value(b);
            stack.push_value(a); // [a, b, c]

            let desired = [b, a, c];

            let cost = EstimatedCostModel::default();
            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: ctx.reach.swap_max,
                max_expansions: 50_000,
            };

            let plan = solve_optimal_normalize_plan(&ctx, &stack, &desired, &cost, search_cfg)
                .expect("no plan");
            assert!(
                !plan.steps.iter().any(|s| matches!(s, Step::LoadVal(_))),
                "expected no loads for permutation: {:?}",
                plan.steps
            );

            let mut replayed = stack.clone();
            let mut actions = crate::stackalloc::Actions::new();
            for &step in &plan.steps {
                match step {
                    Step::Pop => replayed.pop(&mut actions),
                    Step::Swap(d) => replayed.swap(d as usize, &mut actions),
                    Step::Dup(p) => replayed.dup(p as usize, &mut actions),
                    Step::PushImm(_) | Step::LoadVal(_) => {
                        panic!("unexpected materialization step: {step:?}");
                    }
                }
            }

            assert!(stack_matches_exact(&replayed, &desired));
        });
    }

    #[test]
    fn regression_harness_random_small_stacks() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
    block0:
        return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm0_a = func.dfg.make_imm_value(Immediate::I8(0));
            let imm0_b = func.dfg.make_imm_value(Immediate::I256(I256::zero()));
            let imm1 = func.dfg.make_imm_value(Immediate::I8(1));
            let imm_neg1 = func.dfg.make_imm_value(Immediate::I8(-1));

            let a = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let b = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let c = func.dfg.make_undef_value(sonatina_ir::Type::I256);
            let d = func.dfg.make_undef_value(sonatina_ir::Type::I256);

            let pool: [ValueId; 8] = [imm0_a, imm0_b, imm1, imm_neg1, a, b, c, d];

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(
                func,
                &cfg,
                &dom,
                &liveness,
                entry,
                scc,
                reach,
            );

            struct Rng(u64);
            impl Rng {
                fn next_u32(&mut self) -> u32 {
                    let mut x = self.0;
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    self.0 = x;
                    (x >> 32) as u32
                }
                fn gen_range(&mut self, n: usize) -> usize {
                    (self.next_u32() as usize) % n
                }
            }

            let mut rng = Rng(0x9e3779b97f4a7c15);

            // Keep brute-force feasible: small reach + small max_len.
            let search_cfg = SearchCfg {
                dup_max: 6,
                swap_max: 7,
                max_len: 6,
                max_expansions: 1_000_000,
            };
            let cost = EstimatedCostModel::default();

            for _ in 0..100 {
                let start_len = rng.gen_range(search_cfg.max_len + 1);
                let desired_len = rng.gen_range(search_cfg.max_len + 1);

                let mut start_vals: Vec<ValueId> = Vec::with_capacity(start_len);
                for _ in 0..start_len {
                    start_vals.push(pool[rng.gen_range(pool.len())]);
                }

                let mut desired: Vec<ValueId> = Vec::with_capacity(desired_len);
                for _ in 0..desired_len {
                    desired.push(pool[rng.gen_range(pool.len())]);
                }

                let mut stack = SymStack::entry_stack(ctx.func, false);
                for &v in start_vals.iter().rev() {
                    stack.push_value(v);
                }

                let flush_cost = estimate_flush_rebuild_cost(&ctx, &stack, &desired, &cost);
                let plan = solve_optimal_normalize_plan(&ctx, &stack, &desired, &cost, search_cfg);
                let solver_cost = plan
                    .as_ref()
                    .map(|p| cost_for_steps(&p.steps, &p.key_infos, &cost))
                    .unwrap_or(flush_cost);

                let mut key_ids: FxHashMap<Key, u8> = FxHashMap::default();
                let mut key_infos: Vec<KeyInfo> = Vec::new();

                let mut goal_keys: Vec<u8> = Vec::with_capacity(desired.len());
                let mut materializable_imm: Vec<u8> = Vec::new();
                let mut materializable_val: Vec<u8> = Vec::new();
                let mut seen_push: u64 = 0;
                let mut seen_load: u64 = 0;

                for &v in &desired {
                    let key = canonical_key(&ctx, v);
                    let kid = intern_key(&ctx, key, v, &mut key_ids, &mut key_infos)
                        .expect("intern_key failed");
                    goal_keys.push(kid);

                    if ctx.func.dfg.value_is_imm(v) {
                        if (seen_push & (1u64 << kid)) == 0 {
                            seen_push |= 1u64 << kid;
                            materializable_imm.push(kid);
                        }
                    } else if (seen_load & (1u64 << kid)) == 0 {
                        seen_load |= 1u64 << kid;
                        materializable_val.push(kid);
                    }
                }

                let mut start_keys: Vec<u8> = Vec::with_capacity(stack.len_above_func_ret());
                for depth in 0..stack.len_above_func_ret() {
                    let Some(StackItem::Value(v)) = stack.item_at(depth) else {
                        panic!("unexpected non-value in start stack");
                    };
                    let key = canonical_key(&ctx, *v);
                    let kid = intern_key(&ctx, key, *v, &mut key_ids, &mut key_infos)
                        .expect("intern_key failed");
                    start_keys.push(kid);
                }

                let start = PackedState::from_ids(&start_keys).expect("invalid start pack");
                let goal = PackedState::from_ids(&goal_keys).expect("invalid goal pack");
                let brute_cost = brute_force_optimal_cost(
                    start,
                    goal,
                    &key_infos,
                    &materializable_imm,
                    &materializable_val,
                    &cost,
                    search_cfg,
                )
                .expect("brute-force search failed");

                assert!(
                    solver_cost <= flush_cost,
                    "solver must beat flush: solver={solver_cost:?} flush={flush_cost:?} start={start_vals:?} desired={desired:?}"
                );
                assert_eq!(
                    solver_cost,
                    brute_cost,
                    "solver not optimal: solver={solver_cost:?} brute={brute_cost:?} start={start_vals:?} desired={desired:?}"
                );
            }
        });
    }

    #[test]
    fn operand_prep_greedy_upper_bound_beats_baseline_on_high_arity_last_use_shuffle() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let values: Vec<ValueId> = (0..9)
                .map(|_| func.dfg.make_undef_value(Type::I256))
                .collect();
            let args: Vec<ValueId> = values[..8].to_vec();
            let start_vals = [
                args[6], args[5], args[4], args[3], values[8], args[1], args[0], args[7],
            ];

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(4);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let mut stack = SymStack::entry_stack(func, false);
            for &v in start_vals.iter().rev() {
                stack.push_value(v);
            }

            let mut consume_last_use = BitSet::default();
            for &arg in &args {
                consume_last_use.insert(arg);
            }

            let search_cfg = SearchCfg {
                dup_max: ctx.reach.dup_max,
                swap_max: ctx.reach.swap_max,
                max_len: args.len(),
                max_expansions: 0,
            };
            let cost = EstimatedCostModel::default();
            let problem =
                build_operand_prep_problem(&ctx, &stack, &args, &consume_last_use, search_cfg)
                    .expect("expected operand-prep problem");
            let (baseline_steps, baseline_cost) =
                build_operand_prep_baseline_upper_bound(&ctx, &args, &problem, &cost, search_cfg)
                    .expect("expected baseline incumbent");
            let (greedy_steps, greedy_cost) =
                build_greedy_operand_prep_upper_bound(&problem, &cost, search_cfg, baseline_cost)
                    .expect("expected greedy incumbent");
            assert!(
                greedy_cost < baseline_cost,
                "expected greedy incumbent to beat baseline: greedy={greedy_cost:?} baseline={baseline_cost:?} greedy_steps={greedy_steps:?} baseline_steps={baseline_steps:?}"
            );

            let plan = solve_optimal_operand_prep_plan(
                &ctx,
                &stack,
                &args,
                &consume_last_use,
                &cost,
                search_cfg,
            )
            .expect("expected operand-prep plan");
            assert_eq!(
                plan.cost, greedy_cost,
                "zero-budget exact search should return the best incumbent"
            );
        });
    }

    #[test]
    fn operand_prep_replay_failure_rolls_back_state() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm1 = func.dfg.make_imm_value(Immediate::I8(1));
            let imm2 = func.dfg.make_imm_value(Immediate::I8(2));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut free_slots,
                &mut slots,
            );

            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut planner = Planner::new(&ctx, &mut stack, &mut actions, mem);

            let plan = NormalizePlan {
                cost: Cost::default(),
                steps: vec![Step::PushImm(0)],
                key_infos: vec![KeyInfo::Imm {
                    canon: I256::from(1),
                    rep_vid: imm1,
                    rep_imm: Immediate::I8(1),
                }],
                goal_keys: vec![0],
            };

            assert!(
                !planner.apply_operand_prep_plan(&plan, &[imm2]),
                "plan should fail because replayed immediate does not match the desired one"
            );
            assert_eq!(planner.stack.len_above_func_ret(), 0);
            assert!(planner.actions.is_empty());
            assert!(spill_set.is_empty());
            assert!(spill_requests.is_empty());
        });
    }

    #[test]
    fn normalize_replay_failure_rolls_back_state() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;
        let parsed = parse_module(SRC).unwrap();
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm1 = func.dfg.make_imm_value(Immediate::I8(1));
            let imm2 = func.dfg.make_imm_value(Immediate::I8(2));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut free_slots,
                &mut slots,
            );

            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut planner = Planner::new(&ctx, &mut stack, &mut actions, mem);

            let plan = NormalizePlan {
                cost: Cost::default(),
                steps: vec![Step::PushImm(0)],
                key_infos: vec![KeyInfo::Imm {
                    canon: I256::from(1),
                    rep_vid: imm1,
                    rep_imm: Immediate::I8(1),
                }],
                goal_keys: vec![0],
            };

            assert!(
                !planner.apply_normalize_plan(&plan, &[imm2]),
                "plan should fail because replayed immediate does not match the desired one"
            );
            assert_eq!(planner.stack.len_above_func_ret(), 0);
            assert!(planner.actions.is_empty());
            assert!(spill_set.is_empty());
            assert!(spill_requests.is_empty());
        });
    }
}
