use rustc_hash::FxHashMap;
use sonatina_ir::{I256, Immediate, ValueId};
use std::{cmp::Ordering, collections::BinaryHeap, sync::OnceLock};

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

    pub(super) fn saturating_mul(self, n: usize) -> Self {
        let mut out = Self::default();
        for _ in 0..n {
            out = out.saturating_add(self);
        }
        out
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
    if start == goal {
        return Some(NormalizePlan {
            steps: Vec::new(),
            key_infos,
            goal_keys,
        });
    }

    let pop_cost = cost.cost_pop();
    let min_dup_cost = minimal_dup_cost(cost, cfg.dup_max);
    let min_swap_cost = minimal_swap_cost(cost, cfg.swap_max);
    let goal_counts = compute_goal_counts(&goal_keys);

    let mut upper_bound = estimate_flush_rebuild_cost(ctx, stack, desired, cost);
    let mut incumbent_steps: Option<Vec<Step>> = None;

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

    let start_h = heuristic(
        start,
        goal,
        &goal_counts,
        min_dup_cost,
        min_swap_cost,
        pop_cost,
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

        if entry.f >= upper_bound {
            break;
        }

        // If we already have a feasible incumbent (greedy) plan, don't let the exact search blow
        // up compile time or memory trying to prove optimality.
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
            return incumbent_steps.map(|steps| NormalizePlan {
                steps,
                key_infos,
                goal_keys,
            });
        }

        if entry.state == goal {
            let steps = reconstruct_steps(start, goal, &parent)?;
            return Some(NormalizePlan {
                steps,
                key_infos,
                goal_keys,
            });
        }

        let h = heuristic(
            entry.state,
            goal,
            &goal_counts,
            min_dup_cost,
            min_swap_cost,
            pop_cost,
            &key_infos,
            cost,
        );
        if g.saturating_add(h) >= upper_bound {
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
            return incumbent_steps.map(|steps| NormalizePlan {
                steps,
                key_infos,
                goal_keys,
            });
        }

        let cur_len = entry.state.len();
        let mut cur_counts = [0u8; 64];
        for i in 0..cur_len {
            let kid = entry.state.get(i) as usize;
            cur_counts[kid] = cur_counts[kid].saturating_add(1);
        }

        // POP
        if cur_len != 0 {
            consider_succ(
                entry.state.pop(),
                g.saturating_add(cost.cost_pop()),
                entry.state,
                Step::Pop,
                goal,
                pop_cost,
                &goal_counts,
                min_dup_cost,
                min_swap_cost,
                &key_infos,
                cost,
                upper_bound,
                &mut best,
                &mut parent,
                &mut open,
            );
        }

        // SWAP
        if cur_len >= 2 {
            let max_depth = cur_len
                .saturating_sub(1)
                .min(cfg.swap_max.saturating_sub(1));
            for depth in 1..=max_depth {
                consider_succ(
                    entry.state.swap(depth),
                    g.saturating_add(cost.cost_swap(depth as u8)),
                    entry.state,
                    Step::Swap(depth as u8),
                    goal,
                    pop_cost,
                    &goal_counts,
                    min_dup_cost,
                    min_swap_cost,
                    &key_infos,
                    cost,
                    upper_bound,
                    &mut best,
                    &mut parent,
                    &mut open,
                );
            }
        }

        // DUP
        if cur_len != 0 && cfg.dup_max != 0 && cur_len < cfg.max_len {
            let max_pos = cur_len.saturating_sub(1).min(cfg.dup_max.saturating_sub(1));
            for pos in 0..=max_pos {
                consider_succ(
                    entry.state.dup(pos),
                    g.saturating_add(cost.cost_dup(pos as u8)),
                    entry.state,
                    Step::Dup(pos as u8),
                    goal,
                    pop_cost,
                    &goal_counts,
                    min_dup_cost,
                    min_swap_cost,
                    &key_infos,
                    cost,
                    upper_bound,
                    &mut best,
                    &mut parent,
                    &mut open,
                );
            }
        }

        if cur_len < cfg.max_len {
            for &kid in &materializable_imm {
                let KeyInfo::Imm { canon, .. } = key_infos[kid as usize] else {
                    unreachable!("expected imm key info")
                };
                consider_succ(
                    entry.state.push(kid),
                    g.saturating_add(cost.cost_push_imm(canon)),
                    entry.state,
                    Step::PushImm(kid),
                    goal,
                    pop_cost,
                    &goal_counts,
                    min_dup_cost,
                    min_swap_cost,
                    &key_infos,
                    cost,
                    upper_bound,
                    &mut best,
                    &mut parent,
                    &mut open,
                );
            }

            for &kid in &materializable_val {
                // Loading an already-present value is always dominated by DUP (and would also
                // request a new spill slot if it wasn't already spilled). Only load values that
                // are still missing from the current multiset.
                if cur_counts[kid as usize] != 0 {
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
                    goal,
                    pop_cost,
                    &goal_counts,
                    min_dup_cost,
                    min_swap_cost,
                    &key_infos,
                    cost,
                    upper_bound,
                    &mut best,
                    &mut parent,
                    &mut open,
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

    incumbent_steps.map(|steps| NormalizePlan {
        steps,
        key_infos,
        goal_keys,
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
        let Some(&(prev, step)) = parent.get(&cur) else {
            return None;
        };
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

fn minimal_dup_cost(cost: &impl CostModel, dup_max: usize) -> Cost {
    if dup_max == 0 {
        return Cost::default();
    }

    let mut best = cost.cost_dup(0);
    for pos in 1..dup_max {
        best = best.min(cost.cost_dup(pos as u8));
    }
    best
}

fn minimal_swap_cost(cost: &impl CostModel, swap_max: usize) -> Cost {
    if swap_max <= 1 {
        return Cost::default();
    }

    let mut best = cost.cost_swap(1);
    for depth in 2..swap_max {
        best = best.min(cost.cost_swap(depth as u8));
    }
    best
}

fn cost_for_steps(steps: &[Step], key_infos: &[KeyInfo], cost: &impl CostModel) -> Cost {
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

    // 1) Remove any keys that appear too many times (or are not needed at all).
    loop {
        let mut extra_kid: Option<u8> = None;
        for (kid, &have) in cur_counts.iter().enumerate() {
            if have > goal_counts[kid] {
                extra_kid = Some(kid as u8);
                break;
            }
        }
        let Some(kid) = extra_kid else {
            break;
        };

        let pos = cur
            .iter()
            .position(|&x| x == kid)
            .expect("extra key missing from vector");
        if pos != 0 {
            if pos >= cfg.swap_max {
                return None;
            }
            steps.push(Step::Swap(pos as u8));
            apply_step_to_vec(&mut cur, Step::Swap(pos as u8));
        }
        steps.push(Step::Pop);
        apply_step_to_vec(&mut cur, Step::Pop);
        cur_counts[kid as usize] = cur_counts[kid as usize].saturating_sub(1);
    }

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

    if cur.len() != goal_keys.len() || cur_counts != *goal_counts {
        return None;
    }

    // 3) Solve the remaining permutation using minimal star transpositions.
    let swap_steps = build_star_swap_plan(&mut cur, goal_keys, cfg.swap_max)?;
    steps.extend(swap_steps);
    debug_assert_eq!(cur.as_slice(), goal_keys);
    Some(steps)
}

fn materialize_cost(kid: u8, key_infos: &[KeyInfo], cost: &impl CostModel) -> Cost {
    match key_infos[kid as usize] {
        KeyInfo::Imm { canon, .. } => cost.cost_push_imm(canon),
        KeyInfo::Val { vid } => cost.cost_load(vid),
    }
}

fn heuristic(
    state: PackedState,
    goal: PackedState,
    goal_counts: &[u8; 64],
    min_dup_cost: Cost,
    min_swap_cost: Cost,
    pop_cost: Cost,
    key_infos: &[KeyInfo],
    cost: &impl CostModel,
) -> Cost {
    let mut cur_counts = [0u8; 64];
    for i in 0..state.len() {
        let kid = state.get(i) as usize;
        cur_counts[kid] = cur_counts[kid].saturating_add(1);
    }

    // Lower bound: number of required POPs (for excess keys) + cost to create missing keys.
    //
    // This ignores swap/dup reachability constraints (so it stays admissible).
    let mut total = Cost::default();
    for (kid, &want) in goal_counts.iter().enumerate() {
        let have = cur_counts[kid];

        if have > want {
            total = total.saturating_add(pop_cost.saturating_mul((have - want) as usize));
            continue;
        }
        if have == want {
            continue;
        }

        // Missing copies of this key must be created via DUP/PUSH/LOAD.
        let missing = (want - have) as usize;
        let materialize = materialize_cost(kid as u8, key_infos, cost);
        let per_copy = if min_dup_cost == Cost::default() {
            materialize
        } else {
            materialize.min(min_dup_cost)
        };

        if have == 0 {
            total = total.saturating_add(materialize);
            if missing > 1 {
                total = total.saturating_add(per_copy.saturating_mul(missing - 1));
            }
        } else {
            total = total.saturating_add(per_copy.saturating_mul(missing));
        }
    }

    let perm = if state.len == goal.len {
        let len = state.len();
        let mut mismatched_non_top = 0usize;
        for i in 1..len {
            if state.get(i) != goal.get(i) {
                mismatched_non_top += 1;
            }
        }
        min_swap_cost.saturating_mul(mismatched_non_top)
    } else {
        Cost::default()
    };

    total.max(perm)
}

fn consider_succ(
    state: PackedState,
    g: Cost,
    parent_state: PackedState,
    step: Step,
    goal: PackedState,
    pop_cost: Cost,
    goal_counts: &[u8; 64],
    min_dup_cost: Cost,
    min_swap_cost: Cost,
    key_infos: &[KeyInfo],
    cost: &impl CostModel,
    upper_bound: Cost,
    best: &mut FxHashMap<PackedState, Cost>,
    parent: &mut FxHashMap<PackedState, (PackedState, Step)>,
    open: &mut BinaryHeap<QueueEntry>,
) {
    let h = heuristic(
        state,
        goal,
        goal_counts,
        min_dup_cost,
        min_swap_cost,
        pop_cost,
        key_infos,
        cost,
    );
    let f = g.saturating_add(h);
    if f >= upper_bound {
        return;
    }

    let should_update = match best.get(&state) {
        None => true,
        Some(&prev) => g < prev,
    };
    if !should_update {
        return;
    }

    best.insert(state, g);
    parent.insert(state, (parent_state, step));
    open.push(QueueEntry { f, g, state });
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
            templates::{
                compute_def_info, compute_dom_depth, compute_phi_out_sources, compute_phi_results,
                function_has_internal_return,
            },
        },
    };
    use sonatina_ir::cfg::ControlFlowGraph;
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
            let ctx = StackifyContext {
                func,
                cfg: &cfg,
                dom: &dom,
                liveness: &liveness,
                scratch_live_values: Default::default(),
                scratch_spill_slots: 0,
                entry,
                scc,
                dom_depth: compute_dom_depth(&dom, entry),
                def_info: compute_def_info(func, entry),
                phi_results: compute_phi_results(func),
                phi_out_sources: compute_phi_out_sources(func, &cfg),
                has_internal_return: function_has_internal_return(func),
                reach,
            };

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
            for depth in 0..desired.len() {
                let want = desired[depth];
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
            let ctx = StackifyContext {
                func,
                cfg: &cfg,
                dom: &dom,
                liveness: &liveness,
                scratch_live_values: Default::default(),
                scratch_spill_slots: 0,
                entry,
                scc,
                dom_depth: compute_dom_depth(&dom, entry),
                def_info: compute_def_info(func, entry),
                phi_results: compute_phi_results(func),
                phi_out_sources: compute_phi_out_sources(func, &cfg),
                has_internal_return: function_has_internal_return(func),
                reach,
            };

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
            let ctx = StackifyContext {
                func,
                cfg: &cfg,
                dom: &dom,
                liveness: &liveness,
                scratch_live_values: Default::default(),
                scratch_spill_slots: 0,
                entry,
                scc,
                dom_depth: compute_dom_depth(&dom, entry),
                def_info: compute_def_info(func, entry),
                phi_results: compute_phi_results(func),
                phi_out_sources: compute_phi_out_sources(func, &cfg),
                has_internal_return: function_has_internal_return(func),
                reach,
            };

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
            let ctx = StackifyContext {
                func,
                cfg: &cfg,
                dom: &dom,
                liveness: &liveness,
                scratch_live_values: Default::default(),
                scratch_spill_slots: 0,
                entry,
                scc,
                dom_depth: compute_dom_depth(&dom, entry),
                def_info: compute_def_info(func, entry),
                phi_results: compute_phi_results(func),
                phi_out_sources: compute_phi_out_sources(func, &cfg),
                has_internal_return: function_has_internal_return(func),
                reach,
            };

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
}
