use cranelift_entity::{EntityRef, SecondaryMap};
use rustc_hash::{FxHashMap, FxHashSet};
#[cfg(debug_assertions)]
use sonatina_ir::Module;
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::{inst_set::EvmInstKind, machine_inst_set::EvmMachineInstKind},
    isa::{
        Isa,
        evm::{Evm, EvmMachine},
    },
    module::FuncRef,
};

use crate::{
    bitset::BitSet,
    module_analysis::CallGraphSchedule,
    stackalloc::{Action, Allocator, StackifyAlloc},
};

use crate::isa::evm::memory_plan::align_up_to_word;

#[cfg(debug_assertions)]
use super::{
    super::{
        EvmBackend,
        memory_plan::{BackendSpillPlan, FuncPreAnalysis},
        ptr_escape::PtrEscapeSummary,
    },
    placement::{MemoryPlacementSection, compute_semantic_memory_placement},
};
use super::{
    super::{
        MachineFuncPlan, ObjLoc,
        emit::FinalAlloc,
        memory_plan::{
            self, BackendSpillReserve, FinalScratchReserveRange, MachineStackifyAnalysis,
            StableMode, WORD_BYTES,
        },
        prepare::{
            ArenaBaseFacts, SectionMemoryLayout, choose_arena_base, dynamic_terminal_payload,
        },
        static_arena_alloc::StackObjId,
    },
    module::FuncMachineMap,
    placement::EvmMemoryPlacementPlan,
};

/// Bound absolute spill accesses on every path beginning at each allocation's
/// source block. Including the whole block is conservative for accesses before
/// the allocation, and the backward fixed point also covers later loop trips.
/// Callee clobbers and semantic objects are handled by the existing heap plan.
pub(crate) fn compute_malloc_spill_bounds(
    source: &Function,
    machine: &Function,
    map: &FuncMachineMap,
    alloc: &FinalAlloc,
    isa: &Evm,
) -> FxHashMap<InstId, u32> {
    if alloc.mem_plan.uses_dynamic_frame() {
        return FxHashMap::default();
    }
    let mallocs: Vec<_> = source
        .layout
        .iter_block()
        .flat_map(|block| {
            source.layout.iter_inst(block).filter_map(move |inst| {
                matches!(
                    isa.inst_set().resolve_inst(source.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                )
                .then_some((inst, block))
            })
        })
        .collect();
    if mallocs.is_empty() {
        return FxHashMap::default();
    }
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(machine);
    let machine_isa = EvmMachine::new(machine.dfg.ctx.triple);
    let mut bounds: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let action_bound = |action: &Action| match *action {
        Action::MemLoadAbs(addr) | Action::MemStoreAbs(addr) => addr
            .checked_add(WORD_BYTES)
            .expect("spill access end overflow")
            .saturating_sub(alloc.mem_plan.arena_base)
            .div_ceil(WORD_BYTES),
        _ => 0,
    };
    for block in machine.layout.iter_block() {
        let bound = &mut bounds[block];
        if machine.layout.entry_block() == Some(block) {
            *bound = alloc
                .enter_function(machine)
                .iter()
                .map(action_bound)
                .max()
                .unwrap_or(0);
        }
        for inst in machine.layout.iter_inst(block) {
            for action in alloc.pre_inst(inst).iter().chain(alloc.post_inst(inst)) {
                *bound = (*bound).max(action_bound(action));
            }
            if let EvmMachineInstKind::BrTable(branch) =
                machine_isa.inst_set().resolve_inst(machine.dfg.inst(inst))
            {
                for (index, _) in branch.table().iter().enumerate() {
                    for action in alloc.br_table_case(inst, index) {
                        *bound = (*bound).max(action_bound(action));
                    }
                }
            }
        }
    }
    let full_bound = bounds.values().copied().max().unwrap_or(0);
    let blocks: Vec<_> = cfg.post_order().collect();
    loop {
        let mut changed = false;
        for &block in &blocks {
            let next = cfg
                .succs_of(block)
                .map(|next| bounds[*next])
                .max()
                .unwrap_or(0);
            if next > bounds[block] {
                bounds[block] = next;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    mallocs
        .into_iter()
        .map(|(inst, block)| {
            // CFG cleanup can remove a mapped block. Without a surviving boundary
            // retain all function spill accesses, without adding dead semantic objects.
            let bound = map.blocks[block]
                .filter(|&block| machine.layout.is_block_inserted(block))
                .map_or(full_bound, |block| bounds[block]);
            (inst, bound)
        })
        .collect()
}

pub(crate) struct FinalSpillAllocation {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) mem_plan: MachineFuncPlan,
    pub(crate) required_reserve: BackendSpillReserve,
    pub(crate) stack_obj_remap: FxHashMap<StackObjId, StackObjId>,
    pub(crate) used_fallback: bool,
}

pub(crate) struct FinalSpillAllocationInput {
    pub(crate) func: FuncRef,
    pub(crate) alloc: StackifyAlloc,
    pub(crate) mem_plan: MachineFuncPlan,
    pub(crate) final_scratch_reserve: FinalScratchReserveRange,
    pub(crate) reserve: BackendSpillReserve,
    pub(crate) fixed_writes: Vec<FixedMemoryWriteRange>,
    pub(crate) spills: FinalSpillObjects,
    pub(crate) optional_placement: OptionalFinalSpillPlacement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedMemoryWriteRange {
    pub(crate) inst: InstId,
    pub(crate) start_byte: u32,
    pub(crate) end_byte: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OptionalFinalSpillPlacement {
    Scratch,
    Stable,
}

#[derive(Default)]
pub(crate) struct FinalSpillObjects {
    spilled_values: Vec<(ValueId, StackObjId)>,
    /// Final spill words, each as a representative stackify object and whether
    /// the word must be stable. Every object is its own word until
    /// [`Self::share_disjoint_objects`] merges objects into shared words.
    objs: Vec<(StackObjId, bool)>,
    /// Stackify objects that share a representative's word.
    shared: FxHashMap<StackObjId, StackObjId>,
}

impl FinalSpillObjects {
    pub(crate) fn compute(alloc: &StackifyAlloc, stable_spill_values: &BitSet<ValueId>) -> Self {
        let mut spilled_values = final_spilled_values(alloc);
        spilled_values.sort_unstable_by_key(|(value, _)| value.as_u32());
        let mut old_obj_stable: FxHashMap<StackObjId, bool> = FxHashMap::default();
        let mut old_objs = Vec::new();
        for &(value, old_obj) in &spilled_values {
            if !old_obj_stable.contains_key(&old_obj) {
                old_objs.push(old_obj);
            }
            let stable = stable_spill_values.contains(value);
            old_obj_stable
                .entry(old_obj)
                .and_modify(|known| *known |= stable)
                .or_insert(stable);
        }

        let objs = old_objs
            .into_iter()
            .map(|old_obj| (old_obj, old_obj_stable[&old_obj]))
            .collect();
        Self {
            spilled_values,
            objs,
            shared: FxHashMap::default(),
        }
    }

    /// Lets stackify objects whose stored values are never live at the same
    /// time share a word. Stackify gives every spilled value its own object,
    /// so without this a function's final spill words grow with its total spill
    /// count rather than its peak spill pressure. Must-stable and optional
    /// objects are packed separately, since optional placement is chosen later.
    pub(crate) fn share_disjoint_objects(&mut self, function: &Function, alloc: &StackifyAlloc) {
        if self.objs.len() < 2 {
            return;
        }

        // Object accesses at the action sites emission runs, in execution order.
        let machine_isa = EvmMachine::new(function.dfg.ctx.triple);
        let entry = function.layout.entry_block();
        let mut accesses: SecondaryMap<BlockId, Vec<SpillObjectAccess>> = SecondaryMap::new();
        let push = |accesses: &mut Vec<SpillObjectAccess>, actions: &[Action], kills: bool| {
            accesses.extend(actions.iter().filter_map(|action| match *action {
                Action::MemLoadObj(obj) => Some(SpillObjectAccess::Load(obj)),
                Action::MemStoreObj(obj) => Some(SpillObjectAccess::Store { obj, kills }),
                _ => None,
            }));
        };
        let mut entry_accesses = 0;
        for block in function.layout.iter_block() {
            let block_accesses = &mut accesses[block];
            if entry == Some(block) {
                push(block_accesses, &alloc.enter_function(function), true);
                entry_accesses = block_accesses.len();
            }
            let last_inst = function.layout.last_inst_of(block);
            for inst in function.layout.iter_inst(block) {
                push(block_accesses, alloc.pre_inst(inst), true);
                // Case actions run in order until a case matches, so only the
                // first case's actions run on every path through the dispatch.
                if let EvmMachineInstKind::BrTable(br) =
                    machine_isa.inst_set().resolve_inst(function.dfg.inst(inst))
                {
                    for case_idx in 0..br.table().len() {
                        let actions = alloc.br_table_case(inst, case_idx);
                        push(block_accesses, actions, case_idx == 0);
                    }
                }
                push(
                    block_accesses,
                    alloc.post_inst(inst),
                    Some(inst) != last_inst,
                );
            }
        }
        debug_assert_eq!(
            accesses.values().map(Vec::len).sum::<usize>() - entry_accesses,
            {
                let mut stored = 0;
                alloc.for_each_action(|action| {
                    stored += usize::from(matches!(
                        action,
                        Action::MemLoadObj(_) | Action::MemStoreObj(_)
                    ));
                });
                stored
            },
            "spill word sharing must see every stored object action"
        );

        let mut cfg = ControlFlowGraph::default();
        cfg.compute(function);
        let conflicts = spill_object_conflicts(&cfg, &accesses);
        // Each word's representative, whether it is stable, and the union of
        // its members' conflicts.
        let mut words: Vec<(StackObjId, bool, BitSet<StackObjId>)> = Vec::new();
        for &(obj, must_stable) in &self.objs {
            match words.iter_mut().find(|(_, stable, word_conflicts)| {
                *stable == must_stable && !word_conflicts.contains(obj)
            }) {
                Some((rep, _, word_conflicts)) => {
                    word_conflicts.union_with(&conflicts[obj]);
                    self.shared.insert(obj, *rep);
                }
                None => words.push((obj, must_stable, conflicts[obj].clone())),
            }
        }
        self.objs = words
            .into_iter()
            .map(|(rep, must_stable, _)| (rep, must_stable))
            .collect();
    }

    fn is_empty(&self) -> bool {
        self.objs.is_empty()
    }

    fn has_optional_spills(&self) -> bool {
        self.objs.iter().any(|obj| !obj.1)
    }

    pub(crate) fn required_reserve(
        &self,
        mem_plan: &MachineFuncPlan,
        final_scratch_reserve: FinalScratchReserveRange,
        current_reserve: BackendSpillReserve,
        fixed_writes: &[FixedMemoryWriteRange],
        optional_placement: OptionalFinalSpillPlacement,
    ) -> BackendSpillReserve {
        if self.is_empty() {
            return BackendSpillReserve::default();
        }

        let must_stable_words = spill_count(self.objs.iter().filter(|obj| obj.1).count());
        let optional_words = spill_count(self.objs.len()) - must_stable_words;
        let optional_stable = match optional_placement {
            OptionalFinalSpillPlacement::Scratch => 0,
            OptionalFinalSpillPlacement::Stable => optional_words,
        };
        let stable_words = must_stable_words
            .checked_add(optional_stable)
            .expect("final stable spill count overflow");
        let scratch_words = optional_words - optional_stable;
        BackendSpillReserve {
            scratch_words: required_scratch_reserve_words(
                mem_plan,
                final_scratch_reserve.start_word,
                scratch_words,
                fixed_writes,
            ),
            stable_words: required_stable_reserve_words(
                mem_plan,
                current_reserve.stable_words,
                stable_words,
                fixed_writes,
            ),
        }
    }
}

pub(crate) struct MachineFinalSpillInput {
    pub(crate) func: FuncRef,
    pub(crate) analysis: MachineStackifyAnalysis,
    pub(crate) mem_plan: MachineFuncPlan,
    pub(crate) final_scratch_reserve: FinalScratchReserveRange,
    pub(crate) reserve: BackendSpillReserve,
    pub(crate) fixed_writes: Vec<FixedMemoryWriteRange>,
    pub(crate) spills: FinalSpillObjects,
}

type FinalSpillChoiceScore = (u32, u32, u32, u32, u64, u64);

#[cfg(debug_assertions)]
pub(crate) struct FinalSpillReplanCtx<'a> {
    pub(crate) source_module: &'a Module,
    pub(crate) section_entry: FuncRef,
    pub(crate) section_includes: &'a [FuncRef],
    pub(crate) pre_analyses: &'a FxHashMap<FuncRef, FuncPreAnalysis>,
    pub(crate) ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    pub(crate) backend: &'a EvmBackend,
}

pub(crate) struct FinalSpillChoiceCtx<'a> {
    pub(crate) schedule: &'a CallGraphSchedule,
    pub(crate) base_placement: &'a EvmMemoryPlacementPlan,
    pub(crate) fixed_reservations: &'a SectionMemoryLayout,
    pub(crate) funcs: &'a [FuncRef],
    pub(crate) base_fixed_slot_effects: &'a FxHashSet<FuncRef>,
    pub(crate) inputs: &'a [MachineFinalSpillInput],
    #[cfg(debug_assertions)]
    pub(crate) replan: FinalSpillReplanCtx<'a>,
}

impl FinalSpillChoiceCtx<'_> {
    pub(crate) fn choose_optional_placements(
        &self,
    ) -> FxHashMap<FuncRef, OptionalFinalSpillPlacement> {
        let mut choices: FxHashMap<FuncRef, OptionalFinalSpillPlacement> = self
            .inputs
            .iter()
            .filter(|input| input.spills.has_optional_spills())
            .map(|input| (input.func, OptionalFinalSpillPlacement::Scratch))
            .collect();
        if choices.is_empty() {
            return choices;
        }

        let mut best_score = self.score(&choices);
        let mut all_stable = choices.clone();
        for choice in all_stable.values_mut() {
            *choice = OptionalFinalSpillPlacement::Stable;
        }
        let all_stable_score = self.score(&all_stable);
        if all_stable_score < best_score {
            choices = all_stable;
            best_score = all_stable_score;
        }

        for input in self
            .inputs
            .iter()
            .filter(|input| input.spills.has_optional_spills())
        {
            let mut trial = choices.clone();
            let next = match trial[&input.func] {
                OptionalFinalSpillPlacement::Scratch => OptionalFinalSpillPlacement::Stable,
                OptionalFinalSpillPlacement::Stable => OptionalFinalSpillPlacement::Scratch,
            };
            trial.insert(input.func, next);
            let score = self.score(&trial);
            if score < best_score {
                choices = trial;
                best_score = score;
            }
        }

        choices
    }

    /// Scores a choice assignment with the closed-form marginal model: the
    /// per-function placements themselves are reserve-independent, so a trial
    /// reserve only shifts each function's frame words by its delta over the
    /// committed reserve, and the section aggregates are recomputed directly.
    ///
    /// Two second-order feedback paths are deliberately approximated by
    /// holding them at their base-placement values (a trial reserve cannot
    /// change them exactly without a full replan): private-static-malloc
    /// extra scratch, and transient-malloc flips induced by new fixed-slot
    /// effects. Set SONATINA_SPILL_SCORE_XCHECK=1 in a debug build to
    /// cross-check against the full replan.
    fn score(
        &self,
        choices: &FxHashMap<FuncRef, OptionalFinalSpillPlacement>,
    ) -> FinalSpillChoiceScore {
        let reserves = self.final_spill_reserves(choices);
        let marginal = self.score_marginal(&reserves);
        #[cfg(debug_assertions)]
        if std::env::var_os("SONATINA_SPILL_SCORE_XCHECK").is_some() {
            let replanned = self.score_by_replanning(&reserves);
            if marginal != replanned {
                eprintln!(
                    "SPILL_SCORE_XCHECK mismatch: marginal={marginal:?} replanned={replanned:?}"
                );
            }
        }
        marginal
    }

    fn score_marginal(
        &self,
        reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
    ) -> FinalSpillChoiceScore {
        let committed = |func: FuncRef| {
            self.inputs
                .iter()
                .find(|input| input.func == func)
                .map(|input| input.reserve)
                .unwrap_or_default()
        };
        let trial_words = |func: FuncRef| -> (u32, u32) {
            let base = &self.base_placement.funcs[&func].mem_plan;
            let trial = reserves.get(&func).copied().unwrap_or_default();
            let committed = committed(func);
            let scratch_delta = trial
                .scratch_words
                .checked_sub(committed.scratch_words)
                .expect("trial reserve below committed reserve");
            let stable_delta = trial
                .stable_words
                .checked_sub(committed.stable_words)
                .expect("trial reserve below committed reserve");
            (
                memory_plan::add_words(base.scratch_words, scratch_delta),
                memory_plan::add_words(base.stable_words, stable_delta),
            )
        };

        let reserve_scratch_peak = reserves
            .values()
            .map(|reserve| reserve.scratch_words)
            .max()
            .unwrap_or(0);
        let has_dynamic_frames = self
            .base_placement
            .funcs
            .values()
            .any(|plan| plan.mem_plan.uses_dynamic_frame());

        let mut scratch_peak_words = self
            .funcs
            .iter()
            .map(|&func| trial_words(func).0)
            .max()
            .unwrap_or(0);
        if has_dynamic_frames {
            scratch_peak_words = scratch_peak_words.max(reserve_scratch_peak);
        }
        let chain =
            memory_plan::compute_stable_chain_layout(self.schedule, |func| trial_words(func).1);

        let has_stackify_fixed_slot_spills = !self.base_fixed_slot_effects.is_empty()
            || reserves.values().any(|reserve| reserve.scratch_words != 0);
        let arena_base = choose_arena_base(
            self.fixed_reservations,
            ArenaBaseFacts {
                has_dynamic_frames,
                has_stackify_fixed_slot_spills,
                backend_spill_scratch_reserve_words: reserve_scratch_peak,
                has_heap_mallocs: self.base_placement.has_heap_mallocs,
            },
        );
        let global_dyn_base = arena_base
            .checked_add(
                memory_plan::add_words(scratch_peak_words, chain.peak_words)
                    .checked_mul(WORD_BYTES)
                    .expect("global dynamic base overflow"),
            )
            .expect("global dynamic base overflow");

        (
            global_dyn_base,
            arena_base,
            scratch_peak_words,
            chain.peak_words,
            reserves
                .values()
                .map(|reserve| u64::from(reserve.stable_words))
                .sum(),
            reserves
                .values()
                .map(|reserve| u64::from(reserve.scratch_words))
                .sum(),
        )
    }

    /// The pre-marginal-model scorer: a full section replan per evaluation.
    /// Kept as the cross-check oracle for the marginal model.
    #[cfg(debug_assertions)]
    fn score_by_replanning(
        &self,
        reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
    ) -> FinalSpillChoiceScore {
        let replan = &self.replan;
        let mut fixed_slot_effects = self.base_fixed_slot_effects.clone();
        for (&func, reserve) in reserves {
            if reserve.scratch_words != 0 {
                fixed_slot_effects.insert(func);
            }
        }

        let placement = compute_semantic_memory_placement(
            replan.source_module,
            MemoryPlacementSection {
                schedule: self.schedule,
                funcs: self.funcs,
                entry: replan.section_entry,
                includes: replan.section_includes,
                fixed_reservations: self.fixed_reservations,
            },
            replan.pre_analyses,
            replan.ptr_escape,
            &fixed_slot_effects,
            replan.backend,
            &BackendSpillPlan {
                reserves: reserves.clone(),
                malloc_bounds: FxHashMap::default(),
            },
        );

        (
            placement.global_dyn_base,
            placement.arena_base,
            placement.scratch_peak_words,
            placement.stable_chain_peak_words,
            reserves
                .values()
                .map(|reserve| u64::from(reserve.stable_words))
                .sum(),
            reserves
                .values()
                .map(|reserve| u64::from(reserve.scratch_words))
                .sum(),
        )
    }

    fn final_spill_reserves(
        &self,
        choices: &FxHashMap<FuncRef, OptionalFinalSpillPlacement>,
    ) -> FxHashMap<FuncRef, BackendSpillReserve> {
        self.inputs
            .iter()
            .map(|input| {
                let choice = choices
                    .get(&input.func)
                    .copied()
                    .unwrap_or(OptionalFinalSpillPlacement::Scratch);
                (
                    input.func,
                    input.reserve.pointwise_max(input.spills.required_reserve(
                        &input.mem_plan,
                        input.final_scratch_reserve,
                        input.reserve,
                        &input.fixed_writes,
                        choice,
                    )),
                )
            })
            .collect()
    }
}

pub(crate) fn allocate_final_spills(
    input: FinalSpillAllocationInput,
) -> Result<FinalSpillAllocation, String> {
    let FinalSpillAllocationInput {
        func,
        mut alloc,
        mut mem_plan,
        final_scratch_reserve,
        reserve,
        fixed_writes,
        spills,
        optional_placement,
    } = input;

    if spills.is_empty() {
        alloc.validate_spill_storage();
        return Ok(FinalSpillAllocation {
            alloc,
            mem_plan,
            required_reserve: BackendSpillReserve::default(),
            stack_obj_remap: FxHashMap::default(),
            used_fallback: false,
        });
    }

    let mut next_obj = mem_plan
        .obj_loc
        .keys()
        .map(|id| id.as_u32())
        .max()
        .map_or(0, |id| id.checked_add(1).expect("stack object id overflow"));
    let mut remap: FxHashMap<StackObjId, StackObjId> = FxHashMap::default();
    for &(old_obj, _) in &spills.objs {
        remap.insert(old_obj, {
            let obj = StackObjId::new(next_obj as usize);
            next_obj = next_obj.checked_add(1).expect("stack object id overflow");
            obj
        });
    }
    let mut final_objs: Vec<_> = remap.values().copied().collect();
    final_objs.sort_unstable();
    for (&old_obj, rep) in &spills.shared {
        remap.insert(old_obj, remap[rep]);
    }

    let mut scratch_objs = Vec::new();
    let mut stable_objs = Vec::new();
    for &(old_obj, must_stable) in &spills.objs {
        let new_obj = remap[&old_obj];
        if must_stable || matches!(optional_placement, OptionalFinalSpillPlacement::Stable) {
            stable_objs.push((old_obj, new_obj));
        } else {
            scratch_objs.push((old_obj, new_obj));
        }
    }

    let required_reserve = spills.required_reserve(
        &mem_plan,
        final_scratch_reserve,
        reserve,
        &fixed_writes,
        optional_placement,
    );

    let scratch_fallback = place_scratch_spills(
        &mut mem_plan,
        &scratch_objs,
        final_scratch_reserve,
        required_reserve.scratch_words,
        &fixed_writes,
    );
    let stable_fallback = place_stable_spills(
        &mut mem_plan,
        &stable_objs,
        reserve,
        required_reserve.stable_words,
        &fixed_writes,
    );
    let used_fallback = scratch_fallback || stable_fallback;
    validate_final_spill_absolute_disjointness(func, &mem_plan, &final_objs)?;
    validate_final_spills_disjoint_from_fixed_writes(func, &mem_plan, &final_objs, &fixed_writes)?;
    validate_final_spill_regions(
        func,
        &mem_plan,
        final_scratch_reserve,
        reserve,
        &scratch_objs,
        &stable_objs,
        (scratch_fallback, stable_fallback),
    )?;

    alloc.remap_stack_objects(&remap);
    for (value, old_obj) in spills.spilled_values {
        let new_obj = remap[&old_obj];
        alloc.set_spill_object(value, new_obj);
        mem_plan.spill_obj[value] = Some(new_obj);
    }
    alloc.validate_spill_storage();

    Ok(FinalSpillAllocation {
        alloc,
        mem_plan,
        required_reserve,
        stack_obj_remap: remap,
        used_fallback,
    })
}

/// A spill object access in execution order within a block.
#[derive(Clone, Copy)]
enum SpillObjectAccess {
    Load(StackObjId),
    /// `kills` is false for stores that may not run before every later access
    /// in the block: `br_table` case actions after the first, and actions after
    /// a block's terminator.
    Store {
        obj: StackObjId,
        kills: bool,
    },
}

/// Pairs of spill objects that must not share a word: one is stored while the
/// other holds a value that a later load reads.
fn spill_object_conflicts(
    cfg: &ControlFlowGraph,
    accesses: &SecondaryMap<BlockId, Vec<SpillObjectAccess>>,
) -> SecondaryMap<StackObjId, BitSet<StackObjId>> {
    let blocks: Vec<BlockId> = cfg.post_order().collect();
    let mut live_in: SecondaryMap<BlockId, BitSet<StackObjId>> = SecondaryMap::new();
    let mut conflicts: SecondaryMap<StackObjId, BitSet<StackObjId>> = SecondaryMap::new();
    // Live sets only grow, so conflicts recorded before the fixpoint are a
    // subset of the final ones.
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &blocks {
            let mut live = BitSet::default();
            for &succ in cfg.succs_of(block) {
                live.union_with(&live_in[succ]);
            }
            for access in accesses[block].iter().rev() {
                match *access {
                    SpillObjectAccess::Load(obj) => {
                        live.insert(obj);
                    }
                    SpillObjectAccess::Store { obj, kills } => {
                        for other in live.iter().filter(|&other| other != obj) {
                            conflicts[obj].insert(other);
                            conflicts[other].insert(obj);
                        }
                        if kills {
                            live.remove(obj);
                        }
                    }
                }
            }
            if live_in[block] != live {
                live_in[block] = live;
                changed = true;
            }
        }
    }
    conflicts
}

fn final_spilled_values(alloc: &StackifyAlloc) -> Vec<(ValueId, StackObjId)> {
    alloc.object_spills().collect()
}

fn spill_count(len: usize) -> u32 {
    u32::try_from(len).expect("spill count overflow")
}

fn required_scratch_reserve_words(
    mem_plan: &MachineFuncPlan,
    final_scratch_start_word: u32,
    spill_words: u32,
    fixed_writes: &[FixedMemoryWriteRange],
) -> u32 {
    if spill_words == 0 {
        return 0;
    }

    let forbidden = forbidden_arena_words(mem_plan, fixed_writes);
    let start = first_safe_word_block(final_scratch_start_word, u32::MAX, spill_words, &forbidden)
        .expect("final scratch spill reserve search overflow");
    start
        .checked_add(spill_words)
        .and_then(|end| end.checked_sub(final_scratch_start_word))
        .expect("final scratch spill reserve demand overflow")
}

fn required_stable_reserve_words(
    mem_plan: &MachineFuncPlan,
    current_reserved_words: u32,
    spill_words: u32,
    fixed_writes: &[FixedMemoryWriteRange],
) -> u32 {
    if spill_words == 0 {
        return 0;
    }

    match mem_plan.stable_mode {
        StableMode::None | StableMode::DynamicFrame => spill_words,
        StableMode::StableAbs { .. } => {
            let semantic_stable_words = mem_plan
                .stable_words
                .checked_sub(current_reserved_words)
                .expect("reserved stable spill words exceed stable words");
            let forbidden = forbidden_static_stable_offsets(mem_plan, fixed_writes);
            let start =
                first_safe_word_block(semantic_stable_words, u32::MAX, spill_words, &forbidden)
                    .expect("final stable spill reserve search overflow");
            start
                .checked_add(spill_words)
                .and_then(|end| end.checked_sub(semantic_stable_words))
                .expect("final stable spill reserve demand overflow")
        }
    }
}

fn place_scratch_spills(
    mem_plan: &mut MachineFuncPlan,
    objs: &[(StackObjId, StackObjId)],
    final_scratch_reserve: FinalScratchReserveRange,
    required_words: u32,
    fixed_writes: &[FixedMemoryWriteRange],
) -> bool {
    let spill_words = u32::try_from(objs.len()).expect("spill count overflow");
    if spill_words == 0 {
        return false;
    }

    let forbidden = forbidden_arena_words(mem_plan, fixed_writes);
    let reserve_end = final_scratch_reserve
        .start_word
        .checked_add(final_scratch_reserve.words)
        .expect("final scratch reserve range overflow");
    let reserved_start = (required_words <= final_scratch_reserve.words)
        .then(|| {
            first_safe_word_block(
                final_scratch_reserve.start_word,
                reserve_end,
                spill_words,
                &forbidden,
            )
        })
        .flatten();
    let start_word = if let Some(start) = reserved_start {
        start
    } else {
        mem_plan
            .abs_words_end()
            .max(spill_floor_words_from_fixed_writes(mem_plan, fixed_writes))
    };
    place_spills(mem_plan, objs, start_word, ObjLoc::ScratchAbs);
    if reserved_start.is_none() {
        let scratch_peak_words = start_word
            .checked_add(spill_words)
            .expect("final scratch spill peak overflow");
        mem_plan.scratch_words = mem_plan.scratch_words.max(scratch_peak_words);
    }
    reserved_start.is_none()
}

fn place_stable_spills(
    mem_plan: &mut MachineFuncPlan,
    objs: &[(StackObjId, StackObjId)],
    reserve: BackendSpillReserve,
    required_words: u32,
    fixed_writes: &[FixedMemoryWriteRange],
) -> bool {
    let spill_words = u32::try_from(objs.len()).expect("spill count overflow");
    if spill_words == 0 {
        return false;
    }

    let stable_mode = mem_plan.stable_mode;
    let reserved_start = match stable_mode {
        StableMode::StableAbs { .. } => {
            let (reserve_start, reserve_end) = stable_reserve_range(mem_plan, reserve.stable_words)
                .expect("static stable reserve exceeds stable words");
            (required_words <= reserve.stable_words)
                .then(|| {
                    first_safe_word_block(
                        reserve_start,
                        reserve_end,
                        spill_words,
                        &forbidden_static_stable_offsets(mem_plan, fixed_writes),
                    )
                })
                .flatten()
        }
        StableMode::DynamicFrame => stable_tail_start(mem_plan, spill_words)
            .filter(|_| required_words <= reserve.stable_words),
        StableMode::None => None,
    };
    let start_word = if let Some(start) = reserved_start {
        start
    } else {
        mem_plan
            .abs_words_end()
            .max(spill_floor_words_from_fixed_writes(mem_plan, fixed_writes))
    };
    let loc = |word| match (reserved_start.is_some(), stable_mode) {
        (true, StableMode::StableAbs { .. }) => ObjLoc::StableAbs(word),
        (true, StableMode::DynamicFrame) => ObjLoc::StableFrame(word),
        (true, StableMode::None) => unreachable!("stable tail requires stable mode"),
        (false, _) => ObjLoc::ScratchAbs(word),
    };
    place_spills(mem_plan, objs, start_word, loc);
    if reserved_start.is_none() {
        let scratch_peak_words = start_word
            .checked_add(spill_words)
            .expect("final stable spill fallback peak overflow");
        mem_plan.scratch_words = mem_plan.scratch_words.max(scratch_peak_words);
    }
    reserved_start.is_none()
}

fn place_spills(
    mem_plan: &mut MachineFuncPlan,
    objs: &[(StackObjId, StackObjId)],
    start_word: u32,
    loc: impl Fn(u32) -> ObjLoc,
) {
    for (idx, &(_, new_obj)) in objs.iter().enumerate() {
        let word = start_word
            .checked_add(u32::try_from(idx).expect("spill count overflow"))
            .expect("final spill word overflow");
        mem_plan.obj_loc.insert(new_obj, loc(word));
    }
}

fn stable_tail_start(mem_plan: &MachineFuncPlan, spill_words: u32) -> Option<u32> {
    match mem_plan.stable_mode {
        StableMode::StableAbs { .. } | StableMode::DynamicFrame => {
            mem_plan.stable_words.checked_sub(spill_words)
        }
        StableMode::None => None,
    }
}

fn stable_reserve_range(mem_plan: &MachineFuncPlan, reserved_words: u32) -> Option<(u32, u32)> {
    match mem_plan.stable_mode {
        StableMode::StableAbs { .. } | StableMode::DynamicFrame => Some((
            mem_plan.stable_words.checked_sub(reserved_words)?,
            mem_plan.stable_words,
        )),
        StableMode::None => None,
    }
}

fn first_safe_word_block(
    region_start_word: u32,
    region_end_word: u32,
    words: u32,
    forbidden_word_ranges: &[(u32, u32)],
) -> Option<u32> {
    let mut candidate = region_start_word;
    let forbidden_word_ranges = normalized_word_ranges(forbidden_word_ranges);
    for &(start, end) in &forbidden_word_ranges {
        if end <= candidate {
            continue;
        }
        let candidate_end = candidate.checked_add(words)?;
        if candidate_end <= start {
            break;
        }
        candidate = candidate.max(end);
        if candidate.checked_add(words)? > region_end_word {
            return None;
        }
    }

    (candidate.checked_add(words)? <= region_end_word).then_some(candidate)
}

fn normalized_word_ranges(ranges: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut ranges: Vec<_> = ranges
        .iter()
        .copied()
        .filter(|(start, end)| start < end)
        .collect();
    ranges.sort_unstable();

    let mut out: Vec<(u32, u32)> = Vec::new();
    for (start, end) in ranges {
        if let Some((_, last_end)) = out.last_mut()
            && start <= *last_end
        {
            *last_end = (*last_end).max(end);
            continue;
        }
        out.push((start, end));
    }
    out
}

fn spill_floor_words_from_fixed_writes(
    mem_plan: &MachineFuncPlan,
    fixed_writes: &[FixedMemoryWriteRange],
) -> u32 {
    forbidden_arena_words(mem_plan, fixed_writes)
        .iter()
        .map(|(_, end)| *end)
        .max()
        .unwrap_or(0)
}

fn forbidden_arena_words(
    mem_plan: &MachineFuncPlan,
    fixed_writes: &[FixedMemoryWriteRange],
) -> Vec<(u32, u32)> {
    normalized_word_ranges(
        &fixed_writes
            .iter()
            .filter_map(|&write| fixed_write_forbidden_arena_words(mem_plan.arena_base, write))
            .collect::<Vec<_>>(),
    )
}

fn fixed_write_forbidden_arena_words(
    arena_base: u32,
    write: FixedMemoryWriteRange,
) -> Option<(u32, u32)> {
    if write.end_byte <= arena_base {
        return None;
    }

    let rel_start = write.start_byte.saturating_sub(arena_base);
    let rel_end = write.end_byte.checked_sub(arena_base)?;
    let start_word = rel_start / WORD_BYTES;
    let end_word = align_up_to_word(rel_end)?.checked_div(WORD_BYTES)?;
    (start_word < end_word).then_some((start_word, end_word))
}

fn forbidden_static_stable_offsets(
    mem_plan: &MachineFuncPlan,
    fixed_writes: &[FixedMemoryWriteRange],
) -> Vec<(u32, u32)> {
    let StableMode::StableAbs { base_word } = mem_plan.stable_mode else {
        return Vec::new();
    };

    normalized_word_ranges(
        &forbidden_arena_words(mem_plan, fixed_writes)
            .into_iter()
            .filter_map(|(start_word, end_word)| {
                if end_word <= base_word {
                    return None;
                }

                let start = start_word.saturating_sub(base_word);
                let end = end_word.checked_sub(base_word)?;
                (start < end).then_some((start, end))
            })
            .collect::<Vec<_>>(),
    )
}

fn absolute_word_for_loc(mem_plan: &MachineFuncPlan, loc: ObjLoc) -> Result<Option<u32>, String> {
    match loc {
        ObjLoc::ScratchAbs(word) => Ok(Some(word)),
        ObjLoc::StableAbs(off) => mem_plan
            .stable_base_word()
            .map(|base| {
                base.checked_add(off)
                    .ok_or_else(|| format!("final spill stable address overflow at offset {off}"))
            })
            .transpose(),
        ObjLoc::StableFrame(_) => Ok(None),
    }
}

fn validate_final_spill_absolute_disjointness(
    func: FuncRef,
    mem_plan: &MachineFuncPlan,
    final_objs: &[StackObjId],
) -> Result<(), String> {
    let mut ranges = Vec::new();
    for &obj in final_objs {
        let loc = mem_plan.obj_loc.get(&obj).copied().ok_or_else(|| {
            format!(
                "missing final spill location in func {} for obj {}",
                func.as_u32(),
                obj.as_u32()
            )
        })?;
        let Some(start) = absolute_word_for_loc(mem_plan, loc)? else {
            continue;
        };
        let end = start.checked_add(1).ok_or_else(|| {
            format!(
                "final spill range overflow in func {} for obj {}",
                func.as_u32(),
                obj.as_u32()
            )
        })?;
        ranges.push((start, end, obj, loc));
    }

    ranges.sort_by_key(|&(start, end, obj, _)| (start, end, obj.as_u32()));
    for pair in ranges.windows(2) {
        let (a_start, a_end, a_obj, a_loc) = pair[0];
        let (b_start, b_end, b_obj, b_loc) = pair[1];
        if b_start < a_end {
            return Err(format!(
                "EVM final spill absolute-memory overlap in func {}: obj {} {:?} [{}, {}) overlaps obj {} {:?} [{}, {})",
                func.as_u32(),
                a_obj.as_u32(),
                a_loc,
                a_start,
                a_end,
                b_obj.as_u32(),
                b_loc,
                b_start,
                b_end,
            ));
        }
    }

    Ok(())
}

fn validate_final_spills_disjoint_from_fixed_writes(
    func: FuncRef,
    mem_plan: &MachineFuncPlan,
    final_objs: &[StackObjId],
    fixed_writes: &[FixedMemoryWriteRange],
) -> Result<(), String> {
    for &obj in final_objs {
        let loc = mem_plan.obj_loc.get(&obj).copied().ok_or_else(|| {
            format!(
                "missing final spill location in func {} for obj {}",
                func.as_u32(),
                obj.as_u32()
            )
        })?;
        let Some((spill_start, spill_end)) = absolute_byte_range_for_loc(mem_plan, loc)? else {
            continue;
        };
        for &write in fixed_writes {
            if byte_ranges_overlap(spill_start, spill_end, write.start_byte, write.end_byte) {
                return Err(format!(
                    "EVM final spill fixed memory write overlap in func {}: obj {} {:?} [0x{:x}, 0x{:x}) overlaps inst {} fixed write [0x{:x}, 0x{:x})",
                    func.as_u32(),
                    obj.as_u32(),
                    loc,
                    spill_start,
                    spill_end,
                    write.inst.as_u32(),
                    write.start_byte,
                    write.end_byte,
                ));
            }
        }
    }

    Ok(())
}

/// A [`dynamic_terminal_payload`] write is exempt from layout reservations, so it
/// may overwrite any compiler-managed memory from its start upward. The terminal
/// still needs `len` after the write; if `len` is spilled there, the terminal would
/// reload clobbered bytes.
pub(crate) fn validate_dynamic_terminal_payload_spills(
    func: FuncRef,
    function: &Function,
    alloc: &StackifyAlloc,
    mem_plan: &MachineFuncPlan,
) -> Result<(), String> {
    for block in function.layout.iter_block() {
        let Some(payload) = function
            .layout
            .last_inst_of(block)
            .and_then(|terminal| dynamic_terminal_payload(function, terminal))
        else {
            continue;
        };
        let spill_range = if let Some(slot) = alloc.scratch_slot(payload.len) {
            Some((slot * WORD_BYTES, (slot + 1) * WORD_BYTES))
        } else if let Some(obj) = alloc.spill_obj(payload.len) {
            let loc = mem_plan.obj_loc.get(&obj).copied().ok_or_else(|| {
                format!(
                    "missing spill location in func {} for obj {}",
                    func.as_u32(),
                    obj.as_u32()
                )
            })?;
            // Dynamic-frame spills have no static address, so assume the write reaches them.
            absolute_byte_range_for_loc(mem_plan, loc)?
        } else {
            continue;
        };
        if spill_range.is_none_or(|(_, end)| end > payload.start) {
            let name = function.ctx().func_sig(func, |sig| sig.name().to_string());
            return Err(format!(
                "EVM terminal payload in %{name} reloads its length v{} from spill memory at {} after the payload write at 0x{:x} overwrites it",
                payload.len.as_u32(),
                spill_range.map_or("a dynamic frame".to_string(), |(start, _)| format!(
                    "0x{start:x}"
                )),
                payload.start,
            ));
        }
    }
    Ok(())
}

fn absolute_byte_range_for_loc(
    mem_plan: &MachineFuncPlan,
    loc: ObjLoc,
) -> Result<Option<(u32, u32)>, String> {
    let Some(word) = absolute_word_for_loc(mem_plan, loc)? else {
        return Ok(None);
    };
    let start = mem_plan
        .arena_base
        .checked_add(
            word.checked_mul(WORD_BYTES)
                .ok_or_else(|| format!("final spill byte range overflow at word {word}"))?,
        )
        .ok_or_else(|| format!("final spill byte range overflow at word {word}"))?;
    let end = start
        .checked_add(WORD_BYTES)
        .ok_or_else(|| format!("final spill byte range overflow at word {word}"))?;
    Ok(Some((start, end)))
}

fn byte_ranges_overlap(a_start: u32, a_end: u32, b_start: u32, b_end: u32) -> bool {
    a_start < b_end && b_start < a_end
}

fn validate_final_spill_regions(
    func: FuncRef,
    mem_plan: &MachineFuncPlan,
    final_scratch_reserve: FinalScratchReserveRange,
    reserve: BackendSpillReserve,
    scratch_objs: &[(StackObjId, StackObjId)],
    stable_objs: &[(StackObjId, StackObjId)],
    fallback: (bool, bool),
) -> Result<(), String> {
    let (scratch_fallback, stable_fallback) = fallback;
    if !scratch_fallback {
        for &(_, obj) in scratch_objs {
            let loc = mem_plan.obj_loc.get(&obj).copied().ok_or_else(|| {
                format!(
                    "missing scratch final spill location in func {} for obj {}",
                    func.as_u32(),
                    obj.as_u32()
                )
            })?;
            let ObjLoc::ScratchAbs(word) = loc else {
                return Err(format!(
                    "scratch final spill in func {} obj {} used non-scratch location {:?}",
                    func.as_u32(),
                    obj.as_u32(),
                    loc
                ));
            };
            if !final_scratch_reserve.contains(word, 1) {
                return Err(format!(
                    "scratch final spill in func {} obj {} at word {} is outside final scratch reserve [{}, {})",
                    func.as_u32(),
                    obj.as_u32(),
                    word,
                    final_scratch_reserve.start_word,
                    final_scratch_reserve
                        .start_word
                        .checked_add(final_scratch_reserve.words)
                        .expect("final scratch reserve end overflow")
                ));
            }
        }
    }

    if !stable_fallback {
        let reserved_stable_range = stable_reserve_range(mem_plan, reserve.stable_words);
        for &(_, obj) in stable_objs {
            let loc = mem_plan.obj_loc.get(&obj).copied().ok_or_else(|| {
                format!(
                    "missing stable final spill location in func {} for obj {}",
                    func.as_u32(),
                    obj.as_u32()
                )
            })?;
            let valid = matches!(
                (mem_plan.stable_mode, loc),
                (StableMode::StableAbs { .. }, ObjLoc::StableAbs(_))
                    | (StableMode::DynamicFrame, ObjLoc::StableFrame(_))
            );
            if !valid {
                return Err(format!(
                    "stable final spill in func {} obj {} used invalid location {:?} with stable mode {:?}",
                    func.as_u32(),
                    obj.as_u32(),
                    loc,
                    mem_plan.stable_mode
                ));
            }
            let off = match loc {
                ObjLoc::StableAbs(off) | ObjLoc::StableFrame(off) => off,
                ObjLoc::ScratchAbs(_) => unreachable!("validated above"),
            };
            let Some((reserve_start, reserve_end)) = reserved_stable_range else {
                return Err(format!(
                    "stable final spill in func {} obj {} has no reserved stable tail with stable mode {:?}",
                    func.as_u32(),
                    obj.as_u32(),
                    mem_plan.stable_mode
                ));
            };
            if !(reserve_start <= off && off < reserve_end) {
                return Err(format!(
                    "stable final spill in func {} obj {} at offset {} is outside final stable reserve [{}, {})",
                    func.as_u32(),
                    obj.as_u32(),
                    off,
                    reserve_start,
                    reserve_end
                ));
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use cranelift_entity::{EntityRef, SecondaryMap};
    use rustc_hash::FxHashMap;
    use sonatina_ir::{InstId, ValueId, cfg::ControlFlowGraph, module::FuncRef};
    use sonatina_parser::parse_module;

    use super::{
        FinalSpillAllocation, FinalSpillAllocationInput, FinalSpillObjects, FixedMemoryWriteRange,
        OptionalFinalSpillPlacement, SpillObjectAccess,
        allocate_final_spills as alloc_final_spills, spill_object_conflicts,
        validate_final_spill_absolute_disjointness,
        validate_final_spills_disjoint_from_fixed_writes,
    };
    use crate::{
        bitset::BitSet,
        isa::evm::{
            MachineFuncPlan, ObjLoc,
            memory_plan::{BackendSpillReserve, FinalScratchReserveRange, StableMode},
            static_arena_alloc::StackObjId,
        },
        stackalloc::StackifyAlloc,
    };

    fn static_mem_plan(scratch_words: u32, stable_words: u32) -> MachineFuncPlan {
        MachineFuncPlan {
            arena_base: 0xa0,
            scratch_words,
            stable_words,
            stable_mode: StableMode::StableAbs {
                base_word: scratch_words,
            },
            entry_abs_words: scratch_words,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            spill_obj: SecondaryMap::new(),
            call_preserve: FxHashMap::default(),
        }
    }

    fn scratch_mem_plan(scratch_words: u32) -> MachineFuncPlan {
        MachineFuncPlan {
            arena_base: 0xa0,
            scratch_words,
            stable_words: 0,
            stable_mode: StableMode::None,
            entry_abs_words: scratch_words,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            spill_obj: SecondaryMap::new(),
            call_preserve: FxHashMap::default(),
        }
    }

    fn alloc_with_object_spills(values: &[(u32, u32)]) -> StackifyAlloc {
        let mut alloc = StackifyAlloc::default();
        for &(value, obj) in values {
            let value = ValueId::from_u32(value);
            let obj = StackObjId::new(obj as usize);
            alloc.set_object_spill_for_test(value, obj);
        }
        alloc
    }

    fn reserve(scratch_words: u32, stable_words: u32) -> BackendSpillReserve {
        BackendSpillReserve {
            scratch_words,
            stable_words,
        }
    }

    fn stable_values(values: &[u32]) -> BitSet<ValueId> {
        values.iter().copied().map(ValueId::from_u32).collect()
    }

    fn fixed_write(start_word: u32, words: u32) -> Vec<FixedMemoryWriteRange> {
        let start_byte = 0xa0 + start_word * 32;
        vec![FixedMemoryWriteRange {
            inst: InstId::from_u32(0),
            start_byte,
            end_byte: start_byte + words * 32,
        }]
    }

    fn allocate_final_spills(
        alloc: StackifyAlloc,
        mem_plan: MachineFuncPlan,
        reserve: BackendSpillReserve,
        stable: &BitSet<ValueId>,
        placement: OptionalFinalSpillPlacement,
    ) -> FinalSpillAllocation {
        allocate_final_spills_with_writes(alloc, mem_plan, reserve, Vec::new(), stable, placement)
    }

    fn allocate_final_spills_with_writes(
        alloc: StackifyAlloc,
        mem_plan: MachineFuncPlan,
        reserve: BackendSpillReserve,
        fixed_writes: Vec<FixedMemoryWriteRange>,
        stable: &BitSet<ValueId>,
        placement: OptionalFinalSpillPlacement,
    ) -> FinalSpillAllocation {
        let final_scratch_reserve = FinalScratchReserveRange {
            start_word: mem_plan
                .scratch_words
                .checked_sub(reserve.scratch_words)
                .expect("test reserve exceeds scratch words"),
            words: reserve.scratch_words,
        };
        let spills = FinalSpillObjects::compute(&alloc, stable);
        alloc_final_spills(FinalSpillAllocationInput {
            func: FuncRef::from_u32(0),
            alloc,
            mem_plan,
            final_scratch_reserve,
            reserve,
            fixed_writes,
            spills,
            optional_placement: placement,
        })
        .expect("final spill allocation succeeds")
    }

    #[test]
    fn zero_final_spills_do_not_count_stable_words_as_scratch() {
        let final_spills = allocate_final_spills(
            StackifyAlloc::default(),
            static_mem_plan(0, 5),
            BackendSpillReserve::default(),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(
            final_spills.required_reserve,
            BackendSpillReserve::default()
        );
        assert_eq!(final_spills.mem_plan.scratch_words, 0);
    }

    #[test]
    fn zero_final_spills_do_not_request_backend_spill_reserve() {
        let final_spills = allocate_final_spills(
            StackifyAlloc::default(),
            static_mem_plan(3, 5),
            BackendSpillReserve::default(),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(
            final_spills.required_reserve,
            BackendSpillReserve::default()
        );
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
    }

    #[test]
    fn static_final_spills_use_reserved_stable_tail() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 7),
            reserve(0, 2),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::StableAbs(5)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::StableAbs(6)
        );
    }

    #[test]
    fn insufficient_static_reserve_reports_required_words() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 7),
            reserve(0, 1),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(final_spills.mem_plan.scratch_words, 12);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(10)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(11)
        );
    }

    #[test]
    fn static_final_spills_request_only_stable_tail_words() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 7),
            BackendSpillReserve::default(),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(final_spills.mem_plan.scratch_words, 12);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(10)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(11)
        );
    }

    #[test]
    fn stable_final_spills_use_reserved_tail_when_high_fixed_write_is_disjoint() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            static_mem_plan(3, 7),
            reserve(0, 2),
            fixed_write(12, 1),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(final_spills.mem_plan.scratch_words, 3);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::StableAbs(5)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::StableAbs(6)
        );
    }

    #[test]
    fn stable_final_spills_reject_reserved_tail_when_fixed_write_overlaps() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            static_mem_plan(3, 7),
            reserve(0, 2),
            fixed_write(8, 1),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 3));
        assert!(final_spills.used_fallback);
        assert_eq!(final_spills.mem_plan.scratch_words, 12);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(10)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(11)
        );

        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            static_mem_plan(3, 8),
            reserve(0, 3),
            fixed_write(8, 1),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 3));
        assert!(!final_spills.used_fallback);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::StableAbs(6)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::StableAbs(7)
        );
    }

    #[test]
    fn stable_final_spills_use_lower_safe_subrange_when_top_conflicts() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            static_mem_plan(3, 8),
            reserve(0, 3),
            fixed_write(10, 1),
            &stable_values(&[10, 11]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(0, 2));
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::StableAbs(5)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::StableAbs(6)
        );
    }

    #[test]
    fn scratch_final_spills_use_reserved_tail() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            scratch_mem_plan(5),
            reserve(2, 0),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 5);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
    }

    #[test]
    fn scratch_final_spills_fallback_clears_fixed_memory_floor() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            scratch_mem_plan(3),
            BackendSpillReserve::default(),
            fixed_write(6, 1),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 9);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(7)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(8)
        );
    }

    #[test]
    fn scratch_fallback_uses_abs_words_end_not_scratch_words() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(3, 5),
            BackendSpillReserve::default(),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 10);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(8)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(9)
        );
    }

    #[test]
    fn scratch_final_spills_ignore_high_fixed_write_when_exact_range_is_disjoint() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            scratch_mem_plan(5),
            reserve(2, 0),
            fixed_write(6, 1),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 5);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
    }

    #[test]
    fn scratch_final_spills_reject_reserved_range_when_fixed_write_overlaps() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            scratch_mem_plan(5),
            reserve(2, 0),
            fixed_write(3, 1),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(3, 0));
        assert!(final_spills.used_fallback);
        assert_eq!(final_spills.mem_plan.scratch_words, 7);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(5)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(6)
        );

        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            scratch_mem_plan(6),
            reserve(3, 0),
            fixed_write(3, 1),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(3, 0));
        assert!(!final_spills.used_fallback);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(4)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(5)
        );
    }

    #[test]
    fn scratch_final_spills_use_lower_safe_subrange_when_top_conflicts() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let final_spills = allocate_final_spills_with_writes(
            alloc,
            scratch_mem_plan(6),
            reserve(3, 0),
            fixed_write(5, 1),
            &BitSet::default(),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
    }

    #[test]
    fn scratch_final_spills_use_designated_backend_reserve_slice() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1)]);
        let spills = FinalSpillObjects::compute(&alloc, &BitSet::default());
        let final_spills = alloc_final_spills(FinalSpillAllocationInput {
            func: FuncRef::from_u32(0),
            alloc,
            mem_plan: scratch_mem_plan(7),
            final_scratch_reserve: FinalScratchReserveRange {
                start_word: 3,
                words: 2,
            },
            reserve: reserve(2, 0),
            fixed_writes: Vec::new(),
            spills,
            optional_placement: OptionalFinalSpillPlacement::Scratch,
        })
        .expect("final spill allocation succeeds");

        assert_eq!(final_spills.required_reserve, reserve(2, 0));
        assert_eq!(final_spills.mem_plan.scratch_words, 7);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
    }

    #[test]
    fn mixed_final_spills_split_scratch_and_stable_reserves() {
        let alloc = alloc_with_object_spills(&[(10, 0), (11, 1), (12, 2)]);
        let final_spills = allocate_final_spills(
            alloc,
            static_mem_plan(5, 5),
            reserve(2, 1),
            &stable_values(&[12]),
            OptionalFinalSpillPlacement::Scratch,
        );

        assert_eq!(final_spills.required_reserve, reserve(2, 1));
        assert_eq!(final_spills.mem_plan.scratch_words, 5);
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(0)],
            ObjLoc::ScratchAbs(3)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(1)],
            ObjLoc::ScratchAbs(4)
        );
        assert_eq!(
            final_spills.mem_plan.obj_loc[&StackObjId::new(2)],
            ObjLoc::StableAbs(4)
        );
    }

    #[test]
    fn final_spill_validator_rejects_scratch_stable_absolute_alias() {
        let mut mem_plan = static_mem_plan(3, 5);
        let scratch_obj = StackObjId::new(0);
        let stable_obj = StackObjId::new(1);
        mem_plan.obj_loc.insert(scratch_obj, ObjLoc::ScratchAbs(3));
        mem_plan.obj_loc.insert(stable_obj, ObjLoc::StableAbs(0));

        let err = validate_final_spill_absolute_disjointness(
            FuncRef::from_u32(0),
            &mem_plan,
            &[scratch_obj, stable_obj],
        )
        .expect_err("overlap should be rejected");

        assert!(err.contains("absolute-memory overlap"));
    }

    #[test]
    fn final_spill_validator_rejects_scratch_fixed_write_overlap() {
        let mut mem_plan = scratch_mem_plan(5);
        let scratch_obj = StackObjId::new(0);
        mem_plan.obj_loc.insert(scratch_obj, ObjLoc::ScratchAbs(3));

        let err = validate_final_spills_disjoint_from_fixed_writes(
            FuncRef::from_u32(0),
            &mem_plan,
            &[scratch_obj],
            &fixed_write(3, 1),
        )
        .expect_err("fixed write overlap should be rejected");

        assert!(err.contains("fixed memory write overlap"));
    }

    #[test]
    fn final_spill_validator_rejects_stable_fixed_write_overlap() {
        let mut mem_plan = static_mem_plan(3, 7);
        let stable_obj = StackObjId::new(0);
        mem_plan.obj_loc.insert(stable_obj, ObjLoc::StableAbs(5));

        let err = validate_final_spills_disjoint_from_fixed_writes(
            FuncRef::from_u32(0),
            &mem_plan,
            &[stable_obj],
            &fixed_write(8, 1),
        )
        .expect_err("fixed write overlap should be rejected");

        assert!(err.contains("fixed memory write overlap"));
    }

    #[test]
    fn loop_carried_spill_objects_conflict_across_the_back_edge() {
        let parsed = parse_module(
            "target = \"evm-ethereum-osaka\"
            func private %f(v0.i1) {
                block0:
                    jump block1;
                block1:
                    br v0 block1 block2;
                block2:
                    return;
            }",
        )
        .unwrap();
        let mut cfg = ControlFlowGraph::default();
        let blocks: Vec<_> = parsed
            .module
            .func_store
            .view(parsed.module.funcs()[0], |function| {
                cfg.compute(function);
                function.layout.iter_block().collect()
            });
        let [a, b, c, d] = [0, 1, 2, 3].map(StackObjId::new);
        let load = SpillObjectAccess::Load;
        let store = |obj| SpillObjectAccess::Store { obj, kills: true };
        // `a` lives through the loop, `b` and `d` within one iteration, and `c`
        // is carried around the back edge, so `d`, stored after `c`, only
        // conflicts with it through the back edge.
        let mut accesses = SecondaryMap::new();
        accesses[blocks[0]] = vec![store(a), store(c)];
        accesses[blocks[1]] = vec![load(c), store(b), load(b), store(c), store(d), load(d)];
        accesses[blocks[2]] = vec![load(a)];

        let conflicts = spill_object_conflicts(&cfg, &accesses);
        let conflicts_of = |obj| conflicts[obj].iter().collect::<Vec<_>>();
        assert_eq!(conflicts_of(a), [b, c, d]);
        assert_eq!(conflicts_of(b), [a]);
        assert_eq!(conflicts_of(c), [a, d]);
        assert_eq!(conflicts_of(d), [a, c]);
    }
}
