use sonatina_ir::{BlockId, Function, I256, Immediate, InstId};

use crate::stackalloc::{Action, Actions, Allocator, StackifyAlloc};

use super::super::{
    DynamicFrameLayout, FuncMemPlan, ObjLoc, PreserveMode, static_arena_alloc::StackObjId,
};

pub(crate) struct FinalAlloc {
    inner: StackifyAlloc,
    pub(crate) mem_plan: FuncMemPlan,
}

impl FinalAlloc {
    pub(crate) fn new(inner: StackifyAlloc, mem_plan: FuncMemPlan) -> Self {
        Self { inner, mem_plan }
    }

    fn abs_addr_for_word(&self, word_off: u32) -> u32 {
        self.mem_plan.abs_addr_for_word(word_off)
    }

    pub(crate) fn obj_loc_for_id(&self, id: StackObjId) -> ObjLoc {
        self.mem_plan
            .obj_loc
            .get(&id)
            .copied()
            .unwrap_or_else(|| panic!("missing stack object location for obj {}", id.as_u32()))
    }

    fn dynamic_frame_layout(&self) -> DynamicFrameLayout {
        self.mem_plan
            .dynamic_frame_layout()
            .expect("frame location requires an addressable dynamic frame layout")
    }

    fn frame_action_offset(&self, offset_words: u32, extra_words: u32, kind: &str) -> u32 {
        let offset_words = offset_words
            .checked_add(extra_words)
            .unwrap_or_else(|| panic!("frame {kind} offset overflow"));
        self.dynamic_frame_layout()
            .expect_local_word(offset_words, kind)
            .as_u32()
    }

    fn action_for_loc(
        &self,
        loc: ObjLoc,
        extra_words: u32,
        kind: &str,
        abs: fn(u32) -> Action,
        frame: fn(u32) -> Action,
    ) -> Action {
        match loc {
            ObjLoc::ScratchAbs(off) => abs(self.abs_addr_for_word(
                off.checked_add(extra_words)
                    .unwrap_or_else(|| panic!("scratch {kind} offset overflow")),
            )),
            ObjLoc::StableAbs(off) => {
                let base_word = self
                    .mem_plan
                    .stable_base_word()
                    .expect("stable abs object missing stable base");
                abs(self.abs_addr_for_word(
                    base_word
                        .checked_add(off)
                        .and_then(|w| w.checked_add(extra_words))
                        .unwrap_or_else(|| panic!("stable {kind} offset overflow")),
                ))
            }
            ObjLoc::StableFrame(off) => frame(self.frame_action_offset(off, extra_words, kind)),
            ObjLoc::StackPinned(depth) => {
                panic!("stack-pinned objects are not supported in EVM lowering (depth={depth})")
            }
        }
    }

    pub(crate) fn action_load_for_loc(&self, loc: ObjLoc, extra_words: u32) -> Action {
        self.action_for_loc(
            loc,
            extra_words,
            "load",
            Action::MemLoadAbs,
            Action::MemLoadFrameSlot,
        )
    }

    pub(crate) fn action_store_for_loc(&self, loc: ObjLoc, extra_words: u32) -> Action {
        self.action_for_loc(
            loc,
            extra_words,
            "store",
            Action::MemStoreAbs,
            Action::MemStoreFrameSlot,
        )
    }

    fn action_for_exact_local_addr(&self, alloca: InstId, offset_bytes: i64) -> Action {
        let loc = self
            .mem_plan
            .alloca_loc
            .get(&alloca)
            .copied()
            .unwrap_or_else(|| {
                panic!(
                    "missing alloca location for exact local addr inst {}",
                    alloca.as_u32()
                )
            });
        match loc {
            ObjLoc::ScratchAbs(off) => {
                let base = i64::from(self.abs_addr_for_word(off));
                let addr = base
                    .checked_add(offset_bytes)
                    .unwrap_or_else(|| panic!("scratch exact local addr overflow"));
                Action::Push(Immediate::I256(I256::from(addr)))
            }
            ObjLoc::StableAbs(off) => {
                let base_word = self
                    .mem_plan
                    .stable_base_word()
                    .expect("stable abs alloca missing stable base");
                let base = i64::from(
                    self.abs_addr_for_word(
                        base_word
                            .checked_add(off)
                            .expect("stable exact local word overflow"),
                    ),
                );
                let addr = base
                    .checked_add(offset_bytes)
                    .unwrap_or_else(|| panic!("stable exact local addr overflow"));
                Action::Push(Immediate::I256(I256::from(addr)))
            }
            ObjLoc::StableFrame(off) => Action::PushFrameAddr {
                offset_words: self.frame_action_offset(off, 0, "exact local addr"),
                extra_bytes: offset_bytes,
            },
            ObjLoc::StackPinned(depth) => {
                panic!("stack-pinned exact local addresses are not supported (depth={depth})")
            }
        }
    }

    fn inject_call_save_pre(
        &self,
        inst: InstId,
        _operand_count: usize,
        actions: Actions,
    ) -> Actions {
        let Some(plan) = self.mem_plan.call_preserve.get(&inst) else {
            return actions;
        };
        let PreserveMode::ShadowRuns { shadow_obj, runs } = &plan.mode else {
            return actions;
        };
        if runs.is_empty() {
            return actions;
        }

        let Some(cont_pos) = actions
            .iter()
            .position(|a| matches!(a, Action::PushContinuationOffset))
        else {
            panic!("call save expected Action::PushContinuationOffset");
        };
        let shadow_loc = self.obj_loc_for_id(*shadow_obj);

        let mut out = Actions::new();
        for (idx, act) in actions.into_iter().enumerate() {
            if idx == cont_pos {
                for run in runs {
                    for word in 0..run.len_words {
                        out.push(
                            self.action_load_for_loc(
                                ObjLoc::ScratchAbs(run.scratch_src_word),
                                word,
                            ),
                        );
                        out.push(
                            self.action_store_for_loc(
                                shadow_loc,
                                run.shadow_dst_word
                                    .checked_add(word)
                                    .expect("shadow save offset overflow"),
                            ),
                        );
                    }
                }
            }
            out.push(act);
        }
        out
    }

    fn inject_call_save_post(&self, inst: InstId, actions: Actions) -> Actions {
        let Some(plan) = self.mem_plan.call_preserve.get(&inst) else {
            return actions;
        };
        let PreserveMode::ShadowRuns { shadow_obj, runs } = &plan.mode else {
            return actions;
        };
        if runs.is_empty() {
            return actions;
        }

        let mut restore = Actions::new();
        let shadow_loc = self.obj_loc_for_id(*shadow_obj);
        for run in runs.iter().rev() {
            for word in (0..run.len_words).rev() {
                restore.push(
                    self.action_load_for_loc(
                        shadow_loc,
                        run.shadow_dst_word
                            .checked_add(word)
                            .expect("shadow restore offset overflow"),
                    ),
                );
                restore.push(
                    self.action_store_for_loc(ObjLoc::ScratchAbs(run.scratch_src_word), word),
                );
            }
        }

        let mut out = Actions::new();
        out.extend(actions);
        out.extend(restore);
        out
    }

    fn rewrite_actions(&self, mut actions: Actions) -> Actions {
        for action in actions.iter_mut() {
            match action {
                Action::MemLoadObj(id) => {
                    *action = self.action_load_for_loc(self.obj_loc_for_id(*id), 0);
                }
                Action::MemStoreObj(id) => {
                    *action = self.action_store_for_loc(self.obj_loc_for_id(*id), 0);
                }
                Action::MaterializeLocalAddr {
                    alloca,
                    offset_bytes,
                } => {
                    *action = self.action_for_exact_local_addr(*alloca, *offset_bytes);
                }
                _ => {}
            }
        }

        actions
    }
}

impl Allocator for FinalAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        self.rewrite_actions(self.inner.enter_function(function))
    }

    fn read(&self, inst: InstId, vals: &[sonatina_ir::ValueId]) -> Actions {
        let actions = self.inner.read(inst, vals);
        let actions = self.inject_call_save_pre(inst, vals.len(), actions);
        self.rewrite_actions(actions)
    }

    fn read_br_table_case(&self, inst: InstId, case_index: usize) -> Actions {
        self.rewrite_actions(self.inner.read_br_table_case(inst, case_index))
    }

    fn write(&self, inst: InstId, vals: &[sonatina_ir::ValueId]) -> Actions {
        let actions = self.inner.write(inst, vals);
        let actions = self.inject_call_save_post(inst, actions);
        self.rewrite_actions(actions)
    }

    fn traverse_edge(&self, from: BlockId, to: BlockId) -> Actions {
        self.rewrite_actions(self.inner.traverse_edge(from, to))
    }
}

#[cfg(test)]
mod tests {
    use cranelift_entity::SecondaryMap;
    use rustc_hash::{FxHashMap, FxHashSet};
    use sonatina_ir::InstId;

    use super::{FinalAlloc, StackifyAlloc};
    use crate::{
        isa::evm::{FuncMemPlan, ObjLoc, STATIC_BASE, memory_plan::StableMode},
        stackalloc::Action,
    };

    fn mem_plan_with_alloca(alloca: InstId, loc: ObjLoc, stable_words: u32) -> FuncMemPlan {
        let mut alloca_loc = FxHashMap::default();
        alloca_loc.insert(alloca, loc);
        FuncMemPlan {
            arena_base: STATIC_BASE,
            scratch_words: 0,
            stable_words,
            stable_mode: StableMode::DynamicFrame,
            entry_abs_words: 0,
            obj_loc: FxHashMap::default(),
            alloca_loc,
            spill_obj: SecondaryMap::new(),
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words: FxHashMap::default(),
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds: FxHashMap::default(),
            return_escape_caller_abs_words: 0,
        }
    }

    #[test]
    fn exact_local_addr_uses_dynamic_frame_local_offsets() {
        let alloca = InstId::from_u32(7);
        let alloc = FinalAlloc::new(
            StackifyAlloc::default(),
            mem_plan_with_alloca(alloca, ObjLoc::StableFrame(1), 3),
        );

        assert_eq!(
            alloc.action_for_exact_local_addr(alloca, 64),
            Action::PushFrameAddr {
                offset_words: 1,
                extra_bytes: 64,
            }
        );
    }
}
