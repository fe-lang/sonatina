use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::ModuleCtx,
};
use sonatina_triple::{EvmVersion, OperatingSystem};
use tracing::debug_span;

use crate::machinst::{
    lower::{FixupUpdate, LoweredFunction, SectionCodeUnit, SectionWorkModule},
    vcode::{SymFixup, VCode, VCodeInst},
};

use super::{
    STATIC_BASE,
    emit::{EvmFunctionLowering, push_op},
    late_alias::compute_evm_late_aliases,
    late_section_merge::run_late_section_terminal_outline,
    memory_plan::{ArenaCostModel, ObjLoc, PreserveMode, StableMode, WORD_BYTES},
    opcode::OpCode,
    prepare::{self, EvmPreparedSection},
};
use cranelift_entity::SecondaryMap;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum PushWidthPolicy {
    /// Resolve symbol fixups as fixed-width 32-bit immediates.
    Push4,
    /// Resolve symbol fixups to the shortest valid EVM PUSH encoding.
    #[default]
    MinimalRelax,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LateCleanupProfile {
    Off,
    Speed,
    Size,
}

pub struct EvmBackend {
    pub(crate) isa: Evm,
    pub(crate) stackify_reach_depth: u8,
    pub(crate) arena_cost_model: ArenaCostModel,
    pub(crate) late_cleanup_profile: LateCleanupProfile,
}

impl EvmBackend {
    pub fn new(isa: Evm) -> Self {
        let triple = isa.triple();
        assert!(
            matches!(
                triple.operating_system,
                OperatingSystem::Evm(EvmVersion::Osaka)
            ),
            "EvmBackend requires evm-ethereum-osaka (got {triple})"
        );
        Self {
            isa,
            stackify_reach_depth: 16,
            arena_cost_model: ArenaCostModel::default(),
            late_cleanup_profile: LateCleanupProfile::Speed,
        }
    }

    pub fn with_stackify_reach_depth(mut self, reach_depth: u8) -> Self {
        assert!(
            (1..=16).contains(&reach_depth),
            "stackify reach_depth must be in 1..=16"
        );
        self.stackify_reach_depth = reach_depth;
        self
    }

    pub fn with_late_cleanup_profile(mut self, profile: LateCleanupProfile) -> Self {
        self.late_cleanup_profile = profile;
        self
    }

    pub fn with_late_cleanup_optimizations(mut self, enable: bool) -> Self {
        self.late_cleanup_profile = if enable {
            LateCleanupProfile::Speed
        } else {
            LateCleanupProfile::Off
        };
        self
    }

    pub fn stackify_reach_depth(&self) -> u8 {
        self.stackify_reach_depth
    }

    pub fn compute_stackify_value_aliases(
        &self,
        function: &Function,
        module: &ModuleCtx,
    ) -> SecondaryMap<ValueId, Option<ValueId>> {
        compute_evm_late_aliases(function, module, &self.isa)
            .map()
            .clone()
    }

    pub fn with_arena_cost_model(mut self, model: ArenaCostModel) -> Self {
        self.arena_cost_model = model;
        self
    }

    /// Render a deterministic memory-plan summary for snapshot tests.
    ///
    /// This intentionally includes alloca layout (offset/size + computed address),
    /// so snapshots can assert that alloca reuse is correct across loops/branches.
    pub fn snapshot_mem_plan(&self, prepared: &EvmPreparedSection) -> String {
        self.snapshot_mem_plan_impl(prepared, false)
    }

    pub fn snapshot_mem_plan_detail(&self, prepared: &EvmPreparedSection) -> String {
        self.snapshot_mem_plan_impl(prepared, true)
    }

    fn snapshot_mem_plan_impl(&self, prepared: &EvmPreparedSection, detail: bool) -> String {
        use std::fmt::Write as _;

        let module = prepared.module();
        let funcs = prepared.funcs();
        let mut out = String::new();
        writeln!(
            &mut out,
            "evm mem plan: global_dyn_base=0x{:x} static_base=0x{:x} scratch_peak_words={} static_chain_peak_words={}",
            prepared.section_plan().dyn_base,
            STATIC_BASE,
            prepared.section_plan().scratch_peak_words,
            prepared.section_plan().static_chain_peak_words
        )
        .expect("mem plan write failed");

        for &func in funcs {
            let Some(func_plan) = prepared.function_plan(func).map(|plan| &plan.mem_plan) else {
                continue;
            };

            let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
            let stable = match func_plan.stable_mode {
                StableMode::None => "None".to_string(),
                StableMode::DynamicFrame => "DynamicFrame".to_string(),
                StableMode::StaticAbs { base_word } => {
                    format!(
                        "StaticAbs(base=0x{:x})",
                        STATIC_BASE + (base_word * WORD_BYTES)
                    )
                }
            };
            writeln!(
                &mut out,
                "evm mem plan: {name} scratch_words={} stable_words={} stable_mode={} entry_abs_words={} abs_words_end={}",
                func_plan.scratch_words,
                func_plan.stable_words,
                stable,
                func_plan.entry_abs_words,
                func_plan.abs_words_end(),
            )
            .expect("mem plan write failed");

            let addr_of = |loc: ObjLoc| match loc {
                ObjLoc::ScratchAbs(off) => {
                    let addr_bytes = STATIC_BASE
                        .checked_add(off.checked_mul(WORD_BYTES).expect("address bytes overflow"))
                        .expect("address bytes overflow");
                    format!("0x{addr_bytes:x}")
                }
                ObjLoc::StableAbs(off) => {
                    let base_word = func_plan
                        .stable_base_word()
                        .expect("stable abs object missing stable base");
                    let addr_bytes = STATIC_BASE
                        .checked_add(
                            base_word
                                .checked_add(off)
                                .expect("address words overflow")
                                .checked_mul(WORD_BYTES)
                                .expect("address bytes overflow"),
                        )
                        .expect("address bytes overflow");
                    format!("0x{addr_bytes:x}")
                }
                ObjLoc::StableFrame(off) => {
                    let frame_layout = func_plan
                        .dynamic_frame_layout()
                        .expect("stable frame object missing dynamic frame layout");
                    let addr_bytes = frame_layout
                        .sp_relative_bytes(frame_layout.expect_local_word(off, "debug object"));
                    format!("sp-0x{addr_bytes:x}")
                }
                ObjLoc::StackPinned(depth) => format!("stack[{depth}]"),
            };

            if detail {
                let mut call_info: FxHashMap<InstId, super::FuncRef> = FxHashMap::default();
                module.func_store.view(func, |function| {
                    for block in function.layout.iter_block() {
                        for inst in function.layout.iter_inst(block) {
                            let Some(call) = function.dfg.call_info(inst) else {
                                continue;
                            };
                            call_info.insert(inst, call.callee());
                        }
                    }
                });

                let mut call_preserve: Vec<(InstId, &super::memory_plan::CallPreservePlan)> =
                    func_plan
                        .call_preserve
                        .iter()
                        .map(|(inst, plan)| (*inst, plan))
                        .collect();
                call_preserve.sort_unstable_by_key(|(inst, _)| inst.as_u32());
                for (inst, plan) in call_preserve {
                    let callee = call_info.get(&inst).copied().unwrap_or_else(|| {
                        panic!(
                            "missing call info for preserve plan at inst {}",
                            inst.as_u32()
                        )
                    });
                    let callee_name = module.ctx.func_sig(callee, |sig| sig.name().to_string());
                    match &plan.mode {
                        PreserveMode::None => {}
                        PreserveMode::ShadowRuns { shadow_obj, runs } => {
                            let save_words: u32 = runs.iter().map(|run| run.len_words).sum();
                            writeln!(
                                &mut out,
                                "  call inst{} callee=%{callee_name} preserve=ShadowRuns shadow_obj={} result_count={} save_words={} runs={runs:?}",
                                inst.as_u32(),
                                shadow_obj.as_u32(),
                                plan.result_count,
                                save_words,
                            )
                            .expect("mem plan write failed");
                        }
                        PreserveMode::TinyStackLift { word_offsets } => {
                            writeln!(
                                &mut out,
                                "  call inst{} callee=%{callee_name} preserve=TinyStackLift result_count={} save_words={} save_offsets={word_offsets:?}",
                                inst.as_u32(),
                                plan.result_count,
                                word_offsets.len(),
                            )
                            .expect("mem plan write failed");
                        }
                    }
                }

                let mut scratch_spills: Vec<(ValueId, u32)> = Vec::new();
                if let Some(alloc) = prepared.function_plan(func).map(|plan| &plan.alloc) {
                    module.func_store.view(func, |function| {
                        for v in function.dfg.value_ids() {
                            let Some(slot) = alloc.scratch_slot_of_value[v] else {
                                continue;
                            };
                            scratch_spills.push((v, slot));
                        }
                    });
                }

                scratch_spills.sort_unstable_by_key(|(v, _)| v.as_u32());
                for (v, slot) in scratch_spills {
                    let addr_bytes = slot
                        .checked_mul(WORD_BYTES)
                        .expect("scratch slot addr overflow");
                    writeln!(
                        &mut out,
                        "  scratch_spill v{} slot={slot} addr=0x{addr_bytes:x}",
                        v.as_u32()
                    )
                    .expect("mem plan write failed");
                }

                let mut spills: Vec<(ValueId, u32, String)> = Vec::new();
                module.func_store.view(func, |function| {
                    for v in function.dfg.value_ids() {
                        let Some(obj) = func_plan.spill_obj[v] else {
                            continue;
                        };
                        let loc = func_plan
                            .obj_loc
                            .get(&obj)
                            .copied()
                            .expect("missing stack object location");
                        let offset_words = func_plan
                            .obj_word_offset(obj)
                            .expect("missing stack object offset");
                        spills.push((v, offset_words, addr_of(loc)));
                    }
                });

                spills.sort_unstable_by_key(|(v, _, _)| v.as_u32());
                for (v, offset_words, addr) in spills {
                    writeln!(
                        &mut out,
                        "  spill v{} offset_words={offset_words} addr={addr}",
                        v.as_u32()
                    )
                    .expect("mem plan write failed");
                }
            }

            let mut allocas: Vec<(ValueId, u32, u32, String)> = Vec::new();
            module.func_store.view(func, |function| {
                for block in function.layout.iter_block() {
                    for insn in function.layout.iter_inst(block) {
                        let data = self.isa.inst_set().resolve_inst(function.dfg.inst(insn));
                        let EvmInstKind::Alloca(alloca) = data else {
                            continue;
                        };
                        let Some(value) = function.dfg.inst_result(insn) else {
                            continue;
                        };
                        let loc = func_plan
                            .alloca_loc
                            .get(&insn)
                            .copied()
                            .expect("missing alloca plan");
                        let offset_words = match loc {
                            ObjLoc::ScratchAbs(off)
                            | ObjLoc::StableAbs(off)
                            | ObjLoc::StableFrame(off) => off,
                            ObjLoc::StackPinned(depth) => u32::from(depth),
                        };

                        let size_bytes = self
                            .isa
                            .type_layout()
                            .size_of(*alloca.ty(), &module.ctx)
                            .expect("alloca has invalid type")
                            as u32;
                        let size_words = size_bytes.div_ceil(WORD_BYTES);
                        allocas.push((value, offset_words, size_words, addr_of(loc)));
                    }
                }
            });

            if allocas.is_empty() {
                continue;
            }

            allocas.sort_unstable_by_key(|(v, _, _, _)| v.as_u32());
            for (value, offset_words, size_words, addr) in allocas {
                writeln!(
                    &mut out,
                    "  alloca v{} offset_words={offset_words} size_words={size_words} addr={addr}",
                    value.as_u32()
                )
                .expect("mem plan write failed");
            }
        }

        out
    }

    pub fn prepare_section(&self, work: SectionWorkModule) -> Result<EvmPreparedSection, String> {
        prepare::prepare_section(self, work)
    }

    pub fn lower_function(
        &self,
        prepared: &EvmPreparedSection,
        func: super::FuncRef,
    ) -> Result<LoweredFunction<OpCode>, String> {
        let _span = debug_span!(
            "sonatina.codegen.evm.lower_function",
            func_ref = func.as_u32()
        )
        .entered();
        let function_plan = prepared
            .function_plan(func)
            .ok_or_else(|| format!("missing prepared lowering for func {}", func.as_u32()))?;
        EvmFunctionLowering::new(self, prepared.section_plan(), function_plan)
            .lower_prepared_function(prepared.module(), func)
    }

    pub fn post_lower_section(
        &self,
        prepared: &EvmPreparedSection,
        lowered: &mut [(super::FuncRef, LoweredFunction<OpCode>)],
    ) -> Result<Vec<SectionCodeUnit<OpCode>>, String> {
        if self.late_cleanup_profile == LateCleanupProfile::Off {
            return Ok(Vec::new());
        }
        Ok(run_late_section_terminal_outline(
            prepared.module(),
            lowered,
        ))
    }

    pub fn apply_sym_fixup(
        &self,
        vcode: &mut VCode<OpCode>,
        inst: VCodeInst,
        fixup: &SymFixup,
        value: u32,
        policy: &PushWidthPolicy,
    ) -> Result<FixupUpdate, String> {
        let _ = fixup;
        let (_, bytes) = vcode
            .inst_imm_bytes
            .get_mut(inst)
            .ok_or_else(|| "missing fixup immediate bytes".to_string())?;

        let new_bytes = u32_to_evm_push_bytes(value, *policy);
        if bytes.as_slice() == new_bytes.as_slice() {
            return Ok(FixupUpdate::Unchanged);
        }

        let layout_changed = bytes.len() != new_bytes.len();
        bytes.clear();
        bytes.extend_from_slice(&new_bytes);
        self.update_opcode_with_immediate_bytes(&mut vcode.insts[inst], bytes);

        Ok(if layout_changed {
            FixupUpdate::LayoutChanged
        } else {
            FixupUpdate::ContentChanged
        })
    }

    pub(crate) fn update_opcode_with_immediate_bytes(
        &self,
        opcode: &mut OpCode,
        bytes: &mut SmallVec<[u8; 8]>,
    ) {
        debug_assert!(
            bytes.len() <= 32,
            "PUSH immediate too wide: {} bytes",
            bytes.len()
        );
        *opcode = push_op(bytes.len());
    }

    pub(crate) fn update_opcode_with_label(
        &self,
        opcode: &mut OpCode,
        label_offset: u32,
    ) -> SmallVec<[u8; 4]> {
        let bytes = label_offset
            .to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect::<SmallVec<_>>();
        *opcode = push_op(bytes.len());
        bytes
    }

    pub(crate) fn emit_opcode(&self, opcode: &OpCode, buf: &mut Vec<u8>) {
        buf.push(*opcode as u8);
    }

    pub(crate) fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
        buf.extend_from_slice(bytes);
    }

    pub(crate) fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
        buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
    }
}

fn u32_to_evm_push_bytes(value: u32, policy: PushWidthPolicy) -> SmallVec<[u8; 4]> {
    match policy {
        PushWidthPolicy::Push4 => SmallVec::from_slice(&value.to_be_bytes()),
        PushWidthPolicy::MinimalRelax => {
            if value == 0 {
                SmallVec::new()
            } else {
                value
                    .to_be_bytes()
                    .into_iter()
                    .skip_while(|b| *b == 0)
                    .collect()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PushWidthPolicy;

    #[test]
    fn default_push_width_policy_is_minimal_relax() {
        assert_eq!(PushWidthPolicy::default(), PushWidthPolicy::MinimalRelax);
    }
}
