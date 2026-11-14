//! Builds a section's `SectionLowering` from its prepared section and final
//! layout.

use sonatina_ir::{Module, ir_writer::ModuleWriter, module::FuncRef};

use super::{EvmPreparedSection, emit::FinalAlloc, memory_plan::StableMode, opcode::OpCode};
use crate::{
    machinst::{assemble::ObjectLayout, vcode::Label},
    object::lowering::{
        BlockLowering, CodeLabel, FrameLowering, FuncLowering, SectionLowering, SpillLocation,
        StableLowering, StackSlot,
    },
    stackalloc::{Action, SpillStorage, StackItem},
};

/// The text of `funcs` of `module`, without the module's objects, whose
/// directives name functions of other sections.
pub(crate) fn functions_text(module: &Module, funcs: &[FuncRef]) -> String {
    let mut module = module.clone_for_funcs(funcs);
    module.objects.clear();
    ModuleWriter::new(&module).dump_string()
}

/// The section's lowering, if its preparation kept what it is built from.
pub(crate) fn record_section_lowering(
    prepared: &EvmPreparedSection,
    layout: &ObjectLayout<OpCode>,
) -> Option<SectionLowering> {
    let lowering = prepared.lowering()?;
    let module = prepared.module();
    let name = |func: FuncRef| module.ctx.func_sig(func, |sig| sig.name().to_string());
    let code_label = |owner: &str, label: Label| match label {
        Label::Block(block) => CodeLabel::Block {
            func: owner.to_string(),
            block,
        },
        Label::Function(func) => CodeLabel::Func(name(func)),
        Label::SectionCodeUnit(unit) => {
            CodeLabel::Unit(layout.section_units()[&unit].name().to_string())
        }
        Label::Insn(_) => CodeLabel::Inst,
    };

    let mut redirects = Vec::new();
    let funcs =
        prepared
            .funcs()
            .iter()
            .map(|&func| {
                let func_name = name(func);
                let plan = prepared
                    .function_plan(func)
                    .expect("prepared section has a plan for each function");
                let func_layout = layout.func_layout(func);
                if let Some(func_layout) = func_layout {
                    redirects.extend(func_layout.vcode().redirects.iter().map(|&(old, new)| {
                        (code_label(&func_name, old), code_label(&func_name, new))
                    }));
                }
                let final_alloc = FinalAlloc::new(plan.alloc.clone(), plan.mem_plan.clone());
                module.func_store.view(func, |function| {
                    let sources = &lowering.source_blocks[&func];
                    let blocks = function
                        .layout
                        .iter_block()
                        .map(|block| {
                            let mut block_sources =
                                sources.get(&block).cloned().unwrap_or_default();
                            block_sources.sort_unstable();
                            BlockLowering {
                                block,
                                sources: block_sources,
                                offset: func_layout.and_then(|layout| layout.block_offset(block)),
                                alias: plan.block_aliases.get(&block).copied(),
                                entry_stack: plan.alloc.entry_stacks[block]
                                    .iter()
                                    .map(|item| match item {
                                        StackItem::Value(value) => function
                                            .dfg
                                            .value_imm(*value)
                                            .map_or(StackSlot::Value(*value), StackSlot::Imm),
                                        StackItem::FuncRetAddr => StackSlot::FuncReturn,
                                        StackItem::CallRetAddr => StackSlot::CallReturn,
                                    })
                                    .collect(),
                            }
                        })
                        .collect();
                    let object_location = |obj| match final_alloc
                        .action_load_for_loc(final_alloc.obj_loc_for_id(obj), 0)
                    {
                        Action::MemLoadAbs(addr) => SpillLocation::Memory(addr),
                        Action::MemLoadFrameSlot(slot) => SpillLocation::Frame(slot),
                        action => unreachable!("a load of a stack object is {action:?}"),
                    };
                    let mut spills: Vec<_> =
                        plan.alloc
                            .spill_storage
                            .iter()
                            .filter_map(|(value, storage)| {
                                let location = match (*storage)? {
                                    SpillStorage::Scratch(slot) => SpillLocation::Memory(slot * 32),
                                    SpillStorage::Object(obj) => object_location(obj),
                                    SpillStorage::Rematerialized => SpillLocation::Rematerialized,
                                };
                                Some((value, location))
                            })
                            .chain(
                                plan.mem_plan.spill_obj.iter().filter_map(|(value, obj)| {
                                    Some((value, object_location((*obj)?)))
                                }),
                            )
                            .collect();
                    spills.sort_unstable_by_key(|(value, _)| value.as_u32());
                    spills.dedup();
                    FuncLowering {
                        name: func_name.clone(),
                        offset: func_layout.map(|layout| layout.offset()),
                        blocks,
                        spills,
                        frame: FrameLowering {
                            stable: match plan.mem_plan.stable_mode {
                                StableMode::None => StableLowering::None,
                                StableMode::StableAbs { base_word } => {
                                    StableLowering::Abs { base_word }
                                }
                                StableMode::DynamicFrame => StableLowering::DynamicFrame,
                            },
                            scratch_words: plan.mem_plan.scratch_words,
                            stable_words: plan.mem_plan.stable_words,
                        },
                        mallocs: lowering.mallocs[&func].clone(),
                    }
                })
            })
            .collect();

    let units = layout
        .section_units()
        .values()
        .map(|unit| {
            for &(old, new) in &unit.layout().vcode().redirects {
                redirects.push((code_label(unit.name(), old), code_label(unit.name(), new)));
            }
            let unit_layout = unit.layout();
            (
                unit.name().to_string(),
                unit_layout.offset(),
                unit_layout.end() - unit_layout.offset(),
            )
        })
        .collect();

    Some(SectionLowering {
        source_ir: lowering.source_ir.clone(),
        machine_ir: functions_text(module, prepared.funcs()),
        code_size: layout.code_end(),
        arena_base: prepared.section_plan().arena_base,
        dyn_base: prepared.section_plan().dyn_base,
        entry_free_ptr: lowering.entry_free_ptr,
        funcs,
        units,
        redirects,
    })
}
