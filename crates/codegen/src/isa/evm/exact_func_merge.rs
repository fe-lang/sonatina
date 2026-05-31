use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    InstDowncast, Module,
    inst::data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
    module::FuncRef,
};

use crate::machinst::{
    lower::LoweredFunction,
    vcode::{Label, VCode, VCodeFixup, VCodeInst},
};

use super::OpCode;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FuncBodyKey(Vec<FuncBodyKeyItem>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FuncBodyKeyItem {
    Block,
    Inst {
        op: u8,
        imm: Option<Vec<u8>>,
        fixup: Option<FuncBodyFixupKey>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FuncBodyFixupKey {
    Block(u32),
    Insn(u32),
    Function(u32),
    SectionCodeUnit(u32),
}

pub(crate) fn run_exact_private_func_merge(
    module: &Module,
    lowered: &mut Vec<(FuncRef, LoweredFunction<OpCode>)>,
) -> usize {
    let observed = collect_observed_func_symbols(module);
    let mut aliases = FxHashMap::default();
    let mut changed = true;

    while changed {
        changed = false;
        let mut keys = FxHashMap::default();

        for (func, lowered_func) in lowered.iter() {
            if aliases.contains_key(func) || !is_mergeable_func(module, &observed, *func) {
                continue;
            }

            let Some(key) = func_body_key(*func, lowered_func, &aliases) else {
                continue;
            };

            if let Some(canonical) = keys.get(&key).copied() {
                aliases.insert(*func, canonical_func(canonical, &aliases));
                changed = true;
            } else {
                keys.insert(key, canonical_func(*func, &aliases));
            }
        }
    }

    if aliases.is_empty() {
        return 0;
    }

    rewrite_function_labels(lowered, &aliases);

    let original_len = lowered.len();
    lowered.retain(|(func, _)| !aliases.contains_key(func));
    original_len - lowered.len()
}

fn is_mergeable_func(module: &Module, observed: &FxHashSet<FuncRef>, func: FuncRef) -> bool {
    module.ctx.func_linkage(func).is_private() && !observed.contains(&func)
}

fn collect_observed_func_symbols(module: &Module) -> FxHashSet<FuncRef> {
    let mut observed = FxHashSet::default();

    for func_ref in module.funcs() {
        if !module.ctx.func_linkage(func_ref).has_definition() {
            continue;
        }

        module.func_store.view(func_ref, |func| {
            let is = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    let inst = func.dfg.inst(inst_id);
                    if let Some(ptr) = <&GetFunctionPtr as InstDowncast>::downcast(is, inst) {
                        observed.insert(*ptr.func());
                    }
                    if let Some(sym) = <&SymAddr as InstDowncast>::downcast(is, inst)
                        && let SymbolRef::Func(func_ref) = sym.sym()
                    {
                        observed.insert(*func_ref);
                    }
                    if let Some(sym) = <&SymSize as InstDowncast>::downcast(is, inst)
                        && let SymbolRef::Func(func_ref) = sym.sym()
                    {
                        observed.insert(*func_ref);
                    }
                }
            }
        });
    }

    observed
}

fn func_body_key(
    func: FuncRef,
    lowered: &LoweredFunction<OpCode>,
    aliases: &FxHashMap<FuncRef, FuncRef>,
) -> Option<FuncBodyKey> {
    let (block_indexes, inst_indexes) = collect_indexes(&lowered.vcode, &lowered.block_order);
    let mut items = Vec::new();

    for &block in &lowered.block_order {
        items.push(FuncBodyKeyItem::Block);
        for inst in lowered.vcode.block_insns(block) {
            let imm = lowered
                .vcode
                .inst_imm_bytes
                .get(inst)
                .map(|(_, bytes)| bytes.to_vec());
            let fixup = if let Some((_, fixup)) = lowered.vcode.fixups.get(inst) {
                Some(func_body_fixup_key(
                    func,
                    &lowered.vcode,
                    fixup,
                    &block_indexes,
                    &inst_indexes,
                    aliases,
                )?)
            } else {
                None
            };

            items.push(FuncBodyKeyItem::Inst {
                op: lowered.vcode.insts[inst] as u8,
                imm,
                fixup,
            });
        }
    }

    Some(FuncBodyKey(items))
}

fn collect_indexes(
    vcode: &VCode<OpCode>,
    block_order: &[sonatina_ir::BlockId],
) -> (
    FxHashMap<sonatina_ir::BlockId, u32>,
    FxHashMap<VCodeInst, u32>,
) {
    let mut block_indexes = FxHashMap::default();
    let mut inst_indexes = FxHashMap::default();
    let mut inst_index = 0u32;

    for (block_index, &block) in block_order.iter().enumerate() {
        block_indexes.insert(block, block_index as u32);
        for inst in vcode.block_insns(block) {
            inst_indexes.insert(inst, inst_index);
            inst_index += 1;
        }
    }

    (block_indexes, inst_indexes)
}

fn func_body_fixup_key(
    func: FuncRef,
    vcode: &VCode<OpCode>,
    fixup: &VCodeFixup,
    block_indexes: &FxHashMap<sonatina_ir::BlockId, u32>,
    inst_indexes: &FxHashMap<VCodeInst, u32>,
    aliases: &FxHashMap<FuncRef, FuncRef>,
) -> Option<FuncBodyFixupKey> {
    let VCodeFixup::Label(label) = fixup else {
        return None;
    };

    match vcode.labels[*label] {
        Label::Block(block) => block_indexes
            .get(&block)
            .copied()
            .map(FuncBodyFixupKey::Block),
        Label::Insn(inst) => inst_indexes.get(&inst).copied().map(FuncBodyFixupKey::Insn),
        Label::Function(target) => {
            let canonical = canonical_func(target, aliases);
            if canonical == func {
                return None;
            }
            Some(FuncBodyFixupKey::Function(canonical.as_u32()))
        }
        Label::SectionCodeUnit(unit) => Some(FuncBodyFixupKey::SectionCodeUnit(unit.0)),
    }
}

fn canonical_func(func: FuncRef, aliases: &FxHashMap<FuncRef, FuncRef>) -> FuncRef {
    let mut current = func;
    while let Some(&next) = aliases.get(&current) {
        if next == current {
            break;
        }
        current = next;
    }
    current
}

fn rewrite_function_labels(
    lowered: &mut [(FuncRef, LoweredFunction<OpCode>)],
    aliases: &FxHashMap<FuncRef, FuncRef>,
) {
    for (_, lowered_func) in lowered {
        for label in lowered_func.vcode.labels.keys().collect::<Vec<_>>() {
            let Label::Function(func) = lowered_func.vcode.labels[label] else {
                continue;
            };
            let canonical = canonical_func(func, aliases);
            if canonical != func {
                lowered_func.vcode.labels[label] = Label::Function(canonical);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;
    use sonatina_ir::{
        Linkage, Signature, builder::ModuleBuilder, isa::evm::Evm, module::ModuleCtx,
    };
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use crate::machinst::vcode::VCode;

    use super::*;

    fn test_module_builder() -> ModuleBuilder {
        ModuleBuilder::new(ModuleCtx::new(&Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        })))
    }

    fn lowered_push_stop(value: u8) -> LoweredFunction<OpCode> {
        let block = sonatina_ir::BlockId(0);
        let mut vcode = VCode::default();
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode.inst_imm_bytes.insert((push, smallvec![value]));
        vcode.add_inst_to_block(OpCode::STOP, None, block);
        LoweredFunction {
            vcode,
            block_order: vec![block],
        }
    }

    #[test]
    fn exact_private_func_merge_rewrites_call_targets_and_drops_duplicate() {
        let builder = test_module_builder();
        let entry = builder
            .declare_function(Signature::new_unit("entry", Linkage::Public, &[]))
            .unwrap();
        let helper_a = builder
            .declare_function(Signature::new_unit("helper_a", Linkage::Private, &[]))
            .unwrap();
        let helper_b = builder
            .declare_function(Signature::new_unit("helper_b", Linkage::Private, &[]))
            .unwrap();
        let module = builder.build();

        let block = sonatina_ir::BlockId(0);
        let mut entry_vcode = VCode::default();
        let push = entry_vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        let label = entry_vcode.labels.push(Label::Function(helper_b));
        entry_vcode.fixups.insert((push, VCodeFixup::Label(label)));
        entry_vcode.add_inst_to_block(OpCode::JUMP, None, block);

        let mut lowered = vec![
            (
                entry,
                LoweredFunction {
                    vcode: entry_vcode,
                    block_order: vec![block],
                },
            ),
            (helper_a, lowered_push_stop(7)),
            (helper_b, lowered_push_stop(7)),
        ];

        assert_eq!(run_exact_private_func_merge(&module, &mut lowered), 1);
        assert_eq!(lowered.len(), 2);
        assert!(lowered.iter().any(|(func, _)| *func == helper_a));
        assert!(!lowered.iter().any(|(func, _)| *func == helper_b));

        let entry_vcode = &lowered[0].1.vcode;
        let Some((_, VCodeFixup::Label(label))) = entry_vcode.fixups.get(push) else {
            panic!("entry call should still use a function label");
        };
        assert_eq!(entry_vcode.labels[*label], Label::Function(helper_a));
    }
}
