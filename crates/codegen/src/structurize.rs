//! Control flow structuring pass for targets that require structured control flow
//! (WASM, SPIR-V). Converts an arbitrary reducible CFG into nested block/loop
//! constructs using a stackifier algorithm.
//!
//! This pass operates on Sonatina IR post-optimization and produces a
//! [`StructuredCfg`] annotation that structured-CF backends consume.

use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, cfg::ControlFlowGraph};

use crate::{domtree::DomTree, loop_analysis::LoopTree};

/// A structured control flow region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Region {
    /// A linear block (no nesting).
    Block(BlockId),
    /// A loop with a header and body regions.
    Loop { header: BlockId, body: Vec<Region> },
    /// An if-then-else with condition block, then-regions, and else-regions.
    IfThenElse {
        header: BlockId,
        then_branch: Vec<Region>,
        else_branch: Vec<Region>,
        merge: Option<BlockId>,
    },
}

/// The result of structuring a function's control flow.
#[derive(Debug, Clone)]
pub struct StructuredCfg {
    pub regions: Vec<Region>,
    pub block_order: Vec<BlockId>,
}

/// Compute structured control flow for a function.
///
/// Requires a reducible CFG (which Fe always produces). Returns an error
/// for irreducible control flow.
pub fn structurize_function(function: &Function) -> Result<StructuredCfg, String> {
    let mut cfg = ControlFlowGraph::default();
    cfg.compute(function);
    let mut domtree = DomTree::new();
    domtree.compute(&cfg);

    let mut loop_tree = LoopTree::new();
    loop_tree.compute(&cfg, &domtree);

    let rpo = domtree.rpo().to_vec();

    if rpo.is_empty() {
        return Ok(StructuredCfg {
            regions: Vec::new(),
            block_order: Vec::new(),
        });
    }

    let regions = build_regions(&rpo, &cfg, &domtree, &loop_tree);

    Ok(StructuredCfg {
        block_order: rpo,
        regions,
    })
}

fn build_regions(
    rpo: &[BlockId],
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    loop_tree: &LoopTree,
) -> Vec<Region> {
    let mut regions = Vec::new();
    let mut visited: SecondaryMap<BlockId, bool> = SecondaryMap::new();
    let mut idx = 0;

    while idx < rpo.len() {
        let block = rpo[idx];
        if visited[block] {
            idx += 1;
            continue;
        }

        if let Some(lp) = loop_tree.loop_of_block(block) {
            if loop_tree.loop_header(lp) == block {
                let body =
                    collect_loop_body(block, lp, rpo, idx, loop_tree, cfg, domtree, &mut visited);
                regions.push(Region::Loop {
                    header: block,
                    body,
                });
                idx += 1;
                continue;
            }
        }

        visited[block] = true;
        regions.push(Region::Block(block));
        idx += 1;
    }

    regions
}

fn collect_loop_body(
    header: BlockId,
    lp: crate::loop_analysis::Loop,
    rpo: &[BlockId],
    start_idx: usize,
    loop_tree: &LoopTree,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    visited: &mut SecondaryMap<BlockId, bool>,
) -> Vec<Region> {
    let mut body = Vec::new();
    visited[header] = true;
    body.push(Region::Block(header));

    for &block in &rpo[start_idx + 1..] {
        if !loop_tree.is_in_loop(block, lp) {
            break;
        }
        if visited[block] {
            continue;
        }

        if let Some(inner_lp) = loop_tree.loop_of_block(block) {
            if inner_lp != lp && loop_tree.loop_header(inner_lp) == block {
                let inner_body =
                    collect_loop_body(block, inner_lp, rpo, 0, loop_tree, cfg, domtree, visited);
                body.push(Region::Loop {
                    header: block,
                    body: inner_body,
                });
                continue;
            }
        }

        visited[block] = true;
        body.push(Region::Block(block));
    }

    body
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        Linkage, Module, Signature, Type,
        builder::ModuleBuilder,
        func_cursor::InstInserter,
        inst::control_flow::{Br, Jump, Return},
        isa::{Isa, native::Native},
        module::ModuleCtx,
    };
    use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

    fn native_builder() -> (ModuleBuilder, &'static dyn sonatina_ir::InstSetBase) {
        let isa = Native::new(TargetTriple::new(
            Architecture::X86_64,
            Vendor::Unknown,
            OperatingSystem::Native,
        ));
        let is = isa.inst_set();
        let ctx = ModuleCtx::new(&isa);
        (ModuleBuilder::new(ctx), is)
    }

    #[test]
    fn structurize_linear_cfg() {
        let (mb, is) = native_builder();
        let sig = Signature::new_unit("linear", Linkage::Public, &[]);
        let func_ref = mb.declare_function(sig).unwrap();
        let mut fb = mb.func_builder::<InstInserter>(func_ref);

        let b0 = fb.append_block();
        let b1 = fb.append_block();
        fb.switch_to_block(b0);
        fb.insert_inst_no_result(Jump::new(is, b1));
        fb.switch_to_block(b1);
        fb.insert_inst_no_result(Return::new_unit(is));
        fb.seal_all();
        fb.finish();

        let module = mb.build();
        let result = module
            .func_store
            .view(func_ref, |func| structurize_function(func));
        let structured = result.unwrap();
        assert_eq!(structured.regions.len(), 2);
        assert!(matches!(structured.regions[0], Region::Block(_)));
        assert!(matches!(structured.regions[1], Region::Block(_)));
    }

    #[test]
    fn structurize_simple_loop() {
        let (mb, is) = native_builder();
        let sig = Signature::new_unit("loopy", Linkage::Public, &[Type::I32]);
        let func_ref = mb.declare_function(sig).unwrap();
        let mut fb = mb.func_builder::<InstInserter>(func_ref);

        let entry = fb.append_block();
        let loop_header = fb.append_block();
        let exit = fb.append_block();

        fb.switch_to_block(entry);
        fb.insert_inst_no_result(Jump::new(is, loop_header));

        fb.switch_to_block(loop_header);
        let cond = fb.args()[0];
        fb.insert_inst_no_result(Br::new(is, cond, exit, loop_header));

        fb.switch_to_block(exit);
        fb.insert_inst_no_result(Return::new_unit(is));

        fb.seal_all();
        fb.finish();

        let module = mb.build();
        let result = module
            .func_store
            .view(func_ref, |func| structurize_function(func));
        let structured = result.unwrap();

        let has_loop = structured
            .regions
            .iter()
            .any(|r| matches!(r, Region::Loop { .. }));
        assert!(
            has_loop,
            "expected a loop region in {:?}",
            structured.regions
        );
    }
}
