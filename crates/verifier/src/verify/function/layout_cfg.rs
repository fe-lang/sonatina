use rustc_hash::FxHashSet;
use sonatina_ir::{BlockId, InstId, inst::{control_flow::BranchInfo, downcast}};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Location};

use super::{FunctionVerifier, analysis::compute_reachable};

impl FunctionVerifier<'_> {
    pub(super) fn scan_layout(&mut self) {
        let Some(sig) = self.sig.as_ref() else {
            return;
        };

        if sig.linkage().has_definition() && self.func.layout.entry_block().is_none() {
            self.emit(Diagnostic::error(
                DiagnosticCode::MissingEntryBlock,
                "function with definition has no entry block",
                Location::Function(self.func_ref),
            ));
            return;
        }

        if sig.linkage().is_external() && self.func.layout.entry_block().is_some() {
            self.emit(Diagnostic::error(
                DiagnosticCode::MissingEntryBlock,
                "external function declaration must not contain a layout",
                Location::Function(self.func_ref),
            ));
        }

        let mut seen_blocks = FxHashSet::default();
        let mut previous_block = None;
        let mut next_block = self.func.layout.entry_block();
        let max_block_steps = self.func.layout.block_slots_len().saturating_add(1);
        for _ in 0..max_block_steps {
            let Some(block) = next_block else {
                break;
            };

            if !self.func.layout.has_block_slot(block) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidBlockRef,
                        "layout block list points to an out-of-range block",
                        Location::Function(self.func_ref),
                    )
                    .with_note(format!("invalid block id {}", block.as_u32())),
                );
                break;
            }

            if !self.func.layout.is_block_inserted(block) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnlistedButInserted,
                    "layout linked list points at a block marked as not inserted",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
                break;
            }

            if !seen_blocks.insert(block) {
                self.emit(Diagnostic::error(
                    DiagnosticCode::LayoutBlockCycle,
                    "layout block list contains a cycle",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
                break;
            }

            if !self.func.dfg.has_block(block) {
                self.emit(
                    Diagnostic::error(
                        DiagnosticCode::InvalidBlockRef,
                        "layout references a block that does not exist in DFG",
                        Location::Block {
                            func: self.func_ref,
                            block,
                        },
                    )
                    .with_note(format!("missing block id {}", block.as_u32())),
                );
            }

            if self.cfg.should_run_deep_sanity() {
                let prev = self.func.layout.try_prev_block(block);
                if prev != previous_block {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::BranchInfoMismatch,
                            "layout block backward pointer is inconsistent",
                            Location::Block {
                                func: self.func_ref,
                                block,
                            },
                        )
                        .with_note(format!(
                            "expected previous block {:?}, found {:?}",
                            previous_block.map(|b| b.as_u32()),
                            prev.map(|b| b.as_u32())
                        )),
                    );
                }
            }

            self.block_order.push(block);
            previous_block = Some(block);
            next_block = self.func.layout.try_next_block(block);
        }

        if next_block.is_some() {
            self.emit(Diagnostic::error(
                DiagnosticCode::LayoutBlockCycle,
                "layout block traversal did not terminate; cycle is likely present",
                Location::Function(self.func_ref),
            ));
        }

        let max_block_id = self
            .func
            .layout
            .block_slots_len()
            .max(self.func.dfg.num_blocks());
        for raw in 0..max_block_id {
            let block = BlockId::from_u32(raw as u32);
            let inserted = self
                .func
                .layout
                .try_is_block_inserted(block)
                .unwrap_or(false);
            let listed = seen_blocks.contains(&block);

            if inserted && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "block is marked inserted but not reachable from layout entry chain",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }
            if listed && !inserted {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnlistedButInserted,
                    "block is listed in layout chain but not marked inserted",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }
            if !self.cfg.allow_detached_entities && self.func.dfg.has_block(block) && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "DFG block is detached from layout",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }
        }

        let mut global_seen_insts = FxHashSet::default();
        let listed_blocks = self.block_order.clone();
        for block in listed_blocks {
            let mut block_insts = Vec::new();
            let mut local_seen = FxHashSet::default();
            let mut prev_inst = None;
            let mut next_inst = self.func.layout.try_first_inst_of(block).unwrap_or(None);
            let max_inst_steps = self.func.layout.inst_slots_len().saturating_add(1);

            for index in 0..max_inst_steps {
                let Some(inst) = next_inst else {
                    break;
                };

                if !self.func.layout.has_inst_slot(inst) {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InvalidInstRef,
                            "block instruction list points to an out-of-range instruction",
                            Location::Block {
                                func: self.func_ref,
                                block,
                            },
                        )
                        .with_note(format!("invalid instruction id {}", inst.as_u32())),
                    );
                    break;
                }

                if !self.func.layout.is_inst_inserted(inst) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::UnlistedButInserted,
                        "block instruction list points at instruction not marked inserted",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                    break;
                }

                if !local_seen.insert(inst) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::LayoutInstCycle,
                        "instruction list in block contains a cycle",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                    break;
                }

                if let Some(owner) = self.inst_to_block.get(&inst).copied()
                    && owner != block
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InstInMultipleBlocks,
                            "instruction appears in multiple block lists",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_note(format!(
                            "instruction already appears in block {}",
                            owner.as_u32()
                        )),
                    );
                }

                self.inst_to_block.insert(inst, block);
                self.inst_index_in_block.insert(inst, index);

                if !self.func.dfg.has_inst(inst) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::InvalidInstRef,
                        "layout references instruction that does not exist in DFG",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst,
                        },
                    ));
                }

                if let Some(claimed_block) = self.func.layout.try_inst_block(inst)
                    && claimed_block != block
                {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::InstInMultipleBlocks,
                            "instruction block back-reference does not match list owner",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_note(format!(
                            "instruction claims block {}, list owner is {}",
                            claimed_block.as_u32(),
                            block.as_u32()
                        )),
                    );
                }

                if self.cfg.should_run_deep_sanity() {
                    let prev = self.func.layout.try_prev_inst(inst);
                    if prev != prev_inst {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::BranchInfoMismatch,
                                "instruction backward pointer is inconsistent",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst,
                                },
                            )
                            .with_note(format!(
                                "expected previous inst {:?}, found {:?}",
                                prev_inst.map(|i| i.as_u32()),
                                prev.map(|i| i.as_u32())
                            )),
                        );
                    }
                }

                block_insts.push(inst);
                global_seen_insts.insert(inst);
                prev_inst = Some(inst);
                next_inst = self.func.layout.try_next_inst(inst);
            }

            if next_inst.is_some() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::LayoutInstCycle,
                    "instruction list traversal did not terminate; cycle is likely present",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
            }

            self.block_to_insts.insert(block, block_insts);
        }

        let max_inst_id = self
            .func
            .layout
            .inst_slots_len()
            .max(self.func.dfg.num_insts());
        for raw in 0..max_inst_id {
            let inst = InstId::from_u32(raw as u32);
            let inserted = self.func.layout.try_is_inst_inserted(inst).unwrap_or(false);
            let listed = global_seen_insts.contains(&inst);

            if inserted && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "instruction is marked inserted but unreachable from block instruction lists",
                    Location::Inst {
                        func: self.func_ref,
                        block: None,
                        inst,
                    },
                ));
            }
            if listed && !inserted {
                self.emit(Diagnostic::error(
                    DiagnosticCode::UnlistedButInserted,
                    "instruction appears in layout lists but is not marked inserted",
                    Location::Inst {
                        func: self.func_ref,
                        block: self.inst_to_block.get(&inst).copied(),
                        inst,
                    },
                ));
            }
            if !self.cfg.allow_detached_entities && self.func.dfg.has_inst(inst) && !listed {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InsertedButUnlisted,
                    "DFG instruction is detached from layout",
                    Location::Inst {
                        func: self.func_ref,
                        block: None,
                        inst,
                    },
                ));
            }
        }
    }
    pub(super) fn check_block_and_cfg_rules(&mut self) {
        let blocks = self.block_order.clone();
        for block in blocks {
            self.succs.entry(block).or_default();
            self.preds.entry(block).or_default();
        }

        let mut seen_edges = FxHashSet::default();

        let blocks = self.block_order.clone();
        for block in blocks {
            let insts = self.block_to_insts.get(&block).cloned().unwrap_or_default();
            let mut has_non_tail_terminator = false;

            if insts.is_empty() {
                self.emit(Diagnostic::error(
                    DiagnosticCode::EmptyBlock,
                    "block has no instructions",
                    Location::Block {
                        func: self.func_ref,
                        block,
                    },
                ));
                continue;
            }

            let last_inst = *insts.last().expect("checked non-empty");
            for &inst in insts.iter().take(insts.len().saturating_sub(1)) {
                if self
                    .func
                    .dfg
                    .get_inst(inst)
                    .is_some_and(|data| data.is_terminator())
                {
                    has_non_tail_terminator = true;
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::TerminatorNotLast,
                            "terminator appears before end of block",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst,
                            },
                        )
                        .with_snippet(self.snippet_for_inst(inst)),
                    );
                }
            }

            let Some(last_data) = self.func.dfg.get_inst(last_inst) else {
                self.emit(Diagnostic::error(
                    DiagnosticCode::InvalidInstRef,
                    "block terminator instruction is missing",
                    Location::Inst {
                        func: self.func_ref,
                        block: Some(block),
                        inst: last_inst,
                    },
                ));
                continue;
            };

            if !last_data.is_terminator() {
                let code = if has_non_tail_terminator {
                    DiagnosticCode::NonTerminatorAtEnd
                } else {
                    DiagnosticCode::MissingTerminator
                };
                let message = if has_non_tail_terminator {
                    "block ends with a non-terminator after an earlier terminator"
                } else {
                    "block does not end with a terminator instruction"
                };
                self.emit(
                    Diagnostic::error(
                        code,
                        message,
                        Location::Block {
                            func: self.func_ref,
                            block,
                        },
                    )
                    .with_note(format!(
                        "last instruction is `{}` (inst {})",
                        last_data.as_text(),
                        last_inst.as_u32()
                    ))
                    .with_snippet(self.snippet_for_inst(last_inst)),
                );
                continue;
            }

            let branch = downcast::<&dyn BranchInfo>(self.ctx.inst_set, last_data);
            if let Some(branch) = branch {
                let dests = branch.dests();
                if dests.is_empty() {
                    self.emit(
                        Diagnostic::error(
                            DiagnosticCode::BranchInfoMismatch,
                            "branch terminator must target at least one destination",
                            Location::Inst {
                                func: self.func_ref,
                                block: Some(block),
                                inst: last_inst,
                            },
                        )
                        .with_snippet(self.snippet_for_inst(last_inst)),
                    );
                }

                if branch.num_dests() != dests.len() {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::BranchInfoMismatch,
                        "branch metadata reports inconsistent destination count",
                        Location::Inst {
                            func: self.func_ref,
                            block: Some(block),
                            inst: last_inst,
                        },
                    ));
                }

                for dest in dests {
                    if !self.func.dfg.has_block(dest) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::BranchToMissingBlock,
                                "branch targets a block outside DFG block table",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst: last_inst,
                                },
                            )
                            .with_note(format!("invalid block id {}", dest.as_u32())),
                        );
                        continue;
                    }

                    if self.func.layout.try_is_block_inserted(dest) != Some(true) {
                        self.emit(
                            Diagnostic::error(
                                DiagnosticCode::BranchToNonInsertedBlock,
                                "branch targets a non-inserted block",
                                Location::Inst {
                                    func: self.func_ref,
                                    block: Some(block),
                                    inst: last_inst,
                                },
                            )
                            .with_note(format!("target block {} is detached", dest.as_u32())),
                        );
                        continue;
                    }

                    if seen_edges.insert((block, dest)) {
                        self.succs.entry(block).or_default().push(dest);
                        self.preds.entry(dest).or_default().push(block);
                    }
                }
            }
        }

        if let Some(entry) = self.func.layout.entry_block() {
            self.reachable = compute_reachable(entry, &self.succs);
        }

        if !self.cfg.allow_unreachable_blocks {
            let blocks = self.block_order.clone();
            for block in blocks {
                if !self.reachable.contains(&block) {
                    self.emit(Diagnostic::error(
                        DiagnosticCode::UnreachableBlock,
                        "block is unreachable from function entry",
                        Location::Block {
                            func: self.func_ref,
                            block,
                        },
                    ));
                }
            }
        }
    }
}
