use rustc_hash::FxHashMap;
use sonatina_ir::{BlockId, Function, Inst, Type, Value, ValueId, visitor::VisitorMut};

#[derive(Debug, Clone, Copy)]
pub(super) struct PhiFixup {
    pub arg_index: usize,
    pub old_value: ValueId,
}

#[derive(Debug, Clone, Copy)]
enum ValueRewriteMode {
    RequireMapped,
    AllowForwardRefsInPhi,
}

pub(super) struct OperandRewriter<'a> {
    pub callee: &'a Function,
    pub caller: &'a mut Function,
    pub value_map: &'a mut FxHashMap<ValueId, ValueId>,
    pub block_map: &'a FxHashMap<BlockId, BlockId>,

    mode: ValueRewriteMode,
    phi_next_arg: usize,
    phi_expect_block: bool,
    phi_fixups: Vec<PhiFixup>,
    ok: bool,
}

impl<'a> OperandRewriter<'a> {
    pub(super) fn new(
        callee: &'a Function,
        caller: &'a mut Function,
        value_map: &'a mut FxHashMap<ValueId, ValueId>,
        block_map: &'a FxHashMap<BlockId, BlockId>,
    ) -> Self {
        Self {
            callee,
            caller,
            value_map,
            block_map,
            mode: ValueRewriteMode::RequireMapped,
            phi_next_arg: 0,
            phi_expect_block: false,
            phi_fixups: Vec::new(),
            ok: true,
        }
    }

    pub(super) fn rewrite_inst_operands(
        mut self,
        inst: &mut dyn Inst,
        is_phi: bool,
    ) -> Result<Vec<PhiFixup>, ()> {
        if is_phi {
            self.mode = ValueRewriteMode::AllowForwardRefsInPhi;
            self.phi_next_arg = 0;
            self.phi_expect_block = false;
        } else {
            self.mode = ValueRewriteMode::RequireMapped;
        }

        inst.accept_mut(&mut self);

        if self.ok {
            Ok(self.phi_fixups)
        } else {
            Err(())
        }
    }

    fn map_or_materialize_const(&mut self, old: ValueId) -> Option<ValueId> {
        if let Some(&mapped) = self.value_map.get(&old) {
            return Some(mapped);
        }

        let mapped = match self.callee.dfg.value(old) {
            Value::Immediate { imm, .. } => self.caller.dfg.make_imm_value(*imm),
            Value::Global { gv, .. } => self.caller.dfg.make_global_value(*gv),
            Value::Undef { ty } => self.caller.dfg.make_undef_value(*ty),
            Value::Arg { .. } | Value::Inst { .. } => return None,
        };

        self.value_map.insert(old, mapped);
        Some(mapped)
    }

    fn make_undef_for(&mut self, old: ValueId) -> ValueId {
        let ty: Type = self.callee.dfg.value_ty(old);
        self.caller.dfg.make_undef_value(ty)
    }

    fn in_phi_mode(&self) -> bool {
        matches!(self.mode, ValueRewriteMode::AllowForwardRefsInPhi)
    }
}

impl VisitorMut for OperandRewriter<'_> {
    fn visit_value_id(&mut self, value: &mut ValueId) {
        let old = *value;

        if let Some(mapped) = self.map_or_materialize_const(old) {
            *value = mapped;
            if self.in_phi_mode() {
                self.phi_expect_block = true;
            }
            return;
        }

        match self.mode {
            ValueRewriteMode::RequireMapped => {
                self.ok = false;
            }
            ValueRewriteMode::AllowForwardRefsInPhi => match self.callee.dfg.value(old) {
                Value::Inst { .. } => {
                    let undef = self.make_undef_for(old);
                    *value = undef;
                    self.phi_fixups.push(PhiFixup {
                        arg_index: self.phi_next_arg,
                        old_value: old,
                    });
                    self.phi_expect_block = true;
                }
                _ => {
                    self.ok = false;
                }
            },
        }
    }

    fn visit_block_id(&mut self, block: &mut BlockId) {
        let old = *block;
        let Some(&mapped) = self.block_map.get(&old) else {
            self.ok = false;
            return;
        };
        *block = mapped;

        if self.in_phi_mode() && self.phi_expect_block {
            self.phi_next_arg += 1;
            self.phi_expect_block = false;
        }
    }
}
