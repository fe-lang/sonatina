use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, Immediate, Inst, InstId, Signature, Type, Value, ValueId,
    module::{FuncRef, ModuleCtx},
    object::EmbedSymbol,
    types::CompoundType,
};

use crate::{
    VerifierConfig,
    diagnostic::{Diagnostic, DiagnosticCode, DiagnosticContext, Location},
    report::VerificationReport,
};

use super::type_utils;

mod analysis;
mod dominance;
mod layout_cfg;
mod metadata;
mod phi;
mod referential;
mod refs;
mod signature;
mod type_rules;

pub(super) fn verify_function_with_symbols<'a>(
    ctx: &'a ModuleCtx,
    func_ref: FuncRef,
    func: &'a Function,
    cfg: &'a VerifierConfig,
    declared_embed_symbols: Option<&'a FxHashSet<EmbedSymbol>>,
) -> VerificationReport {
    let mut verifier = FunctionVerifier::new(ctx, func_ref, func, cfg, declared_embed_symbols);
    verifier.run();
    verifier.report
}

pub(super) struct FunctionVerifier<'a> {
    pub(super) ctx: &'a ModuleCtx,
    pub(super) func_ref: FuncRef,
    pub(super) func: &'a Function,
    pub(super) sig: Option<Signature>,
    pub(super) declared_embed_symbols: Option<&'a FxHashSet<EmbedSymbol>>,
    pub(super) cfg: &'a VerifierConfig,
    pub(super) report: VerificationReport,

    pub(super) block_order: Vec<BlockId>,
    pub(super) block_to_insts: FxHashMap<BlockId, Vec<InstId>>,
    pub(super) inst_to_block: FxHashMap<InstId, BlockId>,
    pub(super) inst_index_in_block: FxHashMap<InstId, usize>,

    pub(super) succs: FxHashMap<BlockId, Vec<BlockId>>,
    pub(super) preds: FxHashMap<BlockId, Vec<BlockId>>,
    pub(super) reachable: FxHashSet<BlockId>,
}

trait FunctionPass {
    fn enabled(_cfg: &VerifierConfig) -> bool {
        true
    }

    fn run(verifier: &mut FunctionVerifier<'_>);
}

struct SignaturePass;
struct LayoutPass;
struct ReferentialPass;
struct CfgPass;
struct PhiPass;
struct TypePass;
struct DominancePass;
struct MetadataPass;

impl FunctionPass for SignaturePass {
    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_signature_and_values();
    }
}

impl FunctionPass for LayoutPass {
    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.scan_layout();
    }
}

impl FunctionPass for ReferentialPass {
    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_referential_integrity();
    }
}

impl FunctionPass for CfgPass {
    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_block_and_cfg_rules();
    }
}

impl FunctionPass for PhiPass {
    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_phi_rules();
    }
}

impl FunctionPass for TypePass {
    fn enabled(cfg: &VerifierConfig) -> bool {
        cfg.should_check_types()
    }

    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_type_rules();
    }
}

impl FunctionPass for DominancePass {
    fn enabled(cfg: &VerifierConfig) -> bool {
        cfg.should_check_dominance()
    }

    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_dominance_rules();
    }
}

impl FunctionPass for MetadataPass {
    fn enabled(cfg: &VerifierConfig) -> bool {
        cfg.should_check_users() || cfg.should_check_value_caches()
    }

    fn run(verifier: &mut FunctionVerifier<'_>) {
        verifier.check_metadata_consistency();
    }
}

impl<'a> FunctionVerifier<'a> {
    fn new(
        ctx: &'a ModuleCtx,
        func_ref: FuncRef,
        func: &'a Function,
        cfg: &'a VerifierConfig,
        declared_embed_symbols: Option<&'a FxHashSet<EmbedSymbol>>,
    ) -> Self {
        Self {
            ctx,
            func_ref,
            func,
            sig: ctx.get_sig(func_ref),
            declared_embed_symbols,
            cfg,
            report: VerificationReport::default(),
            block_order: Vec::new(),
            block_to_insts: FxHashMap::default(),
            inst_to_block: FxHashMap::default(),
            inst_index_in_block: FxHashMap::default(),
            succs: FxHashMap::default(),
            preds: FxHashMap::default(),
            reachable: FxHashSet::default(),
        }
    }

    fn run(&mut self) {
        self.run_pass::<SignaturePass>();
        self.run_pass::<LayoutPass>();
        self.run_pass::<ReferentialPass>();
        self.run_pass::<CfgPass>();
        self.run_pass::<PhiPass>();
        self.run_pass::<TypePass>();
        self.run_pass::<DominancePass>();
        self.run_pass::<MetadataPass>();
    }

    fn run_pass<P: FunctionPass>(&mut self) {
        if P::enabled(self.cfg) {
            P::run(self);
        }
    }

    pub(super) fn emit(&mut self, diagnostic: Diagnostic) {
        let diagnostic = self.with_diagnostic_context(diagnostic);
        self.report.push(diagnostic, self.cfg.max_diagnostics);
    }

    fn with_diagnostic_context(&self, mut diagnostic: Diagnostic) -> Diagnostic {
        let mut context = diagnostic.context.take().unwrap_or(DiagnosticContext {
            function_name: None,
            inst_text: None,
        });

        if context.function_name.is_none() && self.location_in_current_function(&diagnostic.primary)
        {
            context.function_name = self
                .sig
                .as_ref()
                .map(|signature| format!("%{}", signature.name()));
        }

        if context.inst_text.is_none()
            && let Location::Inst { func, inst, .. } = &diagnostic.primary
            && *func == self.func_ref
        {
            context.inst_text = self
                .func
                .dfg
                .get_inst(*inst)
                .map(|inst_data| inst_data.as_text().to_string());
        }

        if context.function_name.is_some() || context.inst_text.is_some() {
            diagnostic.context = Some(context);
        }

        diagnostic
    }

    fn location_in_current_function(&self, location: &Location) -> bool {
        match location {
            Location::Function(func) => *func == self.func_ref,
            Location::Block { func, .. } => *func == self.func_ref,
            Location::Inst { func, .. } => *func == self.func_ref,
            Location::Value { func, .. } => *func == self.func_ref,
            Location::Type {
                func: Some(func), ..
            } => *func == self.func_ref,
            _ => false,
        }
    }

    pub(super) fn ensure_result_exists(
        &mut self,
        inst: InstId,
        location: Location,
    ) -> Option<Type> {
        let Some(value_id) = self.func.dfg.try_inst_result(inst).flatten() else {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "instruction is expected to produce a result value",
                location,
            ));
            return None;
        };

        self.value_ty(value_id)
    }

    pub(super) fn expect_no_result(&mut self, inst: InstId, location: Location) {
        if self.func.dfg.try_inst_result(inst).flatten().is_some() {
            self.emit(Diagnostic::error(
                DiagnosticCode::InstResultTypeMismatch,
                "instruction must not produce a result value",
                location,
            ));
        }
    }

    pub(super) fn expect_result_ty(&mut self, inst: InstId, expected_ty: Type, location: Location) {
        let Some(actual_ty) = self.ensure_result_exists(inst, location.clone()) else {
            return;
        };

        if actual_ty != expected_ty {
            self.emit(
                Diagnostic::error(
                    DiagnosticCode::InstResultTypeMismatch,
                    "instruction result type does not match expected type",
                    location,
                )
                .with_note(format!("expected {:?}, found {:?}", expected_ty, actual_ty)),
            );
        }
    }

    pub(super) fn inst_result_ty(&self, inst: InstId) -> Option<Type> {
        let value_id = self.func.dfg.try_inst_result(inst).flatten()?;
        self.value_ty(value_id)
    }

    pub(super) fn value_ty(&self, value: ValueId) -> Option<Type> {
        match self.func.dfg.get_value(value) {
            Some(Value::Inst { ty, .. })
            | Some(Value::Arg { ty, .. })
            | Some(Value::Immediate { ty, .. })
            | Some(Value::Global { ty, .. })
            | Some(Value::Undef { ty }) => Some(*ty),
            None => None,
        }
    }

    pub(super) fn value_imm(&self, value: ValueId) -> Option<Immediate> {
        match self.func.dfg.get_value(value) {
            Some(Value::Immediate { imm, .. }) => Some(*imm),
            _ => None,
        }
    }

    pub(super) fn inst_location(&self, inst: InstId) -> Location {
        Location::Inst {
            func: self.func_ref,
            block: self.inst_to_block.get(&inst).copied(),
            inst,
        }
    }

    pub(super) fn snippet_for_inst(&self, inst: InstId) -> Option<String> {
        let block = self.inst_to_block.get(&inst).copied()?;
        let insts = self.block_to_insts.get(&block)?;
        let pos = insts.iter().position(|candidate| *candidate == inst)?;

        let mut snippet = String::new();
        if let Some(sig) = &self.sig {
            snippet.push_str(&format!(
                "func %{}({:?}) -> {:?}\n",
                sig.name(),
                sig.args(),
                sig.ret_ty()
            ));
        }
        snippet.push_str(&format!("  {block}:\n"));

        let start = pos.saturating_sub(2);
        let end = (pos + 3).min(insts.len());
        for (idx, inst_id) in insts[start..end].iter().enumerate() {
            let absolute = start + idx;
            let marker = if absolute == pos { '>' } else { ' ' };
            let name = self
                .func
                .dfg
                .get_inst(*inst_id)
                .map(Inst::as_text)
                .unwrap_or("<missing>");
            snippet.push_str(&format!(" {marker} inst{}: {name}\n", inst_id.as_u32()));
        }

        Some(snippet)
    }

    pub(super) fn type_size(&self, ty: Type) -> Option<usize> {
        if !self.is_type_valid(ty) {
            return None;
        }

        let result = catch_unwind(AssertUnwindSafe(|| self.ctx.size_of(ty)));
        match result {
            Ok(Ok(size)) => Some(size),
            _ => None,
        }
    }

    pub(super) fn is_function_ty(&self, ty: Type) -> bool {
        let Type::Compound(cmpd_ref) = ty else {
            return false;
        };

        self.ctx.with_ty_store(|store| {
            store
                .get_compound(cmpd_ref)
                .is_some_and(|cmpd| matches!(cmpd, CompoundType::Func { .. }))
        })
    }

    pub(super) fn is_storable_type(&self, ty: Type) -> bool {
        self.type_size(ty).is_some() && !self.is_function_ty(ty)
    }

    pub(super) fn is_type_valid(&self, ty: Type) -> bool {
        type_utils::is_type_valid(self.ctx, ty)
    }

    pub(super) fn pointee_ty(&self, ty: Type) -> Option<Type> {
        let Type::Compound(cmpd_ref) = ty else {
            return None;
        };

        self.ctx.with_ty_store(|store| {
            let cmpd = store.get_compound(cmpd_ref)?;
            if let CompoundType::Ptr(elem) = cmpd {
                Some(*elem)
            } else {
                None
            }
        })
    }

    pub(super) fn block_position_map(&self) -> FxHashMap<BlockId, usize> {
        self.block_order
            .iter()
            .enumerate()
            .map(|(index, block)| (*block, index))
            .collect()
    }
}
