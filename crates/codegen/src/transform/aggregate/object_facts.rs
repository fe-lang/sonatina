use sonatina_ir::Module;

use super::{
    LocalObjectArgMap, ObjectEffectSummaryMap, collect_local_object_arg_info_with_effects,
    compute_object_effect_summaries, merge_local_object_arg_info,
};

/// Owned, coherent module facts for a single analysis epoch.
///
/// Build outside mutable function-store accesses. Function passes borrow this
/// snapshot while rewriting; the owner must discard it after a pass that changes
/// object effects, calls, signatures, captures, or reference identities. These
/// maps cannot be supplied independently as pipeline overrides.
pub(crate) struct ModuleObjectFacts {
    effects: ObjectEffectSummaryMap,
    local_args: LocalObjectArgMap,
}

impl ModuleObjectFacts {
    pub(crate) fn compute(module: &Module) -> Self {
        let effects = compute_object_effect_summaries(module);
        let local_args = collect_local_object_arg_info_with_effects(module, &effects);
        Self {
            effects,
            local_args,
        }
    }

    /// Only the enclosing ABI rewrite may transfer its output guarantees into
    /// a fresh snapshot. This checks bindings, not arbitrary mutation validity.
    pub(super) fn with_outputs(mut self, module: &Module, outputs: &LocalObjectArgMap) -> Self {
        merge_local_object_arg_info(module, &mut self.local_args, outputs);
        self
    }

    pub(crate) fn effects(&self) -> &ObjectEffectSummaryMap {
        &self.effects
    }

    pub(crate) fn local_args(&self) -> &LocalObjectArgMap {
        &self.local_args
    }
}
