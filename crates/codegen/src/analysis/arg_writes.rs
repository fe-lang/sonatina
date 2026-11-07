//! Which arguments a function may write through, from the object effect
//! summaries.

use rustc_hash::FxHashMap;
use sonatina_ir::{Module, module::FuncRef};

use crate::transform::aggregate::object_effects::compute_object_effect_summaries;

/// For each defined function, whether it may write through each argument
/// while it runs: write a slice of the object it refers to, or let the
/// reference escape, be captured or be materialized as a raw pointer, after
/// which the summary no longer traces what writes through it. A write through
/// a reference the summary cannot trace is not through an argument, whose
/// reference it traces until one of those happens. A function without a
/// summary, as an external one, may write through every argument, and none
/// writes through an argument its signature marks `readonly`.
pub struct ArgWrites {
    by_func: FxHashMap<FuncRef, Vec<bool>>,
}

impl ArgWrites {
    pub fn new(module: &Module) -> Self {
        let summaries = compute_object_effect_summaries(module);
        let by_func = module
            .funcs()
            .into_iter()
            .map(|func| {
                let summary = summaries.get(&func);
                let writes = module.ctx.func_sig(func, |sig| {
                    (0..sig.args().len())
                        .map(|idx| {
                            !sig.is_readonly_arg(idx)
                                && summary.is_none_or(|summary| {
                                    let effect = &summary.arg_effects[idx];
                                    effect.escapes
                                        || effect.materializes_stack
                                        || !effect.writes.is_empty()
                                        || summary
                                            .captures
                                            .iter()
                                            .any(|capture| capture.src_arg == idx)
                                })
                        })
                        .collect()
                });
                (func, writes)
            })
            .collect();
        Self { by_func }
    }

    /// Whether `func` may write through its argument `index` while it runs.
    pub fn may_write(&self, func: FuncRef, index: usize) -> bool {
        self.by_func
            .get(&func)
            .and_then(|writes| writes.get(index))
            .copied()
            .unwrap_or(true)
    }
}
