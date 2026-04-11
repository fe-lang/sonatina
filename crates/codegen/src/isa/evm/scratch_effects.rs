use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, Module,
    isa::evm::Evm,
    module::{FuncRef, ModuleCtx},
};

use super::{
    provenance::compute_value_provenance, ptr_escape::PtrEscapeSummary,
    scratch_plan::inst_is_scratch_clobber,
};

pub(crate) fn compute_local_scratch_clobbers(
    module: &Module,
    funcs: &[FuncRef],
    isa: &Evm,
) -> FxHashSet<FuncRef> {
    let mut local: Vec<_> = funcs
        .par_iter()
        .copied()
        .filter(|&func| {
            module.func_store.view(func, |function| {
                func_clobbers_scratch(function, &module.ctx, isa)
            })
        })
        .collect();
    local.sort_unstable_by_key(|func| func.as_u32());
    local.into_iter().collect()
}

fn func_clobbers_scratch(function: &Function, module: &ModuleCtx, isa: &Evm) -> bool {
    let prov = compute_value_provenance(function, module, isa, |callee| {
        PtrEscapeSummary::conservative_unknown_ctx(module, callee)
    });

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if inst_is_scratch_clobber(function, isa, inst, &prov) {
                return true;
            }
        }
    }

    false
}
