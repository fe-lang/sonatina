use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, Module,
    isa::evm::Evm,
    module::{FuncRef, ModuleCtx},
};

use super::{provenance::compute_value_provenance, scratch_plan::inst_is_scratch_clobber};

pub(crate) fn compute_local_scratch_clobbers(
    module: &Module,
    funcs: &[FuncRef],
    isa: &Evm,
) -> FxHashSet<FuncRef> {
    let mut local = FxHashSet::default();
    for &func in funcs {
        if module.func_store.view(func, |function| {
            func_clobbers_scratch(function, &module.ctx, isa)
        }) {
            local.insert(func);
        }
    }
    local
}

fn func_clobbers_scratch(function: &Function, module: &ModuleCtx, isa: &Evm) -> bool {
    let prov = compute_value_provenance(function, module, isa, |callee| {
        let arg_count = module.func_sig(callee, |sig| sig.args().len());
        vec![true; arg_count]
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
