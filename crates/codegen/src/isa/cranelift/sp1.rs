use std::sync::Arc;

use cranelift_codegen::{
    isa::{self, TargetIsa},
    settings::{self, Configurable},
};

use super::{CraneliftError, CraneliftObjectBackend};
use crate::backend::BackendOptions;

pub(super) fn build_isa(options: &BackendOptions) -> Result<Arc<dyn TargetIsa>, CraneliftError> {
    let mut flags = CraneliftObjectBackend::flag_builder(options, false)?;
    for (name, value) in [("use_colocated_libcalls", "true"), ("unwind_info", "false")] {
        flags
            .set(name, value)
            .map_err(|error| CraneliftError::Compilation(error.to_string()))?;
    }
    // Keep SP1's exact target in Sonatina. Cranelift uses explicit ISA settings
    // on a standard triple, without a fork of target-lexicon or host CPU flags.
    let mut builder = isa::lookup_by_name("riscv64-unknown-none-elf")
        .map_err(|error| CraneliftError::UnsupportedTarget(error.to_string()))?;
    for (name, value) in [
        ("use_soft_float_abi", "true"),
        ("use_ebreak_traps", "true"),
        ("avoid_integer_constant_pools", "true"),
        ("has_m", "true"),
        ("has_a", "false"),
        ("has_f", "false"),
        ("has_d", "false"),
        ("has_zicsr", "false"),
        ("has_zifencei", "false"),
    ] {
        builder
            .set(name, value)
            .map_err(|error| CraneliftError::Compilation(error.to_string()))?;
    }
    builder
        .finish(settings::Flags::new(flags))
        .map_err(|error| CraneliftError::Compilation(error.to_string()))
}
