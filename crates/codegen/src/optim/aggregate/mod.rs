pub mod abi;
mod cleanup;
pub mod combine;
mod enum_lowering;
pub mod legalize;
mod object;
mod object_abi;
mod object_effects;
mod object_load_store;
mod object_locality;
mod object_memory;
mod private_abi;
pub mod promotion;
mod provenance;
mod reconstruct;
pub mod scalarize;
pub mod shape;

pub use abi::AggregateExpandAbi;
pub use combine::AggregateCombine;
pub use enum_lowering::EnumLowerToProduct;
pub use legalize::{AggregateLowerToMemoryLegalize, assert_aggregate_legalized};
pub use object::ObjectLowerToMemory;
pub use object_abi::ObjectReturnOutParam;
pub(crate) use object_effects::{
    ObjectEffectSummaryMap, ObjectReturnEffect, SliceSet, compute_object_effect_summaries,
};
pub use object_load_store::ObjectLoadStore;
pub(crate) use object_locality::{
    LocalObjectArgInfo, LocalObjectArgMap, RootInit, collect_local_object_arg_info,
    collect_local_object_arg_info_with_effects, merge_local_object_arg_info,
};
pub(crate) use object_memory::{ObjectMemoryAnalysis, ObjectReadGvnKey};
pub(crate) use provenance::{Projection, RootProvenance, collect_root_provenance};
pub use scalarize::AggregateScalarize;
