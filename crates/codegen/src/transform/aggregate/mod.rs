pub(crate) mod abi;
pub(crate) mod byval_object_abi;
mod cleanup;
pub(crate) mod combine;
pub(crate) mod enum_lowering;
pub(crate) mod legalize;
pub(crate) mod object;
pub(crate) mod object_abi;
pub(crate) mod object_effects;
pub(crate) mod object_load_store;
pub(crate) mod object_locality;
pub(crate) mod object_memory;
mod object_state;
mod object_tracking;
pub(crate) mod private_abi;
mod promotion;
mod provenance;
mod reconstruct;
pub(crate) mod scalarize;
pub mod shape;

pub use abi::AggregateExpandAbi;
pub use byval_object_abi::{
    ObjectAggregateAbi, ObjectAggregateAbiConfig, ObjectByValueArgAbi, ObjectByValueArgAbiConfig,
};
pub use enum_lowering::EnumLowerToProduct;
pub use legalize::{AggregateLowerToMemoryLegalize, assert_aggregate_legalized};
pub use object::ObjectLowerToMemory;
pub use object_abi::ObjectReturnOutParam;
pub(crate) use object_effects::{
    ObjectEffectSummaryMap, ObjectReturnEffect, SliceSet, compute_object_effect_summaries,
};
pub(crate) use object_locality::{
    LocalObjectArgInfo, LocalObjectArgMap, RootInit, collect_local_object_arg_info,
    collect_local_object_arg_info_with_effects, merge_local_object_arg_info,
};
pub(crate) use object_memory::{ObjectMemoryAnalysis, ObjectReadGvnKey};
pub(crate) use provenance::{Projection, collect_root_provenance};
