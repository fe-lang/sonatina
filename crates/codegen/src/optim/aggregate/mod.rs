pub use crate::transform::aggregate::{
    combine::AggregateCombine, object_load_store::ObjectLoadStore, scalarize::AggregateScalarize,
};

pub(crate) use crate::transform::aggregate::{
    LocalObjectArgMap, ObjectEffectSummaryMap, ObjectMemoryAnalysis, ObjectReadGvnKey,
    ObjectReturnEffect, collect_local_object_arg_info, collect_local_object_arg_info_with_effects,
    compute_object_effect_summaries,
};
