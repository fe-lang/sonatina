mod cleanup;
pub mod combine;
pub mod legalize;
pub mod promotion;
pub mod scalarize;
pub mod shape;

pub use combine::AggregateCombine;
pub use legalize::{AggregateLowerToMemoryLegalize, assert_aggregate_legalized};
pub use scalarize::AggregateScalarize;
