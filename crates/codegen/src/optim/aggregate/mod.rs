pub mod abi;
mod cleanup;
pub mod combine;
pub mod legalize;
mod object;
mod object_abi;
mod private_abi;
pub mod promotion;
mod reconstruct;
pub mod scalarize;
pub mod shape;

pub use abi::AggregateExpandAbi;
pub use combine::AggregateCombine;
pub use legalize::{AggregateLowerToMemoryLegalize, assert_aggregate_legalized};
pub use object::ObjectLowerToMemory;
pub use object_abi::ObjectReturnOutParam;
pub use scalarize::AggregateScalarize;
