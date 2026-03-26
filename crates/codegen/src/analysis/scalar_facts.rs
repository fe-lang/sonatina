use sonatina_ir::{Function, U256, ValueId};

use crate::range_analysis::{RangeEnv, RangeFact};

use super::{
    demanded_bits::DemandedBitsQuery,
    known_bits::{KnownBits, KnownBitsQuery},
};

pub struct ScalarFacts<'a, 'r> {
    known_bits: KnownBitsQuery<'a>,
    demanded_bits: DemandedBitsQuery<'a>,
    range: Option<&'r RangeEnv>,
}

impl<'a, 'r> ScalarFacts<'a, 'r> {
    pub fn new(func: &'a Function) -> Self {
        Self {
            known_bits: KnownBitsQuery::new(func),
            demanded_bits: DemandedBitsQuery::new(func),
            range: None,
        }
    }

    pub fn with_range_env(func: &'a Function, range: &'r RangeEnv) -> Self {
        Self {
            known_bits: KnownBitsQuery::new(func),
            demanded_bits: DemandedBitsQuery::new(func),
            range: Some(range),
        }
    }

    pub fn known_bits(&self, value: ValueId) -> KnownBits {
        self.known_bits.for_value(value)
    }

    pub fn demanded_bits(&self, value: ValueId) -> U256 {
        self.demanded_bits.for_value(value)
    }

    pub fn range(&self, value: ValueId) -> Option<RangeFact> {
        self.range.and_then(|env| env.get(&value).copied())
    }

    pub fn is_known_nonzero(&self, value: ValueId) -> bool {
        self.known_bits.is_known_nonzero(value)
    }
}
