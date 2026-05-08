mod const_data;
mod legalize;
mod scalar_words;

pub(crate) use const_data::{CONST_WORD_POOL_PREFIX, ConstDataLower};
pub(crate) use legalize::legalize_evm_section;
