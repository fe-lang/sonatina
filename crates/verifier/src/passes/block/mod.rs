//! Passes to verify block integrity

pub mod end_in_terminator;
pub mod non_empty;

pub use end_in_terminator::EndInTerminator;
pub use non_empty::NonEmpty;
