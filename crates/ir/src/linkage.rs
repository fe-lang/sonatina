use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Linkage of symbols.
pub enum Linkage {
    /// The symbol is defined in the module, and can be used from the outside of the module.
    Public,

    /// The symbol is defined in the module, and can NOT be called from another module.
    Private,

    /// The symbol is defined outside of the module.
    External,
}

impl fmt::Display for Linkage {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self {
            Self::Public => write!(f, "public"),
            Self::Private => write!(f, "private"),
            Self::External => write!(f, "external"),
        }
    }
}
