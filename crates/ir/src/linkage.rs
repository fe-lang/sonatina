use std::{fmt, io, str::FromStr};

use crate::{ir_writer::IrWrite, module::ModuleCtx};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
/// Linkage of symbols.
pub enum Linkage {
    /// The symbol is defined in the module, and can be used from the outside of
    /// the module.
    Public,

    #[default]
    /// The symbol is defined in the module, and can NOT be called from another
    /// module.
    Private,

    /// The symbol is defined outside of the module.
    External,
}
impl<Ctx> IrWrite<Ctx> for Linkage
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, _ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        match self {
            Self::Public => write!(w, "public"),
            Self::Private => write!(w, "private"),
            Self::External => write!(w, "external"),
        }
    }
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

impl FromStr for Linkage {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "public" => Ok(Self::Public),
            "private" => Ok(Self::Private),
            "external" => Ok(Self::External),
            _ => Err(()),
        }
    }
}
