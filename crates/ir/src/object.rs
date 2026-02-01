use std::io::{self, Write};

use smol_str::SmolStr;

use crate::{
    GlobalVariableRef,
    ir_writer::IrWrite,
    module::{FuncRef, ModuleCtx},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Object {
    pub name: ObjectName,
    pub sections: Vec<Section>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    pub name: SectionName,
    pub directives: Vec<Directive>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Directive {
    Entry(FuncRef),
    Include(FuncRef),
    Data(GlobalVariableRef),
    Embed(Embed),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Embed {
    pub source: SectionRef,
    pub as_symbol: EmbedSymbol,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SectionRef {
    Local(SectionName),
    External {
        object: ObjectName,
        section: SectionName,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ObjectName(pub SmolStr);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SectionName(pub SmolStr);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EmbedSymbol(pub SmolStr);

impl From<&str> for ObjectName {
    fn from(value: &str) -> Self {
        Self(value.into())
    }
}

impl From<String> for ObjectName {
    fn from(value: String) -> Self {
        Self(value.into())
    }
}

impl From<&str> for SectionName {
    fn from(value: &str) -> Self {
        Self(value.into())
    }
}

impl From<String> for SectionName {
    fn from(value: String) -> Self {
        Self(value.into())
    }
}

impl From<&str> for EmbedSymbol {
    fn from(value: &str) -> Self {
        Self(value.into())
    }
}

impl From<String> for EmbedSymbol {
    fn from(value: String) -> Self {
        Self(value.into())
    }
}

impl<Ctx> IrWrite<Ctx> for ObjectName {
    fn write<W: Write>(&self, w: &mut W, _ctx: &Ctx) -> io::Result<()> {
        write!(w, "@{}", self.0.as_str())
    }
}

impl<Ctx> IrWrite<Ctx> for SectionName {
    fn write<W: Write>(&self, w: &mut W, _ctx: &Ctx) -> io::Result<()> {
        write!(w, "{}", self.0.as_str())
    }
}

impl<Ctx> IrWrite<Ctx> for EmbedSymbol {
    fn write<W: Write>(&self, w: &mut W, _ctx: &Ctx) -> io::Result<()> {
        write!(w, "&{}", self.0.as_str())
    }
}

impl<Ctx> IrWrite<Ctx> for SectionRef {
    fn write<W: Write>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()> {
        match self {
            Self::Local(section) => {
                write!(w, ".")?;
                section.write(w, ctx)
            }
            Self::External { object, section } => {
                object.write(w, ctx)?;
                write!(w, ".")?;
                section.write(w, ctx)
            }
        }
    }
}

impl<Ctx> IrWrite<Ctx> for Embed {
    fn write<W: Write>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()> {
        write!(w, "embed ")?;
        self.source.write(w, ctx)?;
        write!(w, " as ")?;
        self.as_symbol.write(w, ctx)?;
        write!(w, ";")
    }
}

impl<Ctx> IrWrite<Ctx> for Directive
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W: Write>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()> {
        match self {
            Self::Entry(func) => {
                write!(w, "entry ")?;
                func.write(w, ctx)?;
                write!(w, ";")
            }
            Self::Include(func) => {
                write!(w, "include ")?;
                func.write(w, ctx)?;
                write!(w, ";")
            }
            Self::Data(data) => {
                write!(w, "data ")?;
                ctx.as_ref()
                    .with_gv_store(|s| write!(w, "${}", s.gv_data(*data).symbol))?;
                write!(w, ";")
            }
            Self::Embed(embed) => embed.write(w, ctx),
        }
    }
}

impl<Ctx> IrWrite<Ctx> for Section
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W: Write>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()> {
        write!(w, "section ")?;
        self.name.write(w, ctx)?;
        writeln!(w, " {{")?;
        for directive in &self.directives {
            write!(w, "        ")?;
            directive.write(w, ctx)?;
            writeln!(w)?;
        }
        write!(w, "    }}")
    }
}

impl<Ctx> IrWrite<Ctx> for Object
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W: Write>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()> {
        write!(w, "object ")?;
        self.name.write(w, ctx)?;
        writeln!(w, " {{")?;
        for section in &self.sections {
            write!(w, "    ")?;
            section.write(w, ctx)?;
            writeln!(w)?;
        }
        write!(w, "}}")
    }
}
