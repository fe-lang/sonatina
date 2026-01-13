use smol_str::SmolStr;

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
    Entry(FuncName),
    Include(FuncName),
    Data(DataName),
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
pub struct FuncName(pub SmolStr);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataName(pub SmolStr);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EmbedSymbol(pub SmolStr);
