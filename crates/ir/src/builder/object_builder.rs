use rustc_hash::FxHashSet;

use crate::{
    GlobalVariableRef,
    module::FuncRef,
    object::{Directive, Embed, EmbedSymbol, Object, ObjectName, Section, SectionName, SectionRef},
};

use super::{BuilderError, ModuleBuilder};

#[derive(Debug, Clone)]
pub enum ObjectBuilderError {
    MissingEntry {
        object: ObjectName,
        section: SectionName,
    },
    MultipleEntries {
        object: ObjectName,
        section: SectionName,
    },
    DuplicateEmbedSymbol {
        object: ObjectName,
        section: SectionName,
        symbol: EmbedSymbol,
    },
}

impl std::fmt::Display for ObjectBuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingEntry { object, section } => {
                write!(
                    f,
                    "missing entry in section @{}::{}",
                    object.0.as_str(),
                    section.0.as_str()
                )
            }
            Self::MultipleEntries { object, section } => {
                write!(
                    f,
                    "multiple entry directives in section @{}::{}",
                    object.0.as_str(),
                    section.0.as_str()
                )
            }
            Self::DuplicateEmbedSymbol {
                object,
                section,
                symbol,
            } => write!(
                f,
                "duplicate embed symbol &{} in section @{}::{}",
                symbol.0.as_str(),
                object.0.as_str(),
                section.0.as_str()
            ),
        }
    }
}

impl std::error::Error for ObjectBuilderError {}

#[derive(Debug)]
pub enum DeclareObjectError {
    Object(ObjectBuilderError),
    Builder(BuilderError),
}

impl std::fmt::Display for DeclareObjectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Object(e) => e.fmt(f),
            Self::Builder(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for DeclareObjectError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Object(e) => Some(e),
            Self::Builder(e) => Some(e),
        }
    }
}

impl From<ObjectBuilderError> for DeclareObjectError {
    fn from(value: ObjectBuilderError) -> Self {
        Self::Object(value)
    }
}

impl From<BuilderError> for DeclareObjectError {
    fn from(value: BuilderError) -> Self {
        Self::Builder(value)
    }
}

#[derive(Debug, Clone)]
pub struct ObjectBuilder {
    name: ObjectName,
    sections: Vec<SectionBuilder>,
}

impl ObjectBuilder {
    pub fn new(name: impl Into<ObjectName>) -> Self {
        Self {
            name: name.into(),
            sections: Vec::new(),
        }
    }

    pub fn name(&self) -> &ObjectName {
        &self.name
    }

    pub fn section(&mut self, name: impl Into<SectionName>) -> &mut SectionBuilder {
        let name = name.into();
        if let Some(pos) = self.sections.iter().position(|s| s.name == name) {
            return &mut self.sections[pos];
        }
        self.sections.push(SectionBuilder::new(name));
        self.sections.last_mut().expect("just pushed")
    }

    pub fn finish(self) -> Result<Object, ObjectBuilderError> {
        for section in &self.sections {
            section.validate(&self.name)?;
        }

        Ok(Object {
            name: self.name,
            sections: self
                .sections
                .into_iter()
                .map(|section| Section {
                    name: section.name,
                    directives: section.directives,
                })
                .collect(),
        })
    }

    pub fn declare(self, mb: &mut ModuleBuilder) -> Result<(), DeclareObjectError> {
        let object = self.finish()?;
        mb.declare_object(object)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct SectionBuilder {
    name: SectionName,
    directives: Vec<Directive>,
}

impl SectionBuilder {
    pub fn new(name: impl Into<SectionName>) -> Self {
        Self {
            name: name.into(),
            directives: Vec::new(),
        }
    }

    pub fn name(&self) -> &SectionName {
        &self.name
    }

    pub fn directives(&self) -> &[Directive] {
        &self.directives
    }

    pub fn entry(&mut self, func: FuncRef) -> &mut Self {
        self.directives.push(Directive::Entry(func));
        self
    }

    pub fn include(&mut self, func: FuncRef) -> &mut Self {
        self.directives.push(Directive::Include(func));
        self
    }

    pub fn data(&mut self, gv: GlobalVariableRef) -> &mut Self {
        self.directives.push(Directive::Data(gv));
        self
    }

    pub fn embed(&mut self, source: SectionRef, as_symbol: impl Into<EmbedSymbol>) -> &mut Self {
        self.directives.push(Directive::Embed(Embed {
            source,
            as_symbol: as_symbol.into(),
        }));
        self
    }

    pub fn embed_local(
        &mut self,
        section: impl Into<SectionName>,
        as_symbol: impl Into<EmbedSymbol>,
    ) -> &mut Self {
        self.embed(SectionRef::Local(section.into()), as_symbol)
    }

    pub fn embed_external(
        &mut self,
        object: impl Into<ObjectName>,
        section: impl Into<SectionName>,
        as_symbol: impl Into<EmbedSymbol>,
    ) -> &mut Self {
        self.embed(
            SectionRef::External {
                object: object.into(),
                section: section.into(),
            },
            as_symbol,
        )
    }

    fn validate(&self, object: &ObjectName) -> Result<(), ObjectBuilderError> {
        let mut entry_count = 0usize;
        let mut embed_symbols: FxHashSet<EmbedSymbol> = FxHashSet::default();

        for directive in &self.directives {
            match directive {
                Directive::Entry(_) => entry_count += 1,
                Directive::Embed(embed) => {
                    if !embed_symbols.insert(embed.as_symbol.clone()) {
                        return Err(ObjectBuilderError::DuplicateEmbedSymbol {
                            object: object.clone(),
                            section: self.name.clone(),
                            symbol: embed.as_symbol.clone(),
                        });
                    }
                }
                _ => {}
            }
        }

        if entry_count == 0 {
            return Err(ObjectBuilderError::MissingEntry {
                object: object.clone(),
                section: self.name.clone(),
            });
        }
        if entry_count > 1 {
            return Err(ObjectBuilderError::MultipleEntries {
                object: object.clone(),
                section: self.name.clone(),
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Linkage, Signature, Type,
        builder::test_util::test_module_builder,
        global_variable::{GlobalVariableData, GvInitializer},
    };

    #[test]
    fn builds_and_declares_object() {
        let mut mb = test_module_builder();
        let runtime = mb
            .declare_function(Signature::new("runtime", Linkage::Public, &[], Type::Unit))
            .unwrap();
        let init = mb
            .declare_function(Signature::new("init", Linkage::Public, &[], Type::Unit))
            .unwrap();

        let gv = mb.declare_gv(GlobalVariableData::constant(
            "foo".to_string(),
            Type::I32,
            Linkage::Public,
            GvInitializer::make_imm(0i32),
        ));

        let mut obj = ObjectBuilder::new("Contract");
        obj.section("runtime").entry(runtime).data(gv);
        obj.section("init")
            .entry(init)
            .embed_local("runtime", "runtime");

        obj.clone().declare(&mut mb).unwrap();
        let stored = mb.lookup_object("Contract").unwrap();
        assert_eq!(stored.sections.len(), 2);
    }

    #[test]
    fn rejects_missing_entry() {
        let mut obj = ObjectBuilder::new("Contract");
        obj.section("runtime");

        let err = obj.finish().unwrap_err();
        assert!(matches!(err, ObjectBuilderError::MissingEntry { .. }));
    }

    #[test]
    fn rejects_multiple_entries() {
        let mb = test_module_builder();
        let runtime = mb
            .declare_function(Signature::new("runtime", Linkage::Public, &[], Type::Unit))
            .unwrap();

        let mut obj = ObjectBuilder::new("Contract");
        obj.section("runtime").entry(runtime).entry(runtime);

        let err = obj.finish().unwrap_err();
        assert!(matches!(err, ObjectBuilderError::MultipleEntries { .. }));
    }

    #[test]
    fn rejects_duplicate_embed_symbols() {
        let mb = test_module_builder();
        let init = mb
            .declare_function(Signature::new("init", Linkage::Public, &[], Type::Unit))
            .unwrap();

        let mut obj = ObjectBuilder::new("Contract");
        obj.section("init")
            .entry(init)
            .embed_local("runtime", "runtime")
            .embed_local("runtime", "runtime");

        let err = obj.finish().unwrap_err();
        assert!(matches!(
            err,
            ObjectBuilderError::DuplicateEmbedSymbol { .. }
        ));
    }
}
