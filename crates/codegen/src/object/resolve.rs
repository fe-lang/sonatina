use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    GlobalVariableRef, Module,
    module::FuncRef,
    object::{Directive, EmbedSymbol, Object, ObjectName, SectionName, SectionRef},
};

use super::error::ObjectCompileError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SectionId {
    pub object: ObjectId,
    pub section: u32,
}

pub struct ResolvedProgram<'m> {
    pub module: &'m Module,
    pub object_index: FxHashMap<ObjectName, ObjectId>,
    pub objects: Vec<ResolvedObject>,
}

#[derive(Debug)]
pub struct ResolvedObject {
    pub name: ObjectName,
    pub sections: Vec<ResolvedSection>,
}

#[derive(Debug)]
pub struct ResolvedSection {
    pub name: SectionName,
    pub entry: FuncRef,
    pub includes: Vec<FuncRef>,
    pub data: FxHashSet<GlobalVariableRef>,
    pub embeds: Vec<ResolvedEmbed>,
}

#[derive(Debug)]
pub struct ResolvedEmbed {
    pub source: SectionId,
    pub as_symbol: EmbedSymbol,
}

#[derive(Debug)]
struct UnvalidatedObject {
    name: ObjectName,
    sections: Vec<UnvalidatedSection>,
}

#[derive(Debug)]
struct UnvalidatedSection {
    name: SectionName,
    entry: FuncRef,
    includes: Vec<FuncRef>,
    data: FxHashSet<GlobalVariableRef>,
    embeds: Vec<ResolvedEmbed>,
}

impl<'m> ResolvedProgram<'m> {
    pub fn resolve(module: &'m Module) -> Result<Self, Vec<ObjectCompileError>> {
        let mut raw_objects: Vec<&Object> = module.objects.values().collect();
        raw_objects.sort_by(|a, b| a.name.0.as_str().cmp(b.name.0.as_str()));

        let mut object_index = FxHashMap::default();
        for (idx, obj) in raw_objects.iter().enumerate() {
            object_index.insert(obj.name.clone(), ObjectId(idx as u32));
        }

        let mut section_index: Vec<FxHashMap<SectionName, u32>> = Vec::new();
        for obj in &raw_objects {
            let mut map = FxHashMap::default();
            for (idx, section) in obj.sections.iter().enumerate() {
                if map.insert(section.name.clone(), idx as u32).is_some() {
                    panic!(
                        "verifier invariant violated: duplicate section name @{}.{}",
                        obj.name.0.as_str(),
                        section.name.0.as_str()
                    );
                }
            }
            section_index.push(map);
        }

        let mut objects: Vec<UnvalidatedObject> = Vec::new();
        for obj in &raw_objects {
            let object_id = object_index[&obj.name];
            let mut resolved_sections: Vec<UnvalidatedSection> = Vec::new();

            for (section_idx, section) in obj.sections.iter().enumerate() {
                let section_name = section.name.clone();
                let mut entry: Option<FuncRef> = None;
                let mut includes = Vec::new();
                let mut include_set = FxHashSet::default();
                let mut data = FxHashSet::default();
                let mut embeds = Vec::new();
                let mut embed_syms = FxHashSet::default();

                let mut entry_count = 0usize;

                for directive in &section.directives {
                    match directive {
                        Directive::Entry(func) => {
                            entry_count += 1;
                            if entry.is_none() {
                                entry = Some(*func);
                            }
                        }
                        Directive::Include(func) => {
                            if include_set.insert(*func) {
                                includes.push(*func);
                            }
                        }
                        Directive::Data(gv) => {
                            data.insert(*gv);
                        }
                        Directive::Embed(embed) => {
                            if !embed_syms.insert(embed.as_symbol.clone()) {
                                panic!(
                                    "verifier invariant violated: duplicate embed symbol &{} in @{}.{}",
                                    embed.as_symbol.0.as_str(),
                                    obj.name.0.as_str(),
                                    section_name.0.as_str()
                                );
                            }
                            let source = resolve_section_ref(
                                &object_index,
                                &section_index,
                                object_id,
                                &embed.source,
                                &obj.name,
                                &section_name,
                            );
                            embeds.push(ResolvedEmbed {
                                source,
                                as_symbol: embed.as_symbol.clone(),
                            });
                        }
                    }
                }

                if entry_count != 1 || entry.is_none() {
                    panic!(
                        "verifier invariant violated: section @{}.{} must have exactly one entry",
                        obj.name.0.as_str(),
                        section_name.0.as_str()
                    );
                }

                resolved_sections.push(UnvalidatedSection {
                    name: section_name,
                    entry: entry.expect("entry_count checked"),
                    includes,
                    data,
                    embeds,
                });
                debug_assert_eq!(section_idx, resolved_sections.len() - 1);
            }

            objects.push(UnvalidatedObject {
                name: obj.name.clone(),
                sections: resolved_sections,
            });
        }

        let objects: Vec<ResolvedObject> = objects
            .into_iter()
            .map(|obj| ResolvedObject {
                name: obj.name,
                sections: obj
                    .sections
                    .into_iter()
                    .map(|section| ResolvedSection {
                        name: section.name,
                        entry: section.entry,
                        includes: section.includes,
                        data: section.data,
                        embeds: section.embeds,
                    })
                    .collect(),
            })
            .collect();

        let program = Self {
            module,
            object_index,
            objects,
        };

        if let Some(cycle) = detect_embed_cycle(&program) {
            let mut pretty = Vec::new();
            for id in cycle {
                let (obj, section) = program.section_name(id);
                pretty.push((obj.clone(), section.clone()));
            }
            return Err(vec![ObjectCompileError::EmbedCycle { cycle: pretty }]);
        }

        Ok(program)
    }

    pub fn object(&self, id: ObjectId) -> &ResolvedObject {
        &self.objects[id.0 as usize]
    }

    pub fn section(&self, id: SectionId) -> &ResolvedSection {
        &self.objects[id.object.0 as usize].sections[id.section as usize]
    }

    pub fn section_name(&self, id: SectionId) -> (&ObjectName, &SectionName) {
        let obj = &self.objects[id.object.0 as usize];
        let section = &obj.sections[id.section as usize];
        (&obj.name, &section.name)
    }

    pub fn all_sections(&self) -> Vec<SectionId> {
        let mut ids = Vec::new();
        for obj in &self.objects {
            let object = self.object_index[&obj.name];
            for (idx, _) in obj.sections.iter().enumerate() {
                ids.push(SectionId {
                    object,
                    section: idx as u32,
                });
            }
        }
        ids
    }
}

fn resolve_section_ref(
    object_index: &FxHashMap<ObjectName, ObjectId>,
    section_index: &[FxHashMap<SectionName, u32>],
    this_object: ObjectId,
    ref_: &SectionRef,
    object: &ObjectName,
    section: &SectionName,
) -> SectionId {
    let (target_object, target_section_name) = match ref_ {
        SectionRef::Local(name) => (this_object, name.clone()),
        SectionRef::External {
            object: obj,
            section: name,
        } => {
            let object_id = object_index.get(obj).copied().unwrap_or_else(|| {
                panic!(
                    "verifier invariant violated: missing external object @{} referenced from @{}.{}",
                    obj.0.as_str(),
                    object.0.as_str(),
                    section.0.as_str()
                )
            });
            (object_id, name.clone())
        }
    };

    let section_map = &section_index[target_object.0 as usize];
    let section_idx = section_map
        .get(&target_section_name)
        .copied()
        .unwrap_or_else(|| {
            panic!(
                "verifier invariant violated: missing section {} referenced from @{}.{}",
                target_section_name.0.as_str(),
                object.0.as_str(),
                section.0.as_str()
            )
        });

    SectionId {
        object: target_object,
        section: section_idx,
    }
}

fn detect_embed_cycle(program: &ResolvedProgram<'_>) -> Option<Vec<SectionId>> {
    let roots = program.all_sections();

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum State {
        Visiting,
        Done,
    }

    let mut state: FxHashMap<SectionId, State> = FxHashMap::default();
    let mut stack: Vec<SectionId> = Vec::new();

    fn dfs(
        program: &ResolvedProgram<'_>,
        node: SectionId,
        state: &mut FxHashMap<SectionId, State>,
        stack: &mut Vec<SectionId>,
    ) -> Option<Vec<SectionId>> {
        match state.get(&node) {
            Some(State::Done) => return None,
            Some(State::Visiting) => {
                let start = stack.iter().position(|id| *id == node).unwrap_or(0);
                return Some(stack[start..].to_vec());
            }
            None => {}
        }

        state.insert(node, State::Visiting);
        stack.push(node);

        let deps = program.section(node).embeds.iter().map(|e| e.source);
        for dep in deps {
            if let Some(cycle) = dfs(program, dep, state, stack) {
                return Some(cycle);
            }
        }

        stack.pop();
        state.insert(node, State::Done);
        None
    }

    for root in roots {
        if let Some(cycle) = dfs(program, root, &mut state, &mut stack) {
            return Some(cycle);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_parser::parse_module;

    #[test]
    fn reject_embed_cycles() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        return;
}

object @A {
  section init    { entry %main; embed .runtime as &rt; }
  section runtime { entry %main; embed .init    as &init; }
}
"#;

        let parsed = parse_module(s).unwrap();
        let err = ResolvedProgram::resolve(&parsed.module).err().unwrap();
        assert!(
            err.iter()
                .any(|e| matches!(e, ObjectCompileError::EmbedCycle { .. }))
        );
    }

    #[test]
    #[should_panic(expected = "duplicate embed symbol")]
    fn duplicate_embed_symbol_invariant_panics() {
        let s = r#"
target = "evm-ethereum-london"

func public %main() {
    block0:
        return;
}

object @A {
  section init {
    entry %main;
    embed .init as &x;
    embed .init as &x;
  }
}
"#;

        let parsed = parse_module(s).unwrap();
        let _ = ResolvedProgram::resolve(&parsed.module);
    }
}
