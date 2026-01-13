use ir::object::{
    DataName, Directive, Embed, EmbedSymbol, FuncName, Object, ObjectName, Section, SectionName,
    SectionRef,
};
use pest::Parser as _;

use crate::{
    Error,
    syntax::{FromSyntax, Node, Parser, Rule},
};

pub fn parse_object_file(input: &str) -> Result<Vec<Object>, Vec<Error>> {
    match Parser::parse(Rule::object_file, input) {
        Err(err) => Err(vec![Error::SyntaxError(err)]),
        Ok(mut pairs) => {
            let pair = pairs.next().unwrap();
            debug_assert_eq!(pair.as_rule(), Rule::object_file);
            let mut node = Node::new(pair);

            if node.errors.is_empty() {
                Ok(node.multi(Rule::object_definition))
            } else {
                Err(node.errors)
            }
        }
    }
}

impl FromSyntax<Error> for Object {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self {
            name: node.single(Rule::object_identifier),
            sections: node.multi(Rule::object_section),
        }
    }
}

impl FromSyntax<Error> for ObjectName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self(node.parse_str(Rule::object_name))
    }
}

impl FromSyntax<Error> for Section {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self {
            name: node.single(Rule::section_name),
            directives: node.multi(Rule::section_stmt),
        }
    }
}

impl FromSyntax<Error> for SectionName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self(node.txt.into())
    }
}

impl FromSyntax<Error> for Directive {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        node.descend();
        match node.rule {
            Rule::section_entry => Directive::Entry(
                node.descend_into(Rule::function_identifier, |n| n.single(Rule::function_name)),
            ),
            Rule::section_include => Directive::Include(
                node.descend_into(Rule::function_identifier, |n| n.single(Rule::function_name)),
            ),
            Rule::section_data => {
                Directive::Data(node.descend_into(Rule::gv_identifier, |n| n.single(Rule::gv_name)))
            }
            Rule::section_embed => Directive::Embed(Embed::from_syntax(node)),
            _ => unreachable!(),
        }
    }
}

impl FromSyntax<Error> for FuncName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self(node.txt.into())
    }
}

impl FromSyntax<Error> for DataName {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self(node.txt.into())
    }
}

impl FromSyntax<Error> for Embed {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self {
            source: node.single(Rule::section_ref),
            as_symbol: node.single(Rule::embed_symbol),
        }
    }
}

impl FromSyntax<Error> for EmbedSymbol {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        Self(node.parse_str(Rule::embed_name))
    }
}

impl FromSyntax<Error> for SectionRef {
    fn from_syntax(node: &mut Node<Error>) -> Self {
        node.descend();
        match node.rule {
            Rule::local_section_ref => SectionRef::Local(node.single(Rule::section_name)),
            Rule::external_section_ref => SectionRef::External {
                object: node.single(Rule::object_identifier),
                section: node.single(Rule::section_name),
            },
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_object_file_smoke() {
        let s = r#"
object @Factory {
  section init {
    entry %factory_init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %factory; # all functions reachable from %factory are implied
    include %other_function;
    data $foo;
    embed @Child.init as &child_init;
  }
}

object @Child {
  section runtime { entry %child_main; }
  section init    { entry %child_init; embed .runtime as &runtime; }
}
"#;

        let objects = parse_object_file(s).unwrap();
        assert_eq!(
            objects,
            vec![
                Object {
                    name: ObjectName("Factory".into()),
                    sections: vec![
                        Section {
                            name: SectionName("init".into()),
                            directives: vec![
                                Directive::Entry(FuncName("factory_init".into())),
                                Directive::Embed(Embed {
                                    source: SectionRef::Local(SectionName("runtime".into())),
                                    as_symbol: EmbedSymbol("runtime".into()),
                                }),
                            ],
                        },
                        Section {
                            name: SectionName("runtime".into()),
                            directives: vec![
                                Directive::Entry(FuncName("factory".into())),
                                Directive::Include(FuncName("other_function".into())),
                                Directive::Data(DataName("foo".into())),
                                Directive::Embed(Embed {
                                    source: SectionRef::External {
                                        object: ObjectName("Child".into()),
                                        section: SectionName("init".into()),
                                    },
                                    as_symbol: EmbedSymbol("child_init".into()),
                                }),
                            ],
                        },
                    ],
                },
                Object {
                    name: ObjectName("Child".into()),
                    sections: vec![
                        Section {
                            name: SectionName("runtime".into()),
                            directives: vec![Directive::Entry(FuncName("child_main".into()))],
                        },
                        Section {
                            name: SectionName("init".into()),
                            directives: vec![
                                Directive::Entry(FuncName("child_init".into())),
                                Directive::Embed(Embed {
                                    source: SectionRef::Local(SectionName("runtime".into())),
                                    as_symbol: EmbedSymbol("runtime".into()),
                                }),
                            ],
                        },
                    ],
                },
            ],
        );
    }
}
