//! This module defines a module-level linking on sonatina-IR that links
//! multiple sonatina modules into a single module.

use std::mem;

use cranelift_entity::entity_impl;
use dashmap::{DashMap, ReadOnlyView, mapref::one::Ref};
use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    GlobalVariableRef, Linkage, Module, Signature, Type, Value,
    builder::{BuilderError, ModuleBuilder},
    module::FuncRef,
    types::{CompoundType, CompoundTypeRef, StructData},
    visitor::VisitorMut,
};

/// A struct represents a linked module, that is the result of the
/// sonatina-module-level linking.
///
/// This module contains a single module as a result of the linking, and
/// auxiliary mapping from the references in the original modules
/// (e.g., [`FuncRef`]/[`GlobalVariableRef`]/[`CompoundTypeRef`])
/// to the ones in linked modules.
pub struct LinkedModule {
    /// A linked module.
    module: Module,

    /// A mapping from a source module reference to a reference in the linked
    /// module.
    pub module_ref_map: ReadOnlyView<ModuleRef, RefMap>,
}

// TODO: Improve the definition of errors.
#[derive(Debug, Clone)]
pub enum LinkError {
    /// The input modules are empty.
    EmptyModules,

    /// The input modules have inconsistent target triples.
    InconsistentTargetTriple,

    InconsistentStructType {
        name: String,
    },

    InconsistentGlobalVariable {
        name: String,
    },

    InconsistentFuncSignature {
        name: String,
    },

    DuplicateObjectDefinition {
        name: String,
    },
}

impl LinkedModule {
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// Links multiple modules into a single module.
    /// Returns a linked module and a list of module references.
    /// The order of module references are the same as the input modules.
    pub fn link(modules: Vec<Module>) -> Result<(Self, Vec<ModuleRef>), LinkError> {
        let mut modules = modules.into_iter();
        let Some(first_module) = modules.next() else {
            return Err(LinkError::EmptyModules);
        };

        let (mut linker, first_module_ref) = ModuleLinker::from_module(first_module);
        let mut module_refs = vec![first_module_ref];
        for module in modules {
            let module_ref = linker.register_module(module);
            module_refs.push(module_ref);
        }

        let linked_module = linker.link()?;
        Ok((linked_module, module_refs))
    }

    /// Add a module to the linked module.
    pub fn append_module(self, module: Module) -> Result<(Self, ModuleRef), LinkError> {
        let (linked, module_refs) = self.append_modules(vec![module])?;
        Ok((linked, module_refs[0]))
    }

    /// Add multiple modules to the linked module.
    pub fn append_modules(self, modules: Vec<Module>) -> Result<(Self, Vec<ModuleRef>), LinkError> {
        let mut linker = ModuleLinker::from_linked_module(self);
        let mut module_refs = Vec::with_capacity(modules.len());
        for module in modules {
            let module_ref = linker.register_module(module);
            module_refs.push(module_ref);
        }

        let linked_module = linker.link()?;
        Ok((linked_module, module_refs))
    }
}

/// An entity representing a module reference.
/// This is used to identify a module in the linked module for mapping from
/// the source module reference to the linked module reference.
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct ModuleRef(pub u32);
entity_impl!(ModuleRef);

#[derive(Debug, Default)]
pub struct RefMap {
    /// A mapping from a function reference in a source module to a function
    /// reference in a linked module.
    func_mapping: FxHashMap<FuncRef, FuncRef>,

    /// A mapping from a compound type reference in a source module to a
    /// compound type reference in a linked module.
    cmpd_mapping: FxHashMap<CompoundTypeRef, CompoundTypeRef>,

    /// A mapping from a global variable reference in a source module to a
    /// global variable reference in a linked module.
    gv_mapping: FxHashMap<GlobalVariableRef, GlobalVariableRef>,
}

impl RefMap {
    /// Converts a type in a source module to a type in a linked module.
    pub fn lookup_type(&self, source_ty: Type) -> Type {
        match source_ty {
            Type::Compound(cmpd_ref) => Type::Compound(self.cmpd_mapping[&cmpd_ref]),
            _ => source_ty,
        }
    }

    /// Converts a global variable reference to a global variable reference in a
    /// linked module.
    pub fn lookup_gv(&self, gv: GlobalVariableRef) -> GlobalVariableRef {
        self.gv_mapping[&gv]
    }

    /// Converts a function reference to a function reference in a linked
    /// module.
    pub fn lookup_func(&self, func: FuncRef) -> FuncRef {
        self.func_mapping[&func]
    }

    /// Updates the value in-place from a source module to a linked module.
    ///
    /// This method doesn't modify an instruction that the value refers to.
    fn update_value(&self, value: &mut Value) {
        match value {
            Value::Inst { ty, .. } => {
                *ty = self.lookup_type(*ty);
            }

            Value::Arg { ty, .. } => {
                *ty = self.lookup_type(*ty);
            }

            Value::Immediate { ty, .. } => {
                *ty = self.lookup_type(*ty);
            }

            Value::Global { gv, ty } => {
                *gv = self.lookup_gv(*gv);
                *ty = self.lookup_type(*ty);
            }

            Value::Undef { ty } => {
                *ty = self.lookup_type(*ty);
            }
        }
    }

    /// Creates a identity mapping with the given module.
    fn identity_with(module: &Module) -> Self {
        let mut ref_map = Self::default();

        module.func_store.funcs().into_iter().for_each(|func_ref| {
            ref_map.func_mapping.insert(func_ref, func_ref);
        });
        module.ctx.with_gv_store(|s| {
            s.all_gv_refs().for_each(|gv_ref| {
                ref_map.gv_mapping.insert(gv_ref, gv_ref);
            })
        });
        module.ctx.with_ty_store(|s| {
            s.all_compounds().for_each(|(cmpd_ref, _)| {
                ref_map.cmpd_mapping.insert(cmpd_ref, cmpd_ref);
            })
        });

        ref_map
    }

    fn map_cmpd(&mut self, from: CompoundTypeRef, to: CompoundTypeRef) {
        self.cmpd_mapping.insert(from, to);
    }

    fn map_gv(&mut self, from: GlobalVariableRef, to: GlobalVariableRef) {
        self.gv_mapping.insert(from, to);
    }
}

struct ModuleLinker {
    /// A module builder for the linked module.
    builder: ModuleBuilder,

    module_ref_map: DashMap<ModuleRef, RefMap>,

    /// Modules to be linked.
    modules: IndexMap<ModuleRef, Module>,
}

impl ModuleLinker {
    /// Takes a `module` as a destination.
    fn from_module(module: Module) -> (Self, ModuleRef) {
        let ref_map = RefMap::identity_with(&module);

        let builder = ModuleBuilder::from_module(module);
        let module_ref = ModuleRef(0);
        let module_ref_map = DashMap::new();
        module_ref_map.insert(module_ref, ref_map);

        let linker = Self {
            builder,
            module_ref_map,
            modules: IndexMap::new(),
        };

        (linker, module_ref)
    }

    /// Takes a linked module as a destination.
    /// All module references in the `linked_module` are still
    /// valid after linking.
    fn from_linked_module(linked_module: LinkedModule) -> Self {
        let builder = ModuleBuilder::from_module(linked_module.module);
        let module_ref_map = linked_module.module_ref_map.into_inner();

        Self {
            builder,
            module_ref_map,
            modules: IndexMap::new(),
        }
    }

    /// Registers a module as a source module to be linked.
    fn register_module(&mut self, module: Module) -> ModuleRef {
        let next_id = self.module_ref_map.len();
        let module_ref = ModuleRef(next_id as u32);
        self.module_ref_map.insert(module_ref, Default::default());
        self.modules.insert(module_ref, module);

        module_ref
    }

    /// Performs linking.
    fn link(mut self) -> Result<LinkedModule, LinkError> {
        let module_refs: Vec<_> = self.modules.keys().copied().collect();

        // Links all references in the source modules to the linked module.
        self.link_refs(&module_refs)?;

        let modules = mem::take(&mut self.modules);
        // Move functions to the linked module.
        for (module_ref, module) in modules {
            let ref_map = self.module_ref_map.get(&module_ref).unwrap();
            for (_, object) in module.objects {
                self.builder
                    .declare_object(object)
                    .map_err(|err| match err {
                        BuilderError::DuplicateObjectDefinition { name } => {
                            LinkError::DuplicateObjectDefinition { name }
                        }
                        BuilderError::ConflictingFunctionDeclaration => unreachable!(
                            "unexpected function declaration error while linking objects"
                        ),
                    })?;
            }
            module.func_store.par_into_for_each(|func_ref, mut func| {
                // If linkage is external, we don't need to move the function definition to the
                // linked module.
                if func
                    .dfg
                    .ctx
                    .func_sig(func_ref, |sig| sig.linkage())
                    .is_external()
                {
                    return;
                }

                // Updates module context to the linked module.
                func.dfg.ctx = self.builder.ctx.clone();

                // Updates references in values to the linked module.
                func.dfg.values.values_mut().for_each(|value| {
                    ref_map.update_value(value);
                });

                // Updates the references in instructions to the linked module.
                struct InstUpdater<'a> {
                    ref_map: &'a Ref<'a, ModuleRef, RefMap>,
                }
                impl VisitorMut for InstUpdater<'_> {
                    fn visit_func_ref(&mut self, item: &mut FuncRef) {
                        *item = self.ref_map.lookup_func(*item);
                    }

                    fn visit_gv_ref(&mut self, item: &mut GlobalVariableRef) {
                        *item = self.ref_map.lookup_gv(*item);
                    }

                    fn visit_ty(&mut self, item: &mut Type) {
                        *item = self.ref_map.lookup_type(*item);
                    }
                }
                let mut visitor = InstUpdater { ref_map: &ref_map };
                func.dfg
                    .insts
                    .values_mut()
                    .for_each(|inst| inst.accept_mut(&mut visitor));

                let linked_func_ref = ref_map.lookup_func(func_ref);
                self.builder.func_store.update(linked_func_ref, func);
            })
        }

        let linked_module = LinkedModule {
            module: self.builder.build(),
            module_ref_map: self.module_ref_map.into_read_only(),
        };
        Ok(linked_module)
    }

    /// Links all references in the source modules to the linked module.
    ///
    /// When the method performs successfully, all references in the source
    /// modules are available in the linked module, and the reference map is
    /// updated accordingly.
    ///
    /// NOTE: This method doesn't modify the `Function` in each module.
    /// This means after this process, the reference in the function body should
    /// be updated by referring to the reference map later, and also
    /// function body should be moved into linked module as a final process.
    fn link_refs(&mut self, module_refs: &[ModuleRef]) -> Result<(), LinkError> {
        for module_ref in module_refs {
            // 1. Validate the target triple.
            if self.builder.triple() != self.modules[module_ref].ctx.triple {
                return Err(LinkError::InconsistentTargetTriple);
            }

            // 2. Link compound type reference.
            let cmpd_refs: Vec<_> = self.modules[module_ref]
                .ctx
                .with_ty_store(|s| s.all_compound_refs().collect());
            for cmpd_ref in cmpd_refs {
                self.link_cmpd(*module_ref, cmpd_ref)?;
            }

            // 3. Link global variable references.
            let gv_refs: Vec<_> = self.modules[module_ref]
                .ctx
                .with_gv_store(|s| s.all_gv_refs().collect());
            for gv_ref in gv_refs {
                self.link_gv(*module_ref, gv_ref)?;
            }

            // 4. Link function references.
            let func_refs = self.modules[module_ref].funcs();
            for func_ref in func_refs {
                self.link_func_ref(*module_ref, func_ref)?;
            }
        }

        Ok(())
    }

    /// Links a compound type reference in the source module to a linked module.
    /// Returns a linked compound type reference in the linked module.
    ///
    /// This method updates the reference map internally.
    fn link_cmpd(
        &mut self,
        module_ref: ModuleRef,
        cmpd_ref: CompoundTypeRef,
    ) -> Result<CompoundTypeRef, LinkError> {
        if let Some(linked_ref) = self
            .module_ref_map
            .get(&module_ref)
            .unwrap()
            .cmpd_mapping
            .get(&cmpd_ref)
            .copied()
        {
            return Ok(linked_ref);
        }

        let link_type = |linker: &mut Self, ty: Type| {
            if !ty.is_compound() {
                return Ok(ty);
            }

            let Type::Compound(cmpd_ref) = ty else {
                unreachable!()
            };
            linker.link_cmpd(module_ref, cmpd_ref).map(Type::Compound)
        };

        let cmpd = self.modules[&module_ref]
            .ctx
            .with_ty_store(|s| s.resolve_compound(cmpd_ref).clone());
        let linked_cmpd = match cmpd {
            CompoundType::Array { elem, len } => {
                let linked_ty = link_type(self, elem)?;
                CompoundType::Array {
                    elem: linked_ty,
                    len,
                }
            }

            CompoundType::Ptr(ty) => {
                let linked_ty = link_type(self, ty)?;
                CompoundType::Ptr(linked_ty)
            }

            CompoundType::Func { mut args, ret_ty } => {
                for arg in args.iter_mut() {
                    *arg = link_type(self, *arg)?;
                }
                let linked_ret_ty = link_type(self, ret_ty)?;

                CompoundType::Func {
                    args,
                    ret_ty: linked_ret_ty,
                }
            }

            CompoundType::Struct(mut s_data) => {
                let (linked_cmpd_ref, linked_struct_data) =
                    match self.builder.lookup_struct(&s_data.name) {
                        Some(cmpd_ref) => {
                            let CompoundType::Struct(s_data) = self
                                .builder
                                .ctx
                                .with_ty_store(|store| store.resolve_compound(cmpd_ref).clone())
                            else {
                                unreachable!()
                            };

                            (cmpd_ref, Some(s_data))
                        }
                        None => {
                            // Make a new struct type and declare it.
                            // We perform this before mapping the fields to handle
                            // (indirect) recursive types.
                            let s_data = StructData {
                                name: s_data.name.clone(),
                                fields: vec![],
                                packed: s_data.packed,
                            };
                            (
                                self.builder.make_compound(CompoundType::Struct(s_data)),
                                None,
                            )
                        }
                    };

                // Map the struct type before mapping the fields for (indirect) recursive
                // struct types.
                self.module_ref_map
                    .get_mut(&module_ref)
                    .unwrap()
                    .map_cmpd(cmpd_ref, linked_cmpd_ref);

                // Update the field.
                for field in s_data.fields.iter_mut() {
                    *field = link_type(self, *field)?;
                }

                if let Some(linked_s_data) = linked_struct_data {
                    if s_data != linked_s_data {
                        return Err(LinkError::InconsistentStructType {
                            name: s_data.name.clone(),
                        });
                    }
                } else {
                    self.builder
                        .update_struct_fields(&s_data.name, &s_data.fields);
                }

                return Ok(linked_cmpd_ref);
            }
        };

        let linked_cmpd_ref = self.builder.make_compound(linked_cmpd);
        self.module_ref_map
            .get_mut(&module_ref)
            .unwrap()
            .map_cmpd(cmpd_ref, linked_cmpd_ref);
        Ok(linked_cmpd_ref)
    }

    /// Links a global variable reference in the source module to a linked
    /// module.
    fn link_gv(
        &mut self,
        module_ref: ModuleRef,
        gv_ref: GlobalVariableRef,
    ) -> Result<GlobalVariableRef, LinkError> {
        let mut gv_data = self.modules[&module_ref]
            .ctx
            .with_gv_store(|s| s.gv_data(gv_ref).clone());

        let mut ref_map = self.module_ref_map.get_mut(&module_ref).unwrap();
        gv_data.ty = ref_map.lookup_type(gv_data.ty);

        let Some(linked_gv_ref) = self.builder.lookup_gv(&gv_data.symbol) else {
            // If the global variable is not defined in the linked module, declare it and
            // make the mapping.
            let linked_gv_ref = self.builder.declare_gv(gv_data);
            ref_map.map_gv(gv_ref, linked_gv_ref);
            return Ok(linked_gv_ref);
        };

        // Consistency check and update the linkage/initializer if needed.
        self.builder.ctx.with_gv_store_mut(|s| {
            let linked_gv_data = s.gv_data(linked_gv_ref);
            // Validate the type.
            if gv_data.ty != linked_gv_data.ty {
                return Err(LinkError::InconsistentGlobalVariable {
                    name: gv_data.symbol.clone(),
                });
            }

            // Validates the linkage and update the linked gv if needed.
            // The allowed combinations are:
            // (SourceLinkage, LinkedLinkage) = (External, Public), (Public, External) or
            // (External, External).
            //
            // Also, in case of LinkedLinkage is External, we need to update it to
            // a Public.
            match (gv_data.linkage, linked_gv_data.linkage) {
                (Linkage::External, Linkage::Public) | (Linkage::External, Linkage::External) => {}
                (Linkage::Public, Linkage::External) => {
                    s.update_linkage(linked_gv_ref, Linkage::Public);
                }
                _ => {
                    return Err(LinkError::InconsistentGlobalVariable {
                        name: gv_data.symbol.clone(),
                    });
                }
            }

            // Updates the initializer if needed.
            // We assume that the verifier already verified that only global variable with
            // Public or External linkage can have an initializer, so we don't need to check
            // it here.
            if let Some(initializer) = gv_data.initializer {
                s.update_initializer(linked_gv_ref, Some(initializer));
            }

            ref_map.map_gv(gv_ref, linked_gv_ref);
            Ok(linked_gv_ref)
        })
    }

    /// Links a function reference in the source module to a linked module.
    fn link_func_ref(
        &mut self,
        module_ref: ModuleRef,
        func_ref: FuncRef,
    ) -> Result<FuncRef, LinkError> {
        let mut ref_map = self.module_ref_map.get_mut(&module_ref).unwrap();

        let sig = self.modules[&module_ref].ctx.func_sig(func_ref, |sig| {
            let name = &sig.name();
            let linkage = sig.linkage();
            let args: Vec<_> = sig
                .args()
                .iter()
                .map(|ty| ref_map.lookup_type(*ty))
                .collect();
            let ret_ty = ref_map.lookup_type(sig.ret_ty());
            Signature::new(name, linkage, &args, ret_ty)
        });

        let Some(linked_func_ref) = self.builder.lookup_func(sig.name()) else {
            // If the function is not defined in the linked module, declare it and
            // make the mapping.
            // Safe unwrap: no existing function with this name, so declare_function won’t conflict.
            let linked_func_ref = self.builder.declare_function(sig).unwrap();
            ref_map.func_mapping.insert(func_ref, linked_func_ref);
            return Ok(linked_func_ref);
        };

        let linked_func_linkage = self.builder.sig(linked_func_ref, |linked_sig| {
            // Validates the signature.
            if sig.args() != linked_sig.args() || sig.ret_ty() != linked_sig.ret_ty() {
                return Err(LinkError::InconsistentFuncSignature {
                    name: sig.name().to_string(),
                });
            }

            Ok(linked_sig.linkage())
        })?;

        match (sig.linkage(), linked_func_linkage) {
            (Linkage::External, Linkage::Public) | (Linkage::External, Linkage::External) => {}
            (Linkage::Public, Linkage::External) => {
                self.builder
                    .ctx
                    .update_func_linkage(linked_func_ref, Linkage::Public);
            }
            _ => {
                return Err(LinkError::InconsistentFuncSignature {
                    name: sig.name().to_string(),
                });
            }
        }

        ref_map.func_mapping.insert(func_ref, linked_func_ref);
        Ok(linked_func_ref)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Linkage, Object, ObjectName, builder::test_util::test_module_builder, types::Type,
    };

    #[test]
    fn test_linker_conflicting_function_signature_should_fail() {
        let mod1 = {
            let builder = test_module_builder();
            let sig = Signature::new("foo", Linkage::Public, &[Type::I32], Type::I32);
            builder.declare_function(sig).unwrap();
            builder.build()
        };

        let mod2 = {
            let builder = test_module_builder();
            let sig = Signature::new("foo", Linkage::Public, &[Type::I64], Type::I64);
            builder.declare_function(sig).unwrap();
            builder.build()
        };

        let result = LinkedModule::link(vec![mod1, mod2]);

        match result {
            Err(LinkError::InconsistentFuncSignature { name }) => {
                assert_eq!(name, "foo");
            }
            _ => panic!("Expected InconsistentFuncSignature error for function 'foo'"),
        }
    }

    #[test]
    fn test_linker_duplicate_public_functions_should_fail() {
        let sig = Signature::new("foo", Linkage::Public, &[Type::I32], Type::I32);

        let mod1 = {
            let builder = test_module_builder();
            builder.declare_function(sig.clone()).unwrap();
            builder.build()
        };

        let mod2 = {
            let builder = test_module_builder();
            builder.declare_function(sig).unwrap();
            builder.build()
        };

        let result = LinkedModule::link(vec![mod1, mod2]);

        assert!(
            matches!(result, Err(LinkError::InconsistentFuncSignature { name }) if name == "foo"),
            "Expected InconsistentFuncSignature error on duplicate Public function 'foo'"
        );
    }

    #[test]
    fn test_linker_duplicate_private_should_fail() {
        let sig = Signature::new("foo", Linkage::Private, &[Type::I32], Type::I32);

        let mod1 = {
            let builder = test_module_builder();
            builder.declare_function(sig.clone()).unwrap();
            builder.build()
        };

        let mod2 = {
            let builder = test_module_builder();
            builder.declare_function(sig).unwrap();
            builder.build()
        };

        let result = LinkedModule::link(vec![mod1, mod2]);

        assert!(
            matches!(result, Err(LinkError::InconsistentFuncSignature { name }) if name == "foo"),
            "Expected InconsistentFuncSignature error on duplicate Private function 'foo'"
        );
    }

    #[test]
    fn test_linker_public_and_external_should_succeed() {
        let sig_public = Signature::new("foo", Linkage::Public, &[Type::I32], Type::I32);
        let sig_external = Signature::new("foo", Linkage::External, &[Type::I32], Type::I32);

        let mod1 = {
            let builder = test_module_builder();
            builder.declare_function(sig_public).unwrap();
            builder.build()
        };

        let mod2 = {
            let builder = test_module_builder();
            builder.declare_function(sig_external).unwrap();
            builder.build()
        };

        let result = LinkedModule::link(vec![mod1, mod2]);
        assert!(
            result.is_ok(),
            "Expected successful link for Public + External"
        );
    }

    #[test]
    fn test_linker_different_names_should_succeed() {
        let sig1 = Signature::new("foo_mod1", Linkage::Private, &[Type::I32], Type::I32);
        let sig2 = Signature::new("foo_mod2", Linkage::Private, &[Type::I32], Type::I32);

        let mod1 = {
            let builder = test_module_builder();
            builder.declare_function(sig1).unwrap();
            builder.build()
        };

        let mod2 = {
            let builder = test_module_builder();
            builder.declare_function(sig2).unwrap();
            builder.build()
        };

        let result = LinkedModule::link(vec![mod1, mod2]);
        assert!(
            result.is_ok(),
            "Expected successful link for different function names"
        );
    }

    #[test]
    fn test_linker_duplicate_objects_should_fail() {
        let mod1 = {
            let mut builder = test_module_builder();
            builder
                .declare_object(Object {
                    name: ObjectName("Factory".into()),
                    sections: vec![],
                })
                .unwrap();
            builder.build()
        };

        let mod2 = {
            let mut builder = test_module_builder();
            builder
                .declare_object(Object {
                    name: ObjectName("Factory".into()),
                    sections: vec![],
                })
                .unwrap();
            builder.build()
        };

        let result = LinkedModule::link(vec![mod1, mod2]);
        assert!(
            matches!(result, Err(LinkError::DuplicateObjectDefinition { name }) if name == "Factory"),
            "Expected DuplicateObjectDefinition error for object 'Factory'"
        );
    }
}
