use std::collections::HashMap;

use cranelift_codegen::ir::{self as clif, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, DataId, Module as ClifModule};
use sonatina_ir::{
    GlobalVariableRef, Immediate, Type, global_variable::GvInitializer, module::ModuleCtx,
    types::CompoundType,
};

use super::{
    aggregate_elem_offset, translate_linkage, value_storage_alignment, value_storage_size,
};

pub(super) type GlobalDataMap = HashMap<GlobalVariableRef, DataId>;

pub(super) fn define_globals(
    ctx: &ModuleCtx,
    module: &mut impl ClifModule,
) -> Result<GlobalDataMap, String> {
    ctx.with_gv_store(|globals| {
        let mut data_ids = GlobalDataMap::new();
        for global in globals.all_gv_refs() {
            let data = globals.gv_data(global);
            let name = &data.symbol;
            let id = module
                .declare_data(name, translate_linkage(data.linkage), !data.is_const, false)
                .map_err(|error| format!("failed to declare global {name}: {error}"))?;
            data_ids.insert(global, id);
            if data.linkage.is_external() {
                if data.initializer.is_some() {
                    return Err(format!(
                        "external global {name} must not have an initializer"
                    ));
                }
                continue;
            }
            let mut description = DataDescription::new();
            description.set_align(
                value_storage_alignment(data.ty, ctx)
                    .map_err(|error| format!("global {name}: {error}"))?,
            );
            let size = value_storage_size(data.ty, ctx)
                .map_err(|error| format!("global {name}: {error}"))?
                as usize;
            if let Some(init) = &data.initializer {
                // Native padding has a deterministic value too. Initializers
                // write fields at their native offsets, after enum legalization.
                let mut bytes = vec![0; size];
                serialize_initializer(init, data.ty, &mut bytes, ctx)
                    .map_err(|error| format!("global {name}: {error}"))?;
                description.define(bytes.into_boxed_slice());
            } else {
                description.define_zeroinit(size);
            }
            module
                .define_data(id, &description)
                .map_err(|error| format!("failed to define global {name}: {error}"))?;
        }
        Ok(data_ids)
    })
}

pub(super) fn global_address(
    global: GlobalVariableRef,
    data_ids: &GlobalDataMap,
    module: &mut impl ClifModule,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let data = data_ids
        .get(&global)
        .ok_or_else(|| format!("undeclared native global {global:?}"))?;
    let reference = module.declare_data_in_func(*data, builder.func);
    Ok(builder
        .ins()
        .symbol_value(module.target_config().pointer_type(), reference))
}

fn serialize_initializer(
    init: &GvInitializer,
    ty: Type,
    bytes: &mut [u8],
    ctx: &ModuleCtx,
) -> Result<(), String> {
    match init {
        GvInitializer::Immediate(imm) => {
            if matches!(imm, Immediate::EnumTag { .. }) {
                return Err("enum-tag initializer survived legalization".into());
            }
            if imm.ty() != ty && !(ty.is_pointer(ctx) && imm.ty() == ctx.type_layout.pointer_repl())
            {
                return Err(format!(
                    "initializer type mismatch: expected {ty:?}, found {:?}",
                    imm.ty()
                ));
            }
            let words = imm.zext(Type::I256).as_i256().to_u256().to_little_endian();
            bytes.copy_from_slice(&words[..bytes.len()]);
        }
        GvInitializer::Array(elements) => {
            let Some(CompoundType::Array { elem, len }) = ty.resolve_compound(ctx) else {
                return Err(format!("array initializer used for {ty:?}"));
            };
            if elements.len() != len {
                return Err(format!(
                    "array initializer length mismatch: expected {len}, found {}",
                    elements.len()
                ));
            }
            let size = value_storage_size(elem, ctx)? as usize;
            for (index, init) in elements.iter().enumerate() {
                let start = index * size;
                serialize_initializer(init, elem, &mut bytes[start..start + size], ctx)?;
            }
        }
        GvInitializer::Struct(fields) => {
            let Some(CompoundType::Struct(data)) = ty.resolve_compound(ctx) else {
                return Err(format!("struct initializer used for {ty:?}"));
            };
            if fields.len() != data.fields.len() {
                return Err(format!(
                    "struct initializer field count mismatch: expected {}, found {}",
                    data.fields.len(),
                    fields.len()
                ));
            }
            for (index, (init, field)) in fields.iter().zip(data.fields).enumerate() {
                let (offset, _) = aggregate_elem_offset(ctx, ty, index)?;
                let start = offset as usize;
                let size = value_storage_size(field, ctx)? as usize;
                serialize_initializer(init, field, &mut bytes[start..start + size], ctx)?;
            }
        }
    }
    Ok(())
}
