use std::{
    collections::{HashMap, HashSet},
    ops::Index,
};

use cranelift_codegen::ir::{self as clif, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{
    Function, Immediate, Type, U256, Value, ValueId,
    inst::{InstId, inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
};

use super::{
    Limbs, constant_limbs, scalar_constant, sonatina_scalar_type_to_clif_or_err,
    sonatina_type_to_clif_or_err, uses_indirect_value_representation,
};

/// The Cranelift values of translated Sonatina values. An i256 value is
/// four i64 limbs, or two `i64x2` halves when it is only copied; every other
/// value is one Cranelift value, and an aggregate's is the address of its
/// storage.
#[derive(Default)]
pub(super) struct ValueMap {
    scalars: HashMap<ValueId, clif::Value>,
    limbs: HashMap<ValueId, Limbs>,
    halves: HashMap<ValueId, [clif::Value; 2]>,
    copies: HashSet<ValueId>,
}

impl ValueMap {
    /// A map that moves the i256 values `function` only stores as two vector
    /// halves when `vectors` is set.
    pub fn new(function: &Function, vectors: bool) -> Self {
        let copies = if vectors {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .flat_map(|inst| function.dfg.inst_results(inst).iter().copied())
                .filter(|&value| {
                    function.dfg.value_ty(value) == Type::I256
                        && function.dfg.users_num(value) > 0
                        && function
                            .dfg
                            .users(value)
                            .all(|&user| stores_only_value(function, user, value))
                })
                .collect()
        } else {
            HashSet::new()
        };
        Self {
            copies,
            ..Self::default()
        }
    }

    pub fn insert(&mut self, value: ValueId, translated: clif::Value) {
        self.scalars.insert(value, translated);
    }

    pub fn insert_limbs(&mut self, value: ValueId, limbs: Limbs) {
        self.limbs.insert(value, limbs);
    }

    pub fn insert_halves(&mut self, value: ValueId, halves: [clif::Value; 2]) {
        self.halves.insert(value, halves);
    }

    pub fn get(&self, value: &ValueId) -> Option<&clif::Value> {
        self.scalars.get(value)
    }

    pub fn halves(&self, value: &ValueId) -> Option<[clif::Value; 2]> {
        self.halves.get(value).copied()
    }

    /// Whether every use of the i256 `value` stores it.
    pub fn is_copy(&self, value: ValueId) -> bool {
        self.copies.contains(&value)
    }
}

/// Whether `inst` uses `value` only as the value it stores.
fn stores_only_value(function: &Function, inst: InstId, value: ValueId) -> bool {
    match native_inst_set().resolve_inst(function.dfg.inst(inst)) {
        NativeInstKind::ObjStore(store) => *store.value() == value && *store.object() != value,
        NativeInstKind::Mstore(store) => *store.value() == value && *store.addr() != value,
        NativeInstKind::InsertValue(insert) => {
            *insert.value() == value && *insert.dest() != value && *insert.idx() != value
        }
        _ => false,
    }
}

impl Index<&ValueId> for ValueMap {
    type Output = clif::Value;

    fn index(&self, value: &ValueId) -> &clif::Value {
        &self.scalars[value]
    }
}

pub(super) fn insert_clif_results(
    function: &Function,
    inst_id: InstId,
    values: impl IntoIterator<Item = clif::Value>,
    value_map: &mut ValueMap,
) {
    for (ir_result, clif_result) in function.dfg.inst_results(inst_id).iter().zip(values) {
        value_map.insert(*ir_result, clif_result);
    }
}

pub(super) fn resolve_value(
    function: &Function,
    value_id: ValueId,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    if let Some(&clif_val) = value_map.get(&value_id) {
        return Ok(clif_val);
    }
    let value = function.dfg.value(value_id);
    match value {
        Value::Immediate { ty: Type::I256, .. } | Value::Undef { ty: Type::I256 } => Err(format!(
            "i256 value v{} has no single Cranelift value",
            value_id.0
        )),
        Value::Immediate { imm, ty } => match imm {
            Immediate::I128(value) => Ok(scalar_constant(clif::types::I128, *value, builder)),
            _ => {
                let clif_ty = sonatina_scalar_type_to_clif_or_err(*ty)?;
                let i64_val = imm_to_i64(imm)?;
                let val = builder.ins().iconst(clif_ty, i64_val);
                Ok(val)
            }
        },
        Value::Undef { ty } => {
            let ctx = function.ctx();
            if uses_indirect_value_representation(ctx, *ty) {
                // Aggregate consumers zero their destination (`store_indirect`)
                // or a slot of their own (`resolve_operand`).
                return Err(format!(
                    "undef aggregate v{} needs a storage-aware consumer",
                    value_id.0
                ));
            }
            // This is a backend choice for surviving undef values, not an IR
            // promise that optimizations must preserve zero.
            let pointer_ty = sonatina_scalar_type_to_clif_or_err(ctx.type_layout.pointer_repl())?;
            let clif_ty = sonatina_type_to_clif_or_err(*ty, pointer_ty)?;
            Ok(scalar_constant(clif_ty, 0, builder))
        }
        Value::Global { gv, .. } => Err(format!(
            "unresolved global address {gv:?} at v{}",
            value_id.0
        )),
        Value::Arg { .. } | Value::Inst { .. } => {
            Err(format!("unresolved SSA value v{}: {value:?}", value_id.0))
        }
    }
}

/// The limbs of an i256 value. Undef reads as zero, like other undef values.
pub(super) fn resolve_i256(
    function: &Function,
    value_id: ValueId,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<Limbs, String> {
    if let Some(&limbs) = value_map.limbs.get(&value_id) {
        return Ok(limbs);
    }
    match function.dfg.value(value_id) {
        Value::Immediate {
            imm: Immediate::I256(imm),
            ..
        } => Ok(constant_limbs(imm.to_u256(), builder)),
        Value::Undef { ty: Type::I256 } => Ok(constant_limbs(U256::zero(), builder)),
        value => Err(format!("unresolved i256 value v{}: {value:?}", value_id.0)),
    }
}

fn imm_to_i64(imm: &Immediate) -> Result<i64, String> {
    match imm {
        Immediate::I1(b) => Ok(*b as i64),
        Immediate::I8(v) => Ok(*v as i64),
        Immediate::I16(v) => Ok(*v as i64),
        Immediate::I32(v) => Ok(*v as i64),
        Immediate::I64(v) => Ok(*v),
        _ => Err(format!("unsupported immediate type for cranelift: {imm:?}")),
    }
}
