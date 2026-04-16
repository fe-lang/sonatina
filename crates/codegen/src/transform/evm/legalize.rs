use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, Module, Type, U256, Value, ValueId,
    inst::{
        BinaryInstKind, UnaryInstKind,
        arith::{
            self, Add, Mul, Neg, Saddsat, Sdiv, Smod, Smulsat, Ssubsat, Sub, Uaddsat, Udiv, Umod,
            Umulsat, Usubsat,
        },
        cast::{self, Bitcast, IntToPtr, PtrToInt},
        cmp::{self, Eq, IsZero, Ne, Sgt, Slt},
        data::{Alloca, MemAllocDynamic, Mload, Mstore},
        downcast,
        evm::{
            EvmMalloc, EvmSaddsat, EvmSdiv, EvmSdivo, EvmSmod, EvmSmodo, EvmSmulsat, EvmSsubsat,
            EvmUaddsat, EvmUdiv, EvmUdivo, EvmUmod, EvmUmodo, EvmUmulsat, EvmUsubsat,
        },
        logic::{self, And, Or, Xor},
    },
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeRef, StructData},
};
use sonatina_triple::Architecture;

use crate::optim::adce::AdceSolver;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScalarWidth {
    Bool,
    Narrow(u16),
    Full256,
}

impl ScalarWidth {
    fn legalized_ty(self) -> Type {
        match self {
            Self::Bool => Type::I1,
            Self::Narrow(_) | Self::Full256 => Type::I256,
        }
    }
}

#[derive(Default)]
struct TypeLegalizer {
    compound_map: FxHashMap<CompoundTypeRef, CompoundTypeRef>,
}

impl TypeLegalizer {
    fn legalize_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type {
        match ty {
            Type::I1 => Type::I1,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => Type::I256,
            Type::I256 | Type::Unit => ty,
            Type::EnumTag(_) => {
                panic!("enum tags must be lowered before EVM type legalization");
            }
            Type::Compound(compound) => Type::Compound(self.legalize_compound(ctx, compound)),
        }
    }

    fn legalize_compound(&mut self, ctx: &ModuleCtx, compound: CompoundTypeRef) -> CompoundTypeRef {
        if let Some(&mapped) = self.compound_map.get(&compound) {
            return mapped;
        }

        let current = ctx.with_ty_store(|store| store.resolve_compound(compound).clone());
        self.compound_map.insert(compound, compound);

        match current {
            CompoundType::Array { elem, len } => {
                let elem = self.legalize_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_array(elem, len) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::Ptr(elem) => {
                let elem = self.legalize_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_ptr(elem) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::ObjRef(_) => {
                panic!("object references must be lowered before EVM type legalization");
            }
            CompoundType::ConstRef(elem) => {
                let elem = self.legalize_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_const_ref(elem) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::Enum(_) => {
                panic!("enum types must be lowered before EVM type legalization");
            }
            CompoundType::Func { args, ret_tys } => {
                let args: SmallVec<[Type; 8]> = args
                    .iter()
                    .map(|&arg| self.legalize_type(ctx, arg))
                    .collect();
                let ret_tys: SmallVec<[Type; 2]> = ret_tys
                    .iter()
                    .map(|&ret| self.legalize_type(ctx, ret))
                    .collect();
                let mapped =
                    ctx.with_ty_store_mut(|store| match store.make_func(&args, &ret_tys) {
                        Type::Compound(mapped) => mapped,
                        _ => unreachable!(),
                    });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::Struct(StructData { name, fields, .. }) => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|&field| self.legalize_type(ctx, field))
                    .collect();
                ctx.with_ty_store_mut(|store| store.update_struct_fields(&name, &fields));
                compound
            }
        }
    }
}

fn scalar_width_for_type(ctx: &ModuleCtx, ty: Type) -> Option<ScalarWidth> {
    match ty {
        Type::I1 => Some(ScalarWidth::Bool),
        Type::I8 => Some(ScalarWidth::Narrow(8)),
        Type::I16 => Some(ScalarWidth::Narrow(16)),
        Type::I32 => Some(ScalarWidth::Narrow(32)),
        Type::I64 => Some(ScalarWidth::Narrow(64)),
        Type::I128 => Some(ScalarWidth::Narrow(128)),
        Type::I256 => Some(ScalarWidth::Full256),
        Type::EnumTag(_) => None,
        Type::Compound(_) if ty.is_pointer(ctx) => Some(ScalarWidth::Full256),
        Type::Compound(_) | Type::Unit => None,
    }
}

fn legalize_immediate(imm: sonatina_ir::Immediate) -> sonatina_ir::Immediate {
    match imm.ty() {
        Type::I1 => imm,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => imm.zext(Type::I256),
        Type::I256 => imm,
        Type::EnumTag(_) => unreachable!(),
        Type::Compound(_) | Type::Unit => unreachable!(),
    }
}

fn low_mask(bits: u16) -> U256 {
    match bits {
        0 => U256::zero(),
        256 => !U256::zero(),
        bits => (U256::one() << usize::from(bits)) - U256::one(),
    }
}

fn low_mask_bits(func: &Function, value: ValueId) -> Option<u16> {
    let imm = func.dfg.value_imm(value)?;
    let ones = imm.as_i256().to_u256();
    [1u16, 8, 16, 32, 64, 128, 256]
        .into_iter()
        .find(|&bits| ones == low_mask(bits))
}

pub(crate) fn legalize_evm_section(module: &Module, funcs: &[FuncRef]) {
    assert!(
        matches!(module.ctx.triple.architecture, Architecture::Evm),
        "EVM legalization requires an EVM module"
    );
    let mut types = TypeLegalizer::default();

    for &func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        let args: SmallVec<[Type; 8]> = sig
            .args()
            .iter()
            .map(|&arg| types.legalize_type(&module.ctx, arg))
            .collect();
        let ret_tys: SmallVec<[Type; 2]> = sig
            .ret_tys()
            .iter()
            .map(|&ret| types.legalize_type(&module.ctx, ret))
            .collect();

        module
            .ctx
            .declared_funcs
            .get_mut(&func)
            .expect("missing function signature")
            .clone_from(&sonatina_ir::Signature::new(
                sig.name(),
                sig.linkage(),
                &args,
                &ret_tys,
            ));
    }

    for &func in funcs {
        module.func_store.modify(func, |function| {
            let mut legalizer = FunctionLegalizer::new(function, &module.ctx, &mut types);
            legalizer.run();
        });
    }
}

struct FunctionLegalizer<'a> {
    ctx: &'a ModuleCtx,
    func: &'a mut Function,
    types: &'a mut TypeLegalizer,
    provenance: SecondaryMap<ValueId, Option<ScalarWidth>>,
}

impl<'a> FunctionLegalizer<'a> {
    fn new(func: &'a mut Function, ctx: &'a ModuleCtx, types: &'a mut TypeLegalizer) -> Self {
        let mut provenance = SecondaryMap::new();
        let values: Vec<_> = func.dfg.value_ids().collect();
        for value in values {
            provenance[value] = scalar_width_for_type(ctx, func.dfg.value_ty(value));
        }

        Self {
            ctx,
            func,
            types,
            provenance,
        }
    }

    fn run(&mut self) {
        self.legalize_value_types();
        self.legalize_instructions();
        self.func.rebuild_users();
        AdceSolver::new().run(self.func);
    }

    fn legalize_value_types(&mut self) {
        let values: Vec<_> = self.func.dfg.value_ids().collect();
        for value in values {
            let replacement = match self.func.dfg.value(value).clone() {
                Value::Immediate { imm, .. } => Value::Immediate {
                    imm: legalize_immediate(imm),
                    ty: self.types.legalize_type(self.ctx, imm.ty()),
                },
                Value::Inst {
                    inst,
                    result_idx,
                    ty,
                    ..
                } => Value::Inst {
                    inst,
                    result_idx,
                    ty: self.types.legalize_type(self.ctx, ty),
                },
                Value::Arg { idx, ty } => Value::Arg {
                    idx,
                    ty: self.types.legalize_type(self.ctx, ty),
                },
                Value::Global { gv, ty } => Value::Global {
                    gv,
                    ty: self.types.legalize_type(self.ctx, ty),
                },
                Value::Undef { ty } => Value::Undef {
                    ty: self.types.legalize_type(self.ctx, ty),
                },
            };
            self.func.dfg.values[value] = replacement;
        }

        self.func.dfg.immediates.clear();
        for value in self.func.dfg.value_ids().collect::<Vec<_>>() {
            if let Value::Immediate { imm, .. } = self.func.dfg.value(value).clone() {
                self.func.dfg.immediates.insert(imm, value);
            }
        }
    }

    fn legalize_instructions(&mut self) {
        let blocks: Vec<_> = self.func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = self.func.layout.iter_inst(block).collect();
            for inst in insts {
                if !self.func.dfg.has_inst(inst) || !self.func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.legalize_inst(inst);
            }
        }
    }

    fn legalize_inst(&mut self, inst: InstId) {
        let is = self.evm_inst_set();

        if let Some((lhs, rhs)) =
            downcast::<&Uaddsat>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_uaddsat(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Uaddo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_uaddo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&Saddsat>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_saddsat(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Saddo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_overflow_binary(inst, lhs, rhs, SignedOverflowKind::Add);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&Usubsat>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_usubsat(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Usubo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_usubo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&Ssubsat>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_ssubsat(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Ssubo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_overflow_binary(inst, lhs, rhs, SignedOverflowKind::Sub);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&Umulsat>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_umulsat(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Umulo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_umulo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&Smulsat>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_smulsat(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Smulo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_overflow_binary(inst, lhs, rhs, SignedOverflowKind::Mul);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&EvmUdivo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_evm_udivo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&EvmSdivo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_evm_sdivo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&EvmUmodo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_evm_umodo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&EvmSmodo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_evm_smodo(inst, lhs, rhs);
            return;
        }
        if let Some(arg) = downcast::<&arith::Snego>(is, self.func.dfg.inst(inst)).map(|i| *i.arg())
        {
            self.rewrite_snego(inst, arg);
            return;
        }
        if let Some(arg) = downcast::<&cast::Sext>(is, self.func.dfg.inst(inst)).map(|i| *i.from())
        {
            self.rewrite_sext(inst, arg);
            return;
        }
        if let Some(arg) = downcast::<&cast::Zext>(is, self.func.dfg.inst(inst)).map(|i| *i.from())
        {
            self.rewrite_zext(inst, arg);
            return;
        }
        if let Some(arg) = downcast::<&cast::Trunc>(is, self.func.dfg.inst(inst)).map(|i| *i.from())
        {
            self.rewrite_trunc(inst, arg);
            return;
        }
        if let Some((from, ty)) =
            downcast::<&cast::Bitcast>(is, self.func.dfg.inst(inst)).map(|i| (*i.from(), *i.ty()))
        {
            self.rewrite_bitcast(inst, from, ty);
            return;
        }
        if let Some(from) =
            downcast::<&cast::PtrToInt>(is, self.func.dfg.inst(inst)).map(|i| *i.from())
        {
            self.rewrite_ptr_to_int(inst, from);
            return;
        }
        if let Some((from, ty)) =
            downcast::<&cast::IntToPtr>(is, self.func.dfg.inst(inst)).map(|i| (*i.from(), *i.ty()))
        {
            self.rewrite_int_to_ptr(inst, from, ty);
            return;
        }
        if let Some((addr, ty)) =
            downcast::<&Mload>(is, self.func.dfg.inst(inst)).map(|i| (*i.addr(), *i.ty()))
        {
            self.rewrite_mload(inst, addr, ty);
            return;
        }
        if let Some((addr, value, ty)) = downcast::<&Mstore>(is, self.func.dfg.inst(inst))
            .map(|i| (*i.addr(), *i.value(), *i.ty()))
        {
            self.rewrite_mstore(inst, addr, value, ty);
            return;
        }
        if let Some(ty) = downcast::<&Alloca>(is, self.func.dfg.inst(inst)).map(|i| *i.ty()) {
            self.func.dfg.replace_inst(
                inst,
                Box::new(Alloca::new(
                    self.evm_inst_set(),
                    self.types.legalize_type(self.ctx, ty),
                )),
            );
            return;
        }
        if let Some(size) =
            downcast::<&MemAllocDynamic>(is, self.func.dfg.inst(inst)).map(|i| *i.size())
        {
            self.func
                .dfg
                .replace_inst(inst, Box::new(EvmMalloc::new(self.evm_inst_set(), size)));
            return;
        }

        self.legalize_arith_or_cmp(inst);
    }

    fn legalize_arith_or_cmp(&mut self, inst: InstId) {
        let is = self.evm_inst_set();
        if let Some((lhs, rhs)) =
            downcast::<&Add>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_add(inst, lhs, rhs);
        } else if let Some((lhs, rhs)) =
            downcast::<&Sub>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_sub(inst, lhs, rhs);
        } else if let Some((lhs, rhs)) =
            downcast::<&Mul>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_mul(inst, lhs, rhs);
        } else if let Some(arg) = downcast::<&Neg>(is, self.func.dfg.inst(inst)).map(|i| *i.arg()) {
            self.rewrite_neg(inst, arg);
        } else if let Some((lhs, rhs)) =
            downcast::<&Udiv>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_udiv(inst, lhs, rhs);
        } else if let Some((lhs, rhs)) =
            downcast::<&Sdiv>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_sdiv(inst, lhs, rhs);
        } else if let Some((lhs, rhs)) =
            downcast::<&Umod>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_umod(inst, lhs, rhs);
        } else if let Some((lhs, rhs)) =
            downcast::<&Smod>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_smod(inst, lhs, rhs);
        } else if let Some((bits, value)) =
            downcast::<&arith::Shl>(is, self.func.dfg.inst(inst)).map(|i| (*i.bits(), *i.value()))
        {
            self.rewrite_shl(inst, bits, value);
        } else if let Some((bits, value)) =
            downcast::<&arith::Shr>(is, self.func.dfg.inst(inst)).map(|i| (*i.bits(), *i.value()))
        {
            self.rewrite_shr(inst, bits, value);
        } else if let Some((bits, value)) =
            downcast::<&arith::Sar>(is, self.func.dfg.inst(inst)).map(|i| (*i.bits(), *i.value()))
        {
            self.rewrite_sar(inst, bits, value);
        } else if let Some(arg) =
            downcast::<&logic::Not>(is, self.func.dfg.inst(inst)).map(|i| *i.arg())
        {
            self.rewrite_not(inst, arg);
        } else if let Some((lhs, rhs)) =
            downcast::<&cmp::Slt>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_cmp(inst, lhs, rhs, SignedCmpKind::Lt);
        } else if let Some((lhs, rhs)) =
            downcast::<&cmp::Sgt>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_cmp(inst, lhs, rhs, SignedCmpKind::Gt);
        } else if let Some((lhs, rhs)) =
            downcast::<&cmp::Sge>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_cmp(inst, lhs, rhs, SignedCmpKind::Ge);
        } else if let Some((lhs, rhs)) =
            downcast::<&cmp::Sle>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_cmp(inst, lhs, rhs, SignedCmpKind::Le);
        } else if let Some((lhs, rhs)) =
            downcast::<&cmp::Eq>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            let _ = (lhs, rhs);
        } else if let Some((lhs, rhs)) =
            downcast::<&cmp::Ne>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            let _ = (lhs, rhs);
        }
    }

    fn width_of(&self, value: ValueId) -> Option<ScalarWidth> {
        self.provenance[value]
    }

    fn evm_inst_set(&self) -> &'static sonatina_ir::inst::evm::inst_set::EvmInstSet {
        Evm::new(self.ctx.triple).inst_set()
    }

    fn insert_before<I: Inst>(
        &mut self,
        before: InstId,
        data: I,
        result_tys: &[Type],
        widths: &[Option<ScalarWidth>],
    ) -> SmallVec<[ValueId; 2]> {
        let inst = self.func.dfg.make_inst(data);
        self.func.layout.insert_inst_before(inst, before);
        let mut results = SmallVec::new();
        for (idx, &ty) in result_tys.iter().enumerate() {
            let value = self.func.dfg.make_value(Value::Inst {
                inst,
                result_idx: idx.try_into().expect("too many legalizer results"),
                ty,
            });
            self.func.dfg.append_result(inst, value);
            self.provenance[value] = widths.get(idx).copied().flatten();
            results.push(value);
        }
        results
    }

    fn insert_before_one<I: Inst>(
        &mut self,
        before: InstId,
        data: I,
        ty: Type,
        width: Option<ScalarWidth>,
    ) -> ValueId {
        self.insert_before(before, data, &[ty], &[width])[0]
    }

    fn replace_with_aliases(&mut self, inst: InstId, replacements: &[ValueId]) {
        let results = self.func.dfg.inst_results(inst).to_vec();
        assert_eq!(results.len(), replacements.len());
        for (result, replacement) in results.into_iter().zip(replacements.iter().copied()) {
            self.func.dfg.change_to_alias(result, replacement);
        }
        self.func.layout.remove_inst(inst);
        self.func.erase_inst(inst);
    }

    fn imm_i256(&mut self, value: U256) -> ValueId {
        self.func
            .dfg
            .make_imm_value(sonatina_ir::Immediate::from_i256(
                I256::from(value),
                Type::I256,
            ))
    }

    fn imm_for_width(&mut self, value: U256, width: ScalarWidth) -> ValueId {
        let ty = width.legalized_ty();
        self.func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(value), ty))
    }

    fn zero_i256(&mut self) -> ValueId {
        self.imm_i256(U256::zero())
    }

    fn one_i256(&mut self) -> ValueId {
        self.imm_i256(U256::one())
    }

    fn mask_value(&mut self, bits: u16) -> ValueId {
        let mask = low_mask(bits);
        self.imm_i256(mask)
    }

    fn shift_value(&mut self, bits: u16) -> ValueId {
        self.imm_i256(U256::from(bits))
    }

    fn scalar_type_for_width(width: ScalarWidth) -> Type {
        match width {
            ScalarWidth::Bool => Type::I1,
            ScalarWidth::Narrow(8) => Type::I8,
            ScalarWidth::Narrow(16) => Type::I16,
            ScalarWidth::Narrow(32) => Type::I32,
            ScalarWidth::Narrow(64) => Type::I64,
            ScalarWidth::Narrow(128) => Type::I128,
            ScalarWidth::Narrow(bits) => panic!("unsupported scalar width {bits}"),
            ScalarWidth::Full256 => Type::I256,
        }
    }

    fn saturating_scalar_type(&self, inst: InstId) -> Type {
        let [result] = self.func.dfg.inst_results(inst) else {
            panic!("saturating op must have exactly one result");
        };
        let width = self
            .width_of(*result)
            .expect("missing saturating result width");
        assert_ne!(width, ScalarWidth::Bool, "saturating ops do not support i1");
        Self::scalar_type_for_width(width)
    }

    fn replace_with_normalized_narrow_signed_sat<I: Inst>(
        &mut self,
        inst: InstId,
        data: I,
        width: ScalarWidth,
    ) {
        let raw = self.insert_before_one(inst, data, Type::I256, Some(ScalarWidth::Full256));
        let result = self.normalize_and_retag_width(inst, raw, width);
        self.replace_with_aliases(inst, &[result]);
    }

    fn min_value_for_width(&mut self, width: ScalarWidth) -> ValueId {
        match width {
            ScalarWidth::Bool => self.imm_for_width(U256::one(), width),
            ScalarWidth::Narrow(bits) => {
                self.imm_for_width(U256::one() << usize::from(bits - 1), width)
            }
            ScalarWidth::Full256 => self.imm_i256(U256::one() << 255),
        }
    }

    fn neg_one_for_width(&mut self, width: ScalarWidth) -> ValueId {
        match width {
            ScalarWidth::Bool => self.imm_for_width(U256::one(), width),
            ScalarWidth::Narrow(bits) => {
                self.imm_for_width((U256::one() << usize::from(bits)) - U256::one(), width)
            }
            ScalarWidth::Full256 => self.imm_i256(!U256::zero()),
        }
    }

    fn value_has_width(&self, value: ValueId, width: ScalarWidth) -> bool {
        self.func.dfg.value_ty(value) == width.legalized_ty() && self.width_of(value) == Some(width)
    }

    fn retag_i256_width(&mut self, before: InstId, value: ValueId, width: ScalarWidth) -> ValueId {
        debug_assert_ne!(
            width,
            ScalarWidth::Bool,
            "bool values must be retagged through retag_width"
        );
        if self.value_has_width(value, width) {
            return value;
        }

        match self.func.dfg.value_ty(value) {
            Type::I1 => self.insert_before_one(
                before,
                Bitcast::new(self.evm_inst_set(), value, Type::I256),
                Type::I256,
                Some(width),
            ),
            Type::I256 => {
                let zero = self.zero_i256();
                self.insert_before_one(
                    before,
                    Or::new(self.evm_inst_set(), value, zero),
                    Type::I256,
                    Some(width),
                )
            }
            ty => panic!("cannot retag {ty:?} as {:?}", width.legalized_ty()),
        }
    }

    fn retag_width(&mut self, before: InstId, value: ValueId, width: ScalarWidth) -> ValueId {
        match width {
            ScalarWidth::Bool if self.value_has_width(value, ScalarWidth::Bool) => value,
            ScalarWidth::Bool => {
                debug_assert_eq!(
                    self.func.dfg.value_ty(value),
                    Type::I1,
                    "bool retagging requires a normalized i1 value"
                );
                let zero = self.imm_for_width(U256::zero(), ScalarWidth::Bool);
                self.insert_before_one(
                    before,
                    Or::new(self.evm_inst_set(), value, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
            width @ (ScalarWidth::Narrow(_) | ScalarWidth::Full256) => {
                self.retag_i256_width(before, value, width)
            }
        }
    }

    fn zero_extend_to_i256(&mut self, before: InstId, value: ValueId) -> ValueId {
        self.retag_i256_width(before, value, ScalarWidth::Full256)
    }

    fn sign_extend_to_i256(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        match width {
            ScalarWidth::Full256 => self.retag_i256_width(before, value, ScalarWidth::Full256),
            ScalarWidth::Bool => {
                let widened = self.zero_extend_to_i256(before, value);
                let zero = self.zero_i256();
                self.insert_before_one(
                    before,
                    Sub::new(self.evm_inst_set(), zero, widened),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                )
            }
            ScalarWidth::Narrow(bits) => {
                let shift = self.shift_value(256 - bits);
                let shl = self.insert_before_one(
                    before,
                    arith::Shl::new(self.evm_inst_set(), shift, value),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                self.insert_before_one(
                    before,
                    arith::Sar::new(self.evm_inst_set(), shift, shl),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                )
            }
        }
    }

    fn bool_to_i256(&mut self, before: InstId, value: ValueId) -> ValueId {
        self.zero_extend_to_i256(before, value)
    }

    fn bool_to_mask_i256(&mut self, before: InstId, value: ValueId) -> ValueId {
        let flag = self.bool_to_i256(before, value);
        let zero = self.zero_i256();
        self.insert_before_one(
            before,
            Sub::new(self.evm_inst_set(), zero, flag),
            Type::I256,
            Some(ScalarWidth::Full256),
        )
    }

    fn select_i256(
        &mut self,
        before: InstId,
        keep: ValueId,
        replace: ValueId,
        flag: ValueId,
    ) -> ValueId {
        let mask = self.bool_to_mask_i256(before, flag);
        let delta = self.insert_before_one(
            before,
            Xor::new(self.evm_inst_set(), keep, replace),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let masked = self.insert_before_one(
            before,
            And::new(self.evm_inst_set(), delta, mask),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        self.insert_before_one(
            before,
            Xor::new(self.evm_inst_set(), keep, masked),
            Type::I256,
            Some(ScalarWidth::Full256),
        )
    }

    fn sign_mask_i256(&mut self, before: InstId, value: ValueId) -> ValueId {
        let shift = self.shift_value(255);
        self.insert_before_one(
            before,
            arith::Sar::new(self.evm_inst_set(), shift, value),
            Type::I256,
            Some(ScalarWidth::Full256),
        )
    }

    fn normalize_bits_for_width(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        match width {
            ScalarWidth::Full256 => value,
            ScalarWidth::Narrow(bits) => {
                if self.value_fits_narrow_locally(value, bits) {
                    return value;
                }

                let mask = self.mask_value(bits);
                self.insert_before_one(
                    before,
                    And::new(self.evm_inst_set(), value, mask),
                    Type::I256,
                    Some(ScalarWidth::Narrow(bits)),
                )
            }
            ScalarWidth::Bool => {
                if self.value_is_local_bool(value) {
                    return value;
                }

                let one = self.one_i256();
                let masked = self.insert_before_one(
                    before,
                    And::new(self.evm_inst_set(), value, one),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let zero = self.zero_i256();
                self.insert_before_one(
                    before,
                    Ne::new(self.evm_inst_set(), masked, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
        }
    }

    fn normalize_and_retag_width(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        let normalized = self.normalize_bits_for_width(before, value, width);
        let result = self.retag_width(before, normalized, width);
        debug_assert!(self.value_has_width(result, width));
        result
    }

    fn value_fits_narrow_locally(&self, value: ValueId, target_bits: u16) -> bool {
        if self
            .func
            .dfg
            .value_imm(value)
            .is_some_and(|imm| imm.as_i256().to_u256() & !low_mask(target_bits) == U256::zero())
        {
            return true;
        }

        if self.width_of(value).is_some_and(|width| {
            matches!(width, ScalarWidth::Bool)
                || matches!(width, ScalarWidth::Narrow(bits) if bits <= target_bits)
        }) {
            return true;
        }

        let Value::Inst { inst, .. } = self.func.dfg.value(value) else {
            return false;
        };

        if let Some((lhs, rhs)) =
            downcast::<&logic::And>(self.evm_inst_set(), self.func.dfg.inst(*inst))
                .map(|i| (*i.lhs(), *i.rhs()))
        {
            return low_mask_bits(self.func, lhs)
                .or_else(|| low_mask_bits(self.func, rhs))
                .is_some_and(|bits| bits <= target_bits);
        }

        if let Some((bits, _input)) =
            downcast::<&arith::Shr>(self.evm_inst_set(), self.func.dfg.inst(*inst))
                .map(|i| (*i.bits(), *i.value()))
            && let Some(shift) = self.func.dfg.value_imm(bits)
        {
            let shift = shift.as_i256().to_u256();
            if shift <= U256::from(256u16) {
                let fit_bits = 256u16.saturating_sub(shift.as_usize() as u16);
                return fit_bits <= target_bits;
            }
        }

        if let Some(bitcast) = downcast::<&Bitcast>(self.evm_inst_set(), self.func.dfg.inst(*inst))
        {
            return self.func.dfg.value_ty(*bitcast.from()) == Type::I1 && target_bits >= 1;
        }

        false
    }

    fn value_is_local_bool(&self, value: ValueId) -> bool {
        if self.width_of(value) == Some(ScalarWidth::Bool) {
            return true;
        }

        let Value::Inst { inst, .. } = self.func.dfg.value(value) else {
            return false;
        };
        matches!(
            self.func.dfg.inst(*inst).kind(),
            sonatina_ir::inst::InstClassKind::Binary(
                BinaryInstKind::Eq
                    | BinaryInstKind::Ne
                    | BinaryInstKind::Lt
                    | BinaryInstKind::Gt
                    | BinaryInstKind::Slt
                    | BinaryInstKind::Sgt
                    | BinaryInstKind::Le
                    | BinaryInstKind::Ge
                    | BinaryInstKind::Sle
                    | BinaryInstKind::Sge
            ) | sonatina_ir::inst::InstClassKind::Unary(UnaryInstKind::IsZero)
        )
    }

    fn rewrite_uaddo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let sum_width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing sum width");
        let raw = self.insert_before_one(
            inst,
            Add::new(self.evm_inst_set(), lhs, rhs),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let sum = self.normalize_and_retag_width(inst, raw, sum_width);
        let overflow = match sum_width {
            ScalarWidth::Full256 => self.insert_before_one(
                inst,
                cmp::Lt::new(self.evm_inst_set(), sum, lhs),
                Type::I1,
                Some(ScalarWidth::Bool),
            ),
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => self.insert_before_one(
                inst,
                Ne::new(self.evm_inst_set(), raw, sum),
                Type::I1,
                Some(ScalarWidth::Bool),
            ),
        };
        self.replace_with_aliases(inst, &[sum, overflow]);
    }

    fn rewrite_uaddsat(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing saturating add result width");
        if width == ScalarWidth::Full256 {
            let raw = self.insert_before_one(
                inst,
                Add::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let overflow = self.insert_before_one(
                inst,
                cmp::Lt::new(self.evm_inst_set(), raw, lhs),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let overflow_mask = self.bool_to_mask_i256(inst, overflow);
            let result = self.insert_before_one(
                inst,
                Or::new(self.evm_inst_set(), raw, overflow_mask),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let ty = self.saturating_scalar_type(inst);
        self.func.dfg.replace_inst(
            inst,
            Box::new(EvmUaddsat::new(self.evm_inst_set(), lhs, rhs, ty)),
        );
    }

    fn rewrite_usubo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let sum_width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let raw = self.insert_before_one(
            inst,
            Sub::new(self.evm_inst_set(), lhs, rhs),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let result = self.normalize_and_retag_width(inst, raw, sum_width);
        let overflow = self.insert_before_one(
            inst,
            cmp::Lt::new(self.evm_inst_set(), lhs, rhs),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_usubsat(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing saturating sub result width");
        if width == ScalarWidth::Full256 {
            let raw = self.insert_before_one(
                inst,
                Sub::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let underflow = self.insert_before_one(
                inst,
                cmp::Lt::new(self.evm_inst_set(), lhs, rhs),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let zero = self.zero_i256();
            let result = self.select_i256(inst, raw, zero, underflow);
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let ty = self.saturating_scalar_type(inst);
        self.func.dfg.replace_inst(
            inst,
            Box::new(EvmUsubsat::new(self.evm_inst_set(), lhs, rhs, ty)),
        );
    }

    fn rewrite_umulo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let result_width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let raw = self.insert_before_one(
            inst,
            Mul::new(self.evm_inst_set(), lhs, rhs),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let result = self.normalize_and_retag_width(inst, raw, result_width);
        let overflow = match result_width {
            ScalarWidth::Full256 => {
                let zero = self.zero_i256();
                let rhs_nonzero = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), rhs, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let div_back = self.insert_before_one(
                    inst,
                    EvmUdiv::new(self.evm_inst_set(), result, rhs),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let check = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), div_back, lhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), rhs_nonzero, check),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => self.insert_before_one(
                inst,
                Ne::new(self.evm_inst_set(), raw, result),
                Type::I1,
                Some(ScalarWidth::Bool),
            ),
        };
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_umulsat(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing saturating mul result width");
        if width == ScalarWidth::Full256 {
            let raw = self.insert_before_one(
                inst,
                Mul::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let zero = self.zero_i256();
            let rhs_nonzero = self.insert_before_one(
                inst,
                Ne::new(self.evm_inst_set(), rhs, zero),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let div_back = self.insert_before_one(
                inst,
                EvmUdiv::new(self.evm_inst_set(), raw, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let div_mismatch = self.insert_before_one(
                inst,
                Ne::new(self.evm_inst_set(), div_back, lhs),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let overflow = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), rhs_nonzero, div_mismatch),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let overflow_mask = self.bool_to_mask_i256(inst, overflow);
            let result = self.insert_before_one(
                inst,
                Or::new(self.evm_inst_set(), raw, overflow_mask),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let ty = self.saturating_scalar_type(inst);
        self.func.dfg.replace_inst(
            inst,
            Box::new(EvmUmulsat::new(self.evm_inst_set(), lhs, rhs, ty)),
        );
    }

    fn rewrite_signed_overflow_binary(
        &mut self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
        kind: SignedOverflowKind,
    ) {
        let width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        match width {
            ScalarWidth::Full256 => {
                self.rewrite_full_width_signed_overflow_binary(inst, lhs, rhs, kind)
            }
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                let lhs_ext = self.sign_extend_to_i256(inst, lhs, width);
                let rhs_ext = self.sign_extend_to_i256(inst, rhs, width);
                let raw = match kind {
                    SignedOverflowKind::Add => self.insert_before_one(
                        inst,
                        Add::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                        Type::I256,
                        Some(ScalarWidth::Full256),
                    ),
                    SignedOverflowKind::Sub => self.insert_before_one(
                        inst,
                        Sub::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                        Type::I256,
                        Some(ScalarWidth::Full256),
                    ),
                    SignedOverflowKind::Mul => self.insert_before_one(
                        inst,
                        Mul::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                        Type::I256,
                        Some(ScalarWidth::Full256),
                    ),
                };
                let result = self.normalize_and_retag_width(inst, raw, width);
                let result_ext = self.sign_extend_to_i256(inst, result, width);
                let overflow = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), result_ext, raw),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result, overflow]);
            }
        }
    }

    fn rewrite_saddsat(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing saturating add result width");
        if width == ScalarWidth::Full256 {
            let raw = self.insert_before_one(
                inst,
                Add::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let raw_lhs = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), raw, lhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let raw_rhs = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), raw, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let sign_test = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), raw_lhs, raw_rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let zero = self.zero_i256();
            let overflow = self.insert_before_one(
                inst,
                Slt::new(self.evm_inst_set(), sign_test, zero),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let smax = self.imm_i256((U256::one() << 255) - U256::one());
            let lhs_sign = self.sign_mask_i256(inst, lhs);
            let clamp = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), smax, lhs_sign),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let result = self.select_i256(inst, raw, clamp, overflow);
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let ty = self.saturating_scalar_type(inst);
        self.replace_with_normalized_narrow_signed_sat(
            inst,
            EvmSaddsat::new(self.evm_inst_set(), lhs, rhs, ty),
            width,
        );
    }

    fn rewrite_ssubsat(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing saturating sub result width");
        if width == ScalarWidth::Full256 {
            let raw = self.insert_before_one(
                inst,
                Sub::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let lhs_rhs = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let raw_lhs = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), raw, lhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let sign_test = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), lhs_rhs, raw_lhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let zero = self.zero_i256();
            let overflow = self.insert_before_one(
                inst,
                Slt::new(self.evm_inst_set(), sign_test, zero),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let smax = self.imm_i256((U256::one() << 255) - U256::one());
            let lhs_sign = self.sign_mask_i256(inst, lhs);
            let clamp = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), smax, lhs_sign),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let result = self.select_i256(inst, raw, clamp, overflow);
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let ty = self.saturating_scalar_type(inst);
        self.replace_with_normalized_narrow_signed_sat(
            inst,
            EvmSsubsat::new(self.evm_inst_set(), lhs, rhs, ty),
            width,
        );
    }

    fn rewrite_smulsat(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing saturating mul result width");
        if width == ScalarWidth::Full256 {
            let raw = self.insert_before_one(
                inst,
                Mul::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let zero = self.zero_i256();
            let rhs_nonzero = self.insert_before_one(
                inst,
                Ne::new(self.evm_inst_set(), rhs, zero),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let min = self.imm_i256(U256::one() << 255);
            let neg_one = self.imm_i256(!U256::zero());
            let lhs_is_min = self.insert_before_one(
                inst,
                Eq::new(self.evm_inst_set(), lhs, min),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let rhs_is_min = self.insert_before_one(
                inst,
                Eq::new(self.evm_inst_set(), rhs, min),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let lhs_is_neg_one = self.insert_before_one(
                inst,
                Eq::new(self.evm_inst_set(), lhs, neg_one),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let rhs_is_neg_one = self.insert_before_one(
                inst,
                Eq::new(self.evm_inst_set(), rhs, neg_one),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let left_special = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), lhs_is_min, rhs_is_neg_one),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let right_special = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), rhs_is_min, lhs_is_neg_one),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let special = self.insert_before_one(
                inst,
                Or::new(self.evm_inst_set(), left_special, right_special),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let div_back = self.insert_before_one(
                inst,
                EvmSdiv::new(self.evm_inst_set(), raw, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let div_mismatch = self.insert_before_one(
                inst,
                Ne::new(self.evm_inst_set(), div_back, lhs),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let problem = self.insert_before_one(
                inst,
                Or::new(self.evm_inst_set(), special, div_mismatch),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let overflow = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), rhs_nonzero, problem),
                Type::I1,
                Some(ScalarWidth::Bool),
            );
            let sign_bits = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let smax = self.imm_i256((U256::one() << 255) - U256::one());
            let sign_mask = self.sign_mask_i256(inst, sign_bits);
            let clamp = self.insert_before_one(
                inst,
                Xor::new(self.evm_inst_set(), smax, sign_mask),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let result = self.select_i256(inst, raw, clamp, overflow);
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let ty = self.saturating_scalar_type(inst);
        self.replace_with_normalized_narrow_signed_sat(
            inst,
            EvmSmulsat::new(self.evm_inst_set(), lhs, rhs, ty),
            width,
        );
    }

    fn rewrite_full_width_signed_overflow_binary(
        &mut self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
        kind: SignedOverflowKind,
    ) {
        let result = match kind {
            SignedOverflowKind::Add => self.insert_before_one(
                inst,
                Add::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            ),
            SignedOverflowKind::Sub => self.insert_before_one(
                inst,
                Sub::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            ),
            SignedOverflowKind::Mul => self.insert_before_one(
                inst,
                Mul::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            ),
        };

        let zero = self.zero_i256();
        let overflow = match kind {
            SignedOverflowKind::Add => {
                let sign_lhs = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), lhs, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let sign_rhs = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), rhs, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let sign_res = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), result, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let same_inputs = self.insert_before_one(
                    inst,
                    Eq::new(self.evm_inst_set(), sign_lhs, sign_rhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let changed_sign = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), sign_res, sign_lhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), same_inputs, changed_sign),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
            SignedOverflowKind::Sub => {
                let sign_lhs = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), lhs, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let sign_rhs = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), rhs, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let sign_res = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), result, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let diff_inputs = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), sign_lhs, sign_rhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let changed_sign = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), sign_res, sign_lhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), diff_inputs, changed_sign),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
            SignedOverflowKind::Mul => {
                let rhs_nonzero = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), rhs, zero),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let min = self.imm_i256(U256::one() << 255);
                let neg_one = self.imm_i256(!U256::zero());
                let a_is_min = self.insert_before_one(
                    inst,
                    Eq::new(self.evm_inst_set(), lhs, min),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let b_is_min = self.insert_before_one(
                    inst,
                    Eq::new(self.evm_inst_set(), rhs, min),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let a_is_neg1 = self.insert_before_one(
                    inst,
                    Eq::new(self.evm_inst_set(), lhs, neg_one),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let b_is_neg1 = self.insert_before_one(
                    inst,
                    Eq::new(self.evm_inst_set(), rhs, neg_one),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let left_special = self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), a_is_min, b_is_neg1),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let right_special = self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), b_is_min, a_is_neg1),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let special = self.insert_before_one(
                    inst,
                    Or::new(self.evm_inst_set(), left_special, right_special),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let div_back = self.insert_before_one(
                    inst,
                    EvmSdiv::new(self.evm_inst_set(), result, rhs),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let div_check = self.insert_before_one(
                    inst,
                    Ne::new(self.evm_inst_set(), div_back, lhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let problem = self.insert_before_one(
                    inst,
                    Or::new(self.evm_inst_set(), special, div_check),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), rhs_nonzero, problem),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
        };

        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_snego(&mut self, inst: InstId, arg: ValueId) {
        let width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let zero = self.zero_i256();
        let arg_ext = self.zero_extend_to_i256(inst, arg);
        let raw = self.insert_before_one(
            inst,
            Sub::new(self.evm_inst_set(), zero, arg_ext),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let result = self.normalize_and_retag_width(inst, raw, width);
        let min = self.min_value_for_width(width);
        let overflow = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), arg, min),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_evm_udivo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let result = self.insert_before_one(
            inst,
            EvmUdiv::new(self.evm_inst_set(), lhs, rhs),
            width.legalized_ty(),
            Some(width),
        );
        let zero = self.imm_for_width(U256::zero(), width);
        let overflow = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), rhs, zero),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_evm_umodo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let result = self.insert_before_one(
            inst,
            EvmUmod::new(self.evm_inst_set(), lhs, rhs),
            width.legalized_ty(),
            Some(width),
        );
        let zero = self.imm_for_width(U256::zero(), width);
        let overflow = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), rhs, zero),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_evm_sdivo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let result = match width {
            ScalarWidth::Full256 => self.insert_before_one(
                inst,
                EvmSdiv::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            ),
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                let lhs_ext = self.sign_extend_to_i256(inst, lhs, width);
                let rhs_ext = self.sign_extend_to_i256(inst, rhs, width);
                let raw = self.insert_before_one(
                    inst,
                    EvmSdiv::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                self.normalize_and_retag_width(inst, raw, width)
            }
        };

        let zero = self.imm_for_width(U256::zero(), width);
        let min = self.min_value_for_width(width);
        let neg_one = self.neg_one_for_width(width);
        let div_zero = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), rhs, zero),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        let lhs_is_min = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), lhs, min),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        let rhs_is_neg_one = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), rhs, neg_one),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        let min_overflow = self.insert_before_one(
            inst,
            And::new(self.evm_inst_set(), lhs_is_min, rhs_is_neg_one),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        let overflow = self.insert_before_one(
            inst,
            Or::new(self.evm_inst_set(), div_zero, min_overflow),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_evm_smodo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        let result = match width {
            ScalarWidth::Full256 => self.insert_before_one(
                inst,
                EvmSmod::new(self.evm_inst_set(), lhs, rhs),
                Type::I256,
                Some(ScalarWidth::Full256),
            ),
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                let lhs_ext = self.sign_extend_to_i256(inst, lhs, width);
                let rhs_ext = self.sign_extend_to_i256(inst, rhs, width);
                let raw = self.insert_before_one(
                    inst,
                    EvmSmod::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                self.normalize_and_retag_width(inst, raw, width)
            }
        };
        let zero = self.imm_for_width(U256::zero(), width);
        let overflow = self.insert_before_one(
            inst,
            Eq::new(self.evm_inst_set(), rhs, zero),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
    }

    fn rewrite_add(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => {
                let result = self.insert_before_one(
                    inst,
                    Xor::new(self.evm_inst_set(), lhs, rhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result]);
            }
            ScalarWidth::Narrow(_) => {
                let raw = self.insert_before_one(
                    inst,
                    Add::new(self.evm_inst_set(), lhs, rhs),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_sub(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => {
                let result = self.insert_before_one(
                    inst,
                    Xor::new(self.evm_inst_set(), lhs, rhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result]);
            }
            ScalarWidth::Narrow(_) => {
                let raw = self.insert_before_one(
                    inst,
                    Sub::new(self.evm_inst_set(), lhs, rhs),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_mul(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => {
                let result = self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), lhs, rhs),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result]);
            }
            ScalarWidth::Narrow(_) => {
                let raw = self.insert_before_one(
                    inst,
                    Mul::new(self.evm_inst_set(), lhs, rhs),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_neg(&mut self, inst: InstId, arg: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => self.replace_with_aliases(inst, &[arg]),
            ScalarWidth::Narrow(_) => {
                let zero = self.zero_i256();
                let raw = self.insert_before_one(
                    inst,
                    Sub::new(self.evm_inst_set(), zero, arg),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_udiv(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        let data = EvmUdiv::new(self.evm_inst_set(), lhs, rhs);
        if width == ScalarWidth::Full256 {
            self.func.dfg.replace_inst(inst, Box::new(data));
            return;
        }
        let result = self.insert_before_one(inst, data, Type::I256, Some(width));
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_umod(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        let data = EvmUmod::new(self.evm_inst_set(), lhs, rhs);
        if width == ScalarWidth::Full256 {
            self.func.dfg.replace_inst(inst, Box::new(data));
            return;
        }
        let result = self.insert_before_one(inst, data, Type::I256, Some(width));
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_sdiv(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        self.rewrite_signed_div_mod(inst, lhs, rhs, true);
    }

    fn rewrite_smod(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        self.rewrite_signed_div_mod(inst, lhs, rhs, false);
    }

    fn rewrite_signed_div_mod(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId, is_div: bool) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };

        let lhs_ext = self.sign_extend_to_i256(inst, lhs, width);
        let rhs_ext = self.sign_extend_to_i256(inst, rhs, width);
        let raw = if is_div {
            self.insert_before_one(
                inst,
                EvmSdiv::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                Type::I256,
                Some(ScalarWidth::Full256),
            )
        } else {
            self.insert_before_one(
                inst,
                EvmSmod::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                Type::I256,
                Some(ScalarWidth::Full256),
            )
        };
        let result = self.normalize_and_retag_width(inst, raw, width);
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_shl(&mut self, inst: InstId, bits: ValueId, value: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => {
                let keep = self.insert_before_one(
                    inst,
                    IsZero::new(self.evm_inst_set(), bits),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let result = self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), value, keep),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result]);
            }
            ScalarWidth::Narrow(_) => {
                let raw = self.insert_before_one(
                    inst,
                    arith::Shl::new(self.evm_inst_set(), bits, value),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_shr(&mut self, inst: InstId, bits: ValueId, value: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 | ScalarWidth::Narrow(_) => {}
            ScalarWidth::Bool => {
                let keep = self.insert_before_one(
                    inst,
                    IsZero::new(self.evm_inst_set(), bits),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                let result = self.insert_before_one(
                    inst,
                    And::new(self.evm_inst_set(), value, keep),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_sar(&mut self, inst: InstId, bits: ValueId, value: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => self.replace_with_aliases(inst, &[value]),
            ScalarWidth::Narrow(_) => {
                let signed = self.sign_extend_to_i256(inst, value, width);
                let raw = self.insert_before_one(
                    inst,
                    arith::Sar::new(self.evm_inst_set(), bits, signed),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_not(&mut self, inst: InstId, arg: ValueId) {
        let width = match self.single_result_width(inst) {
            Some(width) => width,
            None => return,
        };
        match width {
            ScalarWidth::Full256 => {}
            ScalarWidth::Bool => {
                let result = self.insert_before_one(
                    inst,
                    IsZero::new(self.evm_inst_set(), arg),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.replace_with_aliases(inst, &[result]);
            }
            ScalarWidth::Narrow(bits) => {
                let mask = self.mask_value(bits);
                let result = self.insert_before_one(
                    inst,
                    Xor::new(self.evm_inst_set(), arg, mask),
                    Type::I256,
                    Some(width),
                );
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_signed_cmp(
        &mut self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
        kind: SignedCmpKind,
    ) {
        let width = match self.width_of(lhs).or_else(|| self.width_of(rhs)) {
            Some(width) => width,
            None => return,
        };
        if width == ScalarWidth::Full256 {
            return;
        }
        let lhs_ext = self.sign_extend_to_i256(inst, lhs, width);
        let rhs_ext = self.sign_extend_to_i256(inst, rhs, width);
        let result = match kind {
            SignedCmpKind::Lt => self.insert_before_one(
                inst,
                Slt::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                Type::I1,
                Some(ScalarWidth::Bool),
            ),
            SignedCmpKind::Gt => self.insert_before_one(
                inst,
                Sgt::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                Type::I1,
                Some(ScalarWidth::Bool),
            ),
            SignedCmpKind::Ge => {
                let slt = self.insert_before_one(
                    inst,
                    Slt::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.insert_before_one(
                    inst,
                    IsZero::new(self.evm_inst_set(), slt),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
            SignedCmpKind::Le => {
                let sgt = self.insert_before_one(
                    inst,
                    Sgt::new(self.evm_inst_set(), lhs_ext, rhs_ext),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                );
                self.insert_before_one(
                    inst,
                    IsZero::new(self.evm_inst_set(), sgt),
                    Type::I1,
                    Some(ScalarWidth::Bool),
                )
            }
        };
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_sext(&mut self, inst: InstId, arg: ValueId) {
        let dst = self
            .single_result_width(inst)
            .expect("missing sext result width");
        let src = self.width_of(arg).expect("missing sext source width");
        let extended = self.sign_extend_to_i256(inst, arg, src);
        let result = match dst {
            ScalarWidth::Full256 => extended,
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                self.normalize_and_retag_width(inst, extended, dst)
            }
        };
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_zext(&mut self, inst: InstId, arg: ValueId) {
        let dst = self
            .single_result_width(inst)
            .expect("missing zext result width");
        let src = self.width_of(arg).expect("missing zext source width");
        if matches!(dst, ScalarWidth::Bool) {
            let result = self.retag_width(inst, arg, dst);
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        let result = match src {
            ScalarWidth::Bool => self.insert_before_one(
                inst,
                Bitcast::new(self.evm_inst_set(), arg, Type::I256),
                Type::I256,
                Some(dst),
            ),
            ScalarWidth::Narrow(_) | ScalarWidth::Full256 => self.retag_width(inst, arg, dst),
        };
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_trunc(&mut self, inst: InstId, arg: ValueId) {
        let dst = self
            .single_result_width(inst)
            .expect("missing trunc result width");
        let extended = self.zero_extend_to_i256(inst, arg);
        let result = match dst {
            ScalarWidth::Full256 => self.retag_width(inst, arg, ScalarWidth::Full256),
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                self.normalize_and_retag_width(inst, extended, dst)
            }
        };
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_bitcast(&mut self, inst: InstId, from: ValueId, ty: Type) {
        let dst_ty = self.types.legalize_type(self.ctx, ty);
        let src_ty = self.func.dfg.value_ty(from);
        if src_ty == dst_ty {
            // Narrow and widened scalar bitcasts both collapse to `i256` on EVM, but they still
            // need the destination width's semantics and provenance.
            let result = if dst_ty == Type::I256 {
                let dst = self
                    .single_result_width(inst)
                    .expect("missing bitcast result width");
                self.normalize_and_retag_width(inst, from, dst)
            } else {
                from
            };
            self.replace_with_aliases(inst, &[result]);
            return;
        }

        self.func.dfg.replace_inst(
            inst,
            Box::new(Bitcast::new(self.evm_inst_set(), from, dst_ty)),
        );
    }

    fn rewrite_ptr_to_int(&mut self, inst: InstId, from: ValueId) {
        let dst = self
            .single_result_width(inst)
            .expect("missing ptrtoint result width");
        if dst == ScalarWidth::Full256 {
            self.func.dfg.replace_inst(
                inst,
                Box::new(PtrToInt::new(self.evm_inst_set(), from, Type::I256)),
            );
            return;
        }

        let raw = self.insert_before_one(
            inst,
            PtrToInt::new(self.evm_inst_set(), from, Type::I256),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let result = self.normalize_and_retag_width(inst, raw, dst);
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_int_to_ptr(&mut self, inst: InstId, from: ValueId, ty: Type) {
        let ty = self.types.legalize_type(self.ctx, ty);
        self.func
            .dfg
            .replace_inst(inst, Box::new(IntToPtr::new(self.evm_inst_set(), from, ty)));
    }

    fn rewrite_mload(&mut self, inst: InstId, addr: ValueId, ty: Type) {
        let Some(width) = scalar_width_for_type(self.ctx, ty) else {
            let ty = self.types.legalize_type(self.ctx, ty);
            self.func
                .dfg
                .replace_inst(inst, Box::new(Mload::new(self.evm_inst_set(), addr, ty)));
            return;
        };

        match width {
            ScalarWidth::Full256 => {
                self.func.dfg.replace_inst(
                    inst,
                    Box::new(Mload::new(self.evm_inst_set(), addr, Type::I256)),
                );
            }
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                let raw = self.insert_before_one(
                    inst,
                    Mload::new(self.evm_inst_set(), addr, Type::I256),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let result = self.normalize_and_retag_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_mstore(&mut self, inst: InstId, addr: ValueId, value: ValueId, ty: Type) {
        let ty = self.types.legalize_type(self.ctx, ty);
        let value = match scalar_width_for_type(self.ctx, ty) {
            Some(ScalarWidth::Narrow(bits)) => {
                let extended = self.zero_extend_to_i256(inst, value);
                self.normalize_bits_for_width(inst, extended, ScalarWidth::Narrow(bits))
            }
            Some(ScalarWidth::Bool) | Some(ScalarWidth::Full256) | None => value,
        };
        self.func.dfg.replace_inst(
            inst,
            Box::new(Mstore::new(self.evm_inst_set(), addr, value, ty)),
        );
    }

    fn single_result_width(&self, inst: InstId) -> Option<ScalarWidth> {
        let [result] = self.func.dfg.inst_results(inst) else {
            return None;
        };
        self.width_of(*result)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SignedOverflowKind {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SignedCmpKind {
    Lt,
    Gt,
    Le,
    Ge,
}

#[cfg(test)]
mod tests {
    use super::legalize_evm_section;
    use sonatina_ir::{Function, ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::{ParsedModule, parse_module};

    fn parse(src: &str) -> ParsedModule {
        parse_module(src).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn find_func(parsed: &ParsedModule, name: &str) -> FuncRef {
        parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func_ref| {
                parsed
                    .module
                    .ctx
                    .func_sig(func_ref, |sig| sig.name() == name)
            })
            .unwrap_or_else(|| panic!("function `{name}` should exist"))
    }

    fn dump_func(function: &Function, func_ref: FuncRef) -> String {
        FuncWriter::new(func_ref, function).dump_string()
    }

    fn legalize_and_dump(src: &str, name: &str) -> String {
        let parsed = parse(src);
        let funcs = parsed.module.funcs();
        legalize_evm_section(&parsed.module, &funcs);

        let func_ref = find_func(&parsed, name);
        parsed
            .module
            .func_store
            .view(func_ref, |function| dump_func(function, func_ref))
    }

    #[test]
    fn pointer_preserving_bitcasts_stay_aliases_through_legalization() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"

func public %entry() -> i8 {
block0:
    v0.*i8 = alloca i8;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 7.i8 i8;
    v2.*i8 = bitcast v1 *i8;
    v3.i8 = mload v2 i8;
    return v3;
}
"#,
            "entry",
        );

        assert!(dumped.contains("v0.*i256 = alloca i256;"), "{dumped}");
        assert!(dumped.contains("mstore v0 7.i256 i256;"), "{dumped}");
        assert!(dumped.contains("mload v0 i256;"), "{dumped}");
        assert!(dumped.contains("and v"), "{dumped}");
        assert!(dumped.contains("return v"), "{dumped}");
        assert!(!dumped.contains("bitcast"), "{dumped}");
        assert!(!dumped.contains(" = or "), "{dumped}");
        assert!(!dumped.contains("ptrtoint"), "{dumped}");
        assert!(!dumped.contains("inttoptr"), "{dumped}");
    }

    #[test]
    fn collapsed_scalar_bitcasts_keep_destination_width_semantics() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i32) -> i16 {
block0:
    v1.i8 = bitcast v0 i8;
    v2.i16 = sext v1 i16;
    return v2;
}
"#,
            "entry",
        );

        assert!(dumped.contains("255.i256"), "{dumped}");
        assert!(dumped.contains("248.i256"), "{dumped}");
        assert!(!dumped.contains("224.i256"), "{dumped}");
        assert!(!dumped.contains(" = bitcast "), "{dumped}");
    }

    #[test]
    fn trunc_results_retag_even_when_bits_already_fit_locally() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1) -> i16 {
block0:
    v1.i256 = zext v0 i256;
    v2.i8 = trunc v1 i8;
    v3.i16 = sext v2 i16;
    return v3;
}
"#,
            "entry",
        );

        assert!(dumped.contains("248.i256"), "{dumped}");
        assert!(dumped.contains(" = or v"), "{dumped}");
        assert!(dumped.contains("65535.i256"), "{dumped}");
        assert!(!dumped.contains(" = trunc "), "{dumped}");
        assert!(!dumped.contains(" = sext "), "{dumped}");
    }

    #[test]
    fn narrow_mload_results_feed_signed_ops_at_their_own_width() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"

func public %entry() -> i16 {
block0:
    v0.*i8 = alloca i8;
    mstore v0 255.i8 i8;
    v1.i8 = mload v0 i8;
    v2.i16 = sext v1 i16;
    return v2;
}
"#,
            "entry",
        );

        assert!(dumped.contains("mload v0 i256;"), "{dumped}");
        assert!(dumped.contains("255.i256"), "{dumped}");
        assert!(dumped.contains("248.i256"), "{dumped}");
        assert!(!dumped.contains(" = mload v0 i8;"), "{dumped}");
    }
}
