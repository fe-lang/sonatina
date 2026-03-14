use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, Module, Type, U256, Value, ValueId,
    inst::{
        arith::{self, Add, Mul, Neg, Sdiv, Smod, Sub, Udiv, Umod},
        cast::{self, Bitcast, IntToPtr, PtrToInt},
        cmp::{self, Eq, IsZero, Ne, Sgt, Slt},
        data::{Alloca, MemAllocDynamic, Mload, Mstore},
        downcast,
        evm::{
            EvmMalloc, EvmSdiv, EvmSdivo, EvmSmod, EvmSmodo, EvmUdiv, EvmUdivo, EvmUmod, EvmUmodo,
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
            downcast::<&arith::Uaddo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_uaddo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Saddo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_overflow_binary(inst, lhs, rhs, SignedOverflowKind::Add);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Usubo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_usubo(inst, lhs, rhs);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Ssubo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_signed_overflow_binary(inst, lhs, rhs, SignedOverflowKind::Sub);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&arith::Umulo>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_umulo(inst, lhs, rhs);
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
        let mask = if bits == 256 {
            !U256::zero()
        } else {
            (U256::one() << usize::from(bits)) - U256::one()
        };
        self.imm_i256(mask)
    }

    fn shift_value(&mut self, bits: u16) -> ValueId {
        self.imm_i256(U256::from(bits))
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

    fn copy_i256_with_width(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        let zero = self.zero_i256();
        self.insert_before_one(
            before,
            Or::new(self.evm_inst_set(), value, zero),
            Type::I256,
            Some(width),
        )
    }

    fn zero_extend_to_i256(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        match width {
            ScalarWidth::Bool => self.insert_before_one(
                before,
                Bitcast::new(self.evm_inst_set(), value, Type::I256),
                Type::I256,
                Some(ScalarWidth::Full256),
            ),
            ScalarWidth::Narrow(_) | ScalarWidth::Full256 => {
                self.copy_i256_with_width(before, value, ScalarWidth::Full256)
            }
        }
    }

    fn sign_extend_to_i256(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        match width {
            ScalarWidth::Full256 => self.copy_i256_with_width(before, value, ScalarWidth::Full256),
            ScalarWidth::Bool => {
                let widened = self.zero_extend_to_i256(before, value, ScalarWidth::Bool);
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

    fn canonicalize_to_width(
        &mut self,
        before: InstId,
        value: ValueId,
        width: ScalarWidth,
    ) -> ValueId {
        match width {
            ScalarWidth::Full256 => value,
            ScalarWidth::Narrow(bits) => {
                let mask = self.mask_value(bits);
                self.insert_before_one(
                    before,
                    And::new(self.evm_inst_set(), value, mask),
                    Type::I256,
                    Some(ScalarWidth::Narrow(bits)),
                )
            }
            ScalarWidth::Bool => {
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
        let sum = self.canonicalize_to_width(inst, raw, sum_width);
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
        let result = self.canonicalize_to_width(inst, raw, sum_width);
        let overflow = self.insert_before_one(
            inst,
            cmp::Lt::new(self.evm_inst_set(), lhs, rhs),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        self.replace_with_aliases(inst, &[result, overflow]);
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
        let result = self.canonicalize_to_width(inst, raw, result_width);
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
        let arg_ext = self.zero_extend_to_i256(inst, arg, width);
        let raw = self.insert_before_one(
            inst,
            Sub::new(self.evm_inst_set(), zero, arg_ext),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let result = self.canonicalize_to_width(inst, raw, width);
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
                self.canonicalize_to_width(inst, raw, width)
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
                self.canonicalize_to_width(inst, raw, width)
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
        let result = self.canonicalize_to_width(inst, raw, width);
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
                let result = self.canonicalize_to_width(inst, raw, width);
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
                self.canonicalize_to_width(inst, extended, dst)
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
            self.replace_with_aliases(inst, &[arg]);
            return;
        }

        let result = match src {
            ScalarWidth::Bool => self.insert_before_one(
                inst,
                Bitcast::new(self.evm_inst_set(), arg, Type::I256),
                Type::I256,
                Some(dst),
            ),
            ScalarWidth::Narrow(_) | ScalarWidth::Full256 => {
                self.copy_i256_with_width(inst, arg, dst)
            }
        };
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_trunc(&mut self, inst: InstId, arg: ValueId) {
        let dst = self
            .single_result_width(inst)
            .expect("missing trunc result width");
        let extended = self.zero_extend_to_i256(
            inst,
            arg,
            self.width_of(arg).unwrap_or(ScalarWidth::Full256),
        );
        let result = match dst {
            ScalarWidth::Full256 => self.copy_i256_with_width(inst, arg, ScalarWidth::Full256),
            ScalarWidth::Bool | ScalarWidth::Narrow(_) => {
                self.canonicalize_to_width(inst, extended, dst)
            }
        };
        self.replace_with_aliases(inst, &[result]);
    }

    fn rewrite_bitcast(&mut self, inst: InstId, from: ValueId, ty: Type) {
        let dst_ty = self.types.legalize_type(self.ctx, ty);
        let src_ty = self.func.dfg.value_ty(from);
        if src_ty == dst_ty {
            self.replace_with_aliases(inst, &[from]);
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
        let result = self.canonicalize_to_width(inst, raw, dst);
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
                let result = self.canonicalize_to_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    fn rewrite_mstore(&mut self, inst: InstId, addr: ValueId, value: ValueId, ty: Type) {
        let ty = self.types.legalize_type(self.ctx, ty);
        let value = match scalar_width_for_type(self.ctx, ty) {
            Some(ScalarWidth::Narrow(bits)) => {
                let width = self.width_of(value).unwrap_or(ScalarWidth::Narrow(bits));
                let extended = self.zero_extend_to_i256(inst, value, width);
                self.canonicalize_to_width(inst, extended, ScalarWidth::Narrow(bits))
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
