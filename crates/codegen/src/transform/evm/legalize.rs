use std::iter;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, InstSetExt, Module, Type, U256, Value, ValueId,
    inst::{
        BinaryInstKind, UnaryInstKind,
        arith::{
            self, Add, Mul, Neg, Saddsat, Sdiv, Smod, Smulsat, Ssubsat, Sub, Uaddsat, Udiv, Umod,
            Umulsat, Usubsat,
        },
        cast::{self, Bitcast, IntToPtr, PtrToInt},
        cmp::{self, Eq, IsZero, Ne, Sgt, Slt},
        data::{
            AggMake, Alloca, ExtractValue, Freeze, InsertValue, MemAllocDynamic, Memcopy, Mload,
            Mstore,
        },
        downcast,
        evm::{
            EvmCodeLoad, EvmExp, EvmMalloc, EvmMcopy, EvmSaddsat, EvmSdiv, EvmSdivo, EvmSmod,
            EvmSmodo, EvmSmulsat, EvmSsubsat, EvmUaddsat, EvmUdiv, EvmUdivo, EvmUmod, EvmUmodo,
            EvmUmulsat, EvmUsubsat, inst_set::EvmInstKind,
        },
        logic::{self, And, Or, Xor},
    },
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeRef, StructData},
};
use sonatina_triple::Architecture;

use super::{const_data::emit_const_load_from_addr, scalar_words::legalize_evm_scalar_immediate};
use crate::{optim::adce::AdceSolver, transform::aggregate::shape::is_supported_aggregate_ty};

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

    /// A member of an aggregate is a word, as in memory: an `i1` member becomes `i256`, as
    /// narrower integers do, so no `i1` is ever read from memory. Reading one back goes through
    /// a `bitcast` to `i1`, which keeps only the low bit.
    fn legalize_member_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type {
        if ty == Type::I1 {
            Type::I256
        } else {
            self.legalize_type(ctx, ty)
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
                let elem = self.legalize_member_type(ctx, elem);
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
                    .map(|&field| self.legalize_member_type(ctx, field))
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

/// The `insert_value`s of an `i1` and the `bitcast`s of an `i1` to an aggregate.
fn widened_aggregate_members(ctx: &ModuleCtx, func: &Function) -> FxHashSet<InstId> {
    func.layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| {
            if let Some(insert) = func.dfg.downcast::<&InsertValue>(inst) {
                func.dfg.value_ty(*insert.value()) == Type::I1
            } else {
                func.dfg.downcast::<&Bitcast>(inst).is_some_and(|bitcast| {
                    func.dfg.value_ty(*bitcast.from()) == Type::I1
                        && is_supported_aggregate_ty(ctx, *bitcast.ty())
                })
            }
        })
        .collect()
}

/// The extracts and aggregate-to-scalar bitcasts that read an `i1` member, which is a word after
/// legalization.
fn bool_member_reads(ctx: &ModuleCtx, func: &Function) -> FxHashSet<InstId> {
    func.layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| {
            matches!(func.dfg.inst_results(inst), [result] if func.dfg.value_ty(*result) == Type::I1)
                && (func.dfg.downcast::<&ExtractValue>(inst).is_some()
                    || func.dfg.downcast::<&Bitcast>(inst).is_some_and(|bitcast| {
                        is_supported_aggregate_ty(ctx, func.dfg.value_ty(*bitcast.from()))
                    }))
        })
        .collect()
}

/// The `i1`s read from an aggregate member or memory whose only uses store them as `i1`s, into
/// memory or an aggregate member. Such a copy carries the word it read: a load and a store of
/// the same type carry the slot's word, and every read that uses the value as an `i1` still goes
/// through a `bitcast` to `i1`.
fn bool_word_copies(func: &Function, bool_member_reads: &FxHashSet<InstId>) -> FxHashSet<ValueId> {
    func.layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|inst| {
            bool_member_reads.contains(inst)
                || func
                    .dfg
                    .downcast::<&Mload>(*inst)
                    .is_some_and(|load| *load.ty() == Type::I1)
        })
        .filter_map(|inst| func.dfg.inst_result(inst))
        .filter(|&value| {
            func.dfg.users(value).all(|&user| {
                func.dfg.downcast::<&Mstore>(user).is_some_and(|store| {
                    *store.value() == value && *store.addr() != value && *store.ty() == Type::I1
                }) || func
                    .dfg
                    .downcast::<&InsertValue>(user)
                    .is_some_and(|insert| {
                        *insert.value() == value
                            && *insert.dest() != value
                            && *insert.idx() != value
                    })
                    || func
                        .dfg
                        .downcast::<&AggMake>(user)
                        .is_some_and(|make| make.values().contains(&value))
            })
        })
        .collect()
}

/// Whether an instruction of `kind` gives a word that a result of `width` need not hold, so that
/// the word must be cut to the result type. Every kind is listed, so a new instruction does not
/// compile until it is classified.
fn gives_wider_word(kind: EvmInstKind<'_>, width: ScalarWidth) -> bool {
    match kind {
        // A word read from the environment, memory, storage or a hash, or the address `create`
        // makes: any word, whatever the result type.
        EvmInstKind::EvmKeccak256(_)
        | EvmInstKind::EvmAddress(_)
        | EvmInstKind::EvmBalance(_)
        | EvmInstKind::EvmOrigin(_)
        | EvmInstKind::EvmCaller(_)
        | EvmInstKind::EvmCallValue(_)
        | EvmInstKind::EvmCalldataLoad(_)
        | EvmInstKind::EvmCalldataSize(_)
        | EvmInstKind::EvmCodeSize(_)
        | EvmInstKind::EvmGasPrice(_)
        | EvmInstKind::EvmExtCodeSize(_)
        | EvmInstKind::EvmReturnDataSize(_)
        | EvmInstKind::EvmExtCodeHash(_)
        | EvmInstKind::EvmBlockHash(_)
        | EvmInstKind::EvmCoinBase(_)
        | EvmInstKind::EvmTimestamp(_)
        | EvmInstKind::EvmNumber(_)
        | EvmInstKind::EvmPrevRandao(_)
        | EvmInstKind::EvmGasLimit(_)
        | EvmInstKind::EvmChainId(_)
        | EvmInstKind::EvmSelfBalance(_)
        | EvmInstKind::EvmBaseFee(_)
        | EvmInstKind::EvmBlobHash(_)
        | EvmInstKind::EvmBlobBaseFee(_)
        | EvmInstKind::EvmMload(_)
        | EvmInstKind::EvmSload(_)
        | EvmInstKind::EvmMsize(_)
        | EvmInstKind::EvmGas(_)
        | EvmInstKind::EvmTload(_)
        | EvmInstKind::EvmCreate(_)
        | EvmInstKind::EvmCreate2(_) => true,
        // A narrow value sign-extended to 256 bits. Its operands share the result type, so at
        // `i1` it gives 0 or 1.
        EvmInstKind::EvmSignExtend(_) => width != ScalarWidth::Bool,
        // Rewritten elsewhere in legalization to a value of the result type.
        EvmInstKind::Neg(_)
        | EvmInstKind::Add(_)
        | EvmInstKind::Uaddo(_)
        | EvmInstKind::Uaddsat(_)
        | EvmInstKind::Saddo(_)
        | EvmInstKind::Saddsat(_)
        | EvmInstKind::Mul(_)
        | EvmInstKind::Sub(_)
        | EvmInstKind::Usubo(_)
        | EvmInstKind::Usubsat(_)
        | EvmInstKind::Ssubo(_)
        | EvmInstKind::Ssubsat(_)
        | EvmInstKind::Umulo(_)
        | EvmInstKind::Umulsat(_)
        | EvmInstKind::Smulo(_)
        | EvmInstKind::Smulsat(_)
        | EvmInstKind::Snego(_)
        | EvmInstKind::Sdiv(_)
        | EvmInstKind::Udiv(_)
        | EvmInstKind::Umod(_)
        | EvmInstKind::Smod(_)
        | EvmInstKind::Shl(_)
        | EvmInstKind::Shr(_)
        | EvmInstKind::Sar(_)
        | EvmInstKind::Sext(_)
        | EvmInstKind::Zext(_)
        | EvmInstKind::Trunc(_)
        | EvmInstKind::Bitcast(_)
        | EvmInstKind::PtrToInt(_)
        | EvmInstKind::Not(_)
        | EvmInstKind::Select(_)
        | EvmInstKind::Bswap(_)
        | EvmInstKind::Clz(_)
        | EvmInstKind::Ctz(_)
        | EvmInstKind::EvmSdiv(_)
        | EvmInstKind::EvmSdivo(_)
        | EvmInstKind::EvmUdivo(_)
        | EvmInstKind::EvmSmod(_)
        | EvmInstKind::EvmUmodo(_)
        | EvmInstKind::EvmSmodo(_)
        | EvmInstKind::EvmExp(_)
        | EvmInstKind::Mload(_) => false,
        // No wider than an operand of the result type, or below one: bitwise logic, unsigned
        // division and remainder, `addmod` and `mulmod`, a byte of the word, saturation at the
        // type the instruction names.
        EvmInstKind::And(_)
        | EvmInstKind::Or(_)
        | EvmInstKind::Xor(_)
        | EvmInstKind::EvmUdiv(_)
        | EvmInstKind::EvmUmod(_)
        | EvmInstKind::EvmAddMod(_)
        | EvmInstKind::EvmMulMod(_)
        | EvmInstKind::EvmByte(_)
        | EvmInstKind::EvmUaddsat(_)
        | EvmInstKind::EvmSaddsat(_)
        | EvmInstKind::EvmUsubsat(_)
        | EvmInstKind::EvmSsubsat(_)
        | EvmInstKind::EvmUmulsat(_)
        | EvmInstKind::EvmSmulsat(_) => false,
        // 0 or 1: comparisons and the success flag of a call.
        EvmInstKind::Lt(_)
        | EvmInstKind::Gt(_)
        | EvmInstKind::Slt(_)
        | EvmInstKind::Sgt(_)
        | EvmInstKind::Le(_)
        | EvmInstKind::Ge(_)
        | EvmInstKind::Sle(_)
        | EvmInstKind::Sge(_)
        | EvmInstKind::Eq(_)
        | EvmInstKind::Ne(_)
        | EvmInstKind::IsZero(_)
        | EvmInstKind::EvmCall(_)
        | EvmInstKind::EvmCallCode(_)
        | EvmInstKind::EvmDelegateCall(_)
        | EvmInstKind::EvmStaticCall(_) => false,
        // A value passed on from elsewhere, which its producer made a value of its type: a phi
        // input, a returned value, the argument of `black_box` or `freeze`, or a member an insert
        // or a typed store put there.
        EvmInstKind::Phi(_)
        | EvmInstKind::Call(_)
        | EvmInstKind::BlackBox(_)
        | EvmInstKind::Freeze(_)
        | EvmInstKind::ExtractValue(_) => false,
        // A word or pointer result, which the verifier requires, or an aggregate.
        EvmInstKind::EvmKeccak256Words(_)
        | EvmInstKind::EvmCodeLoad(_)
        | EvmInstKind::EvmMalloc(_)
        | EvmInstKind::MemAllocDynamic(_)
        | EvmInstKind::IntToPtr(_)
        | EvmInstKind::Gep(_)
        | EvmInstKind::GetFunctionPtr(_)
        | EvmInstKind::SymAddr(_)
        | EvmInstKind::SymSize(_)
        | EvmInstKind::Alloca(_)
        | EvmInstKind::InsertValue(_)
        | EvmInstKind::AggMake(_) => false,
        // Objects, constant references and enums are lowered before EVM legalization.
        EvmInstKind::ObjAlloc(_)
        | EvmInstKind::ConstRef(_)
        | EvmInstKind::ConstProj(_)
        | EvmInstKind::ConstIndex(_)
        | EvmInstKind::ConstLoad(_)
        | EvmInstKind::ObjProj(_)
        | EvmInstKind::ObjIndex(_)
        | EvmInstKind::ObjLoad(_)
        | EvmInstKind::ObjStore(_)
        | EvmInstKind::EnumMake(_)
        | EvmInstKind::EnumTag(_)
        | EvmInstKind::EnumIsVariant(_)
        | EvmInstKind::EnumAssertVariant(_)
        | EvmInstKind::EnumAssertVariantRef(_)
        | EvmInstKind::EnumExtract(_)
        | EvmInstKind::EnumSetTag(_)
        | EvmInstKind::EnumWriteVariant(_)
        | EvmInstKind::EnumGetTag(_)
        | EvmInstKind::EnumProj(_)
        | EvmInstKind::ObjMaterializeStack(_)
        | EvmInstKind::ObjFromPtr(_) => false,
        // No result.
        EvmInstKind::Jump(_)
        | EvmInstKind::Br(_)
        | EvmInstKind::BrTable(_)
        | EvmInstKind::Return(_)
        | EvmInstKind::Unreachable(_)
        | EvmInstKind::Mstore(_)
        | EvmInstKind::Memzero(_)
        | EvmInstKind::Memcopy(_)
        | EvmInstKind::EvmStop(_)
        | EvmInstKind::EvmInvalid(_)
        | EvmInstKind::EvmCalldataCopy(_)
        | EvmInstKind::EvmCodeCopy(_)
        | EvmInstKind::EvmExtCodeCopy(_)
        | EvmInstKind::EvmReturnDataCopy(_)
        | EvmInstKind::EvmMstore(_)
        | EvmInstKind::EvmMstore8(_)
        | EvmInstKind::EvmSstore(_)
        | EvmInstKind::EvmMcopy(_)
        | EvmInstKind::EvmTstore(_)
        | EvmInstKind::EvmLog0(_)
        | EvmInstKind::EvmLog1(_)
        | EvmInstKind::EvmLog2(_)
        | EvmInstKind::EvmLog3(_)
        | EvmInstKind::EvmLog4(_)
        | EvmInstKind::EvmReturn(_)
        | EvmInstKind::EvmRevert(_)
        | EvmInstKind::EvmSelfDestruct(_) => false,
    }
}

fn legalize_immediate(imm: sonatina_ir::Immediate) -> sonatina_ir::Immediate {
    legalize_evm_scalar_immediate(imm).expect("EVM immediate legalization only supports scalars")
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

/// Lowers `freeze undef` to zero, or the null pointer, and leaves a freeze of
/// any other value alone. That freeze stays until [`lower_late_freezes`]: IR
/// passes run after legalization, and to them its argument may be
/// unspecified where its result is not. Returns the value that now stands
/// for the freeze's result, or `None` if the freeze stays.
fn lower_frozen_undef(func: &mut Function, inst: InstId) -> Option<ValueId> {
    let arg = *func.dfg.downcast::<&Freeze>(inst).expect("a freeze").arg();
    let result = func.dfg.inst_result(inst).expect("freeze has a result");
    let replacement = match *func.dfg.value(arg) {
        Value::Undef { ty } if ty.is_pointer(func.ctx()) => {
            let zero = func.dfg.make_imm_value(I256::zero());
            let null = IntToPtr::new_unchecked(func.inst_set(), zero, ty);
            func.dfg.replace_inst(inst, Box::new(null));
            return Some(result);
        }
        Value::Undef { ty } => func.dfg.make_imm_value(Immediate::zero(ty)),
        _ => return None,
    };
    func.dfg.change_to_alias(result, replacement);
    func.layout.remove_inst(inst);
    func.erase_inst(inst);
    Some(replacement)
}

/// Lowers every freeze once no IR pass is left: machine lowering picks zero
/// for each `undef`, so a frozen value is its argument there. Lowering a
/// freeze replaces its result in a later freeze of it.
pub(crate) fn lower_late_freezes(func: &mut Function) {
    let freezes: Vec<_> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| func.dfg.downcast::<&Freeze>(inst).is_some())
        .collect();
    for inst in freezes {
        if lower_frozen_undef(func, inst).is_none() {
            let arg = *func.dfg.downcast::<&Freeze>(inst).expect("a freeze").arg();
            let result = func.dfg.inst_result(inst).expect("freeze has a result");
            func.dfg.change_to_alias(result, arg);
            func.layout.remove_inst(inst);
            func.erase_inst(inst);
        }
    }
}

/// Removes the phis, loads and stores of `unit`, which hold no bits. A use of a
/// removed result reads `undef.unit` instead. ABI expansion has already dropped
/// unit arguments and results, so with these gone no unit value reaches machine
/// lowering, whatever earlier passes made.
pub fn erase_unit_values(func: &mut Function) {
    let insts: Vec<_> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| {
            func.dfg.is_phi(inst)
                && func
                    .dfg
                    .inst_result(inst)
                    .is_some_and(|result| func.dfg.value_ty(result).is_unit())
                || func
                    .dfg
                    .downcast::<&Mload>(inst)
                    .is_some_and(|load| load.ty().is_unit())
                || func
                    .dfg
                    .downcast::<&Mstore>(inst)
                    .is_some_and(|store| store.ty().is_unit())
        })
        .collect();
    for &inst in &insts {
        if let Some(result) = func.dfg.inst_result(inst) {
            let undef = func.dfg.make_undef_value(Type::Unit);
            func.dfg.change_to_alias(result, undef);
        }
        func.layout.remove_inst(inst);
    }
    func.erase_insts(&insts);
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

/// How an instruction uses an operand, for normalizing narrow values on EVM.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OperandUse {
    /// Sets what an effect does: a length, size, gas, value, call target, salt, or an offset into
    /// calldata, code or return data. A narrow word that holds the unspecified value may be wider
    /// than its type, so it is made a value of its type here, as `freeze` makes one.
    Effect,
    /// Needs no mask: strict data, data passed on or written out as bits, or a use that is
    /// undefined when the value is unspecified (an address, object, index, condition or
    /// variant assumption).
    Plain,
}

/// The use of each operand of an instruction, in operand order, or `None` when every operand is
/// `Plain`. The match has no catch-all arm, so an instruction added to the EVM instruction set
/// does not compile until it is classified here, and legalization checks that each slice has
/// one entry per operand.
fn operand_uses(kind: EvmInstKind<'_>) -> Option<&'static [OperandUse]> {
    use OperandUse::{Effect as E, Plain as P};
    match kind {
        EvmInstKind::Neg(_)
        | EvmInstKind::Add(_)
        | EvmInstKind::Uaddo(_)
        | EvmInstKind::Uaddsat(_)
        | EvmInstKind::Saddo(_)
        | EvmInstKind::Saddsat(_)
        | EvmInstKind::Mul(_)
        | EvmInstKind::Sub(_)
        | EvmInstKind::Usubo(_)
        | EvmInstKind::Usubsat(_)
        | EvmInstKind::Ssubo(_)
        | EvmInstKind::Ssubsat(_)
        | EvmInstKind::Umulo(_)
        | EvmInstKind::Umulsat(_)
        | EvmInstKind::Smulo(_)
        | EvmInstKind::Smulsat(_)
        | EvmInstKind::Snego(_)
        | EvmInstKind::Sdiv(_)
        | EvmInstKind::Udiv(_)
        | EvmInstKind::Umod(_)
        | EvmInstKind::Smod(_)
        | EvmInstKind::Shl(_)
        | EvmInstKind::Shr(_)
        | EvmInstKind::Sar(_)
        | EvmInstKind::Sext(_)
        | EvmInstKind::Zext(_)
        | EvmInstKind::Trunc(_)
        | EvmInstKind::Bitcast(_)
        | EvmInstKind::IntToPtr(_)
        | EvmInstKind::PtrToInt(_)
        | EvmInstKind::Lt(_)
        | EvmInstKind::Gt(_)
        | EvmInstKind::Slt(_)
        | EvmInstKind::Sgt(_)
        | EvmInstKind::Le(_)
        | EvmInstKind::Ge(_)
        | EvmInstKind::Sle(_)
        | EvmInstKind::Sge(_)
        | EvmInstKind::Eq(_)
        | EvmInstKind::Ne(_)
        | EvmInstKind::IsZero(_)
        | EvmInstKind::Not(_)
        | EvmInstKind::And(_)
        | EvmInstKind::Or(_)
        | EvmInstKind::Xor(_)
        | EvmInstKind::Select(_)
        | EvmInstKind::Bswap(_)
        | EvmInstKind::Clz(_)
        | EvmInstKind::Ctz(_)
        | EvmInstKind::EvmSdiv(_)
        | EvmInstKind::EvmUdiv(_)
        | EvmInstKind::EvmSdivo(_)
        | EvmInstKind::EvmUdivo(_)
        | EvmInstKind::EvmUmod(_)
        | EvmInstKind::EvmSmod(_)
        | EvmInstKind::EvmUmodo(_)
        | EvmInstKind::EvmSmodo(_)
        | EvmInstKind::EvmUaddsat(_)
        | EvmInstKind::EvmSaddsat(_)
        | EvmInstKind::EvmUsubsat(_)
        | EvmInstKind::EvmSsubsat(_)
        | EvmInstKind::EvmUmulsat(_)
        | EvmInstKind::EvmSmulsat(_)
        | EvmInstKind::EvmAddMod(_)
        | EvmInstKind::EvmMulMod(_)
        | EvmInstKind::EvmExp(_)
        | EvmInstKind::EvmSignExtend(_)
        | EvmInstKind::EvmByte(_)
        | EvmInstKind::EvmKeccak256Words(_)
        | EvmInstKind::EvmBalance(_)
        | EvmInstKind::EvmExtCodeSize(_)
        | EvmInstKind::EvmExtCodeHash(_)
        | EvmInstKind::EvmBlockHash(_)
        | EvmInstKind::EvmBlobHash(_) => None,
        EvmInstKind::Jump(_)
        | EvmInstKind::Br(_)
        | EvmInstKind::Phi(_)
        | EvmInstKind::BrTable(_)
        | EvmInstKind::Call(_)
        | EvmInstKind::Return(_)
        | EvmInstKind::Unreachable(_)
        | EvmInstKind::Freeze(_)
        | EvmInstKind::BlackBox(_)
        | EvmInstKind::Gep(_)
        | EvmInstKind::GetFunctionPtr(_)
        | EvmInstKind::SymAddr(_)
        | EvmInstKind::SymSize(_)
        | EvmInstKind::Alloca(_)
        | EvmInstKind::ObjAlloc(_)
        | EvmInstKind::ConstRef(_)
        | EvmInstKind::ConstProj(_)
        | EvmInstKind::ConstIndex(_)
        | EvmInstKind::ConstLoad(_)
        | EvmInstKind::ObjProj(_)
        | EvmInstKind::ObjIndex(_)
        | EvmInstKind::ObjLoad(_)
        | EvmInstKind::ObjStore(_)
        | EvmInstKind::EnumMake(_)
        | EvmInstKind::EnumTag(_)
        | EvmInstKind::EnumIsVariant(_)
        | EvmInstKind::EnumAssertVariant(_)
        | EvmInstKind::EnumAssertVariantRef(_)
        | EvmInstKind::EnumExtract(_)
        | EvmInstKind::EnumSetTag(_)
        | EvmInstKind::EnumWriteVariant(_)
        | EvmInstKind::EnumGetTag(_)
        | EvmInstKind::EnumProj(_)
        | EvmInstKind::ObjMaterializeStack(_)
        | EvmInstKind::ObjFromPtr(_)
        | EvmInstKind::AggMake(_)
        | EvmInstKind::InsertValue(_)
        | EvmInstKind::ExtractValue(_)
        | EvmInstKind::EvmStop(_)
        | EvmInstKind::EvmInvalid(_)
        | EvmInstKind::EvmAddress(_)
        | EvmInstKind::EvmOrigin(_)
        | EvmInstKind::EvmCaller(_)
        | EvmInstKind::EvmCallValue(_)
        | EvmInstKind::EvmCalldataSize(_)
        | EvmInstKind::EvmCodeSize(_)
        | EvmInstKind::EvmGasPrice(_)
        | EvmInstKind::EvmReturnDataSize(_)
        | EvmInstKind::EvmCoinBase(_)
        | EvmInstKind::EvmTimestamp(_)
        | EvmInstKind::EvmNumber(_)
        | EvmInstKind::EvmPrevRandao(_)
        | EvmInstKind::EvmGasLimit(_)
        | EvmInstKind::EvmChainId(_)
        | EvmInstKind::EvmSelfBalance(_)
        | EvmInstKind::EvmBaseFee(_)
        | EvmInstKind::EvmBlobBaseFee(_)
        | EvmInstKind::EvmMsize(_)
        | EvmInstKind::EvmGas(_) => None,
        EvmInstKind::Mload(_)
        | EvmInstKind::EvmMload(_)
        | EvmInstKind::EvmSload(_)
        | EvmInstKind::EvmTload(_) => Some(&[P]),
        EvmInstKind::Mstore(_)
        | EvmInstKind::EvmMstore(_)
        | EvmInstKind::EvmMstore8(_)
        | EvmInstKind::EvmSstore(_)
        | EvmInstKind::EvmTstore(_) => Some(&[P, P]),
        EvmInstKind::Memzero(_)
        | EvmInstKind::EvmKeccak256(_)
        | EvmInstKind::EvmLog0(_)
        | EvmInstKind::EvmReturn(_)
        | EvmInstKind::EvmRevert(_) => Some(&[P, E]),
        EvmInstKind::Memcopy(_) | EvmInstKind::EvmMcopy(_) => Some(&[P, P, E]),
        EvmInstKind::MemAllocDynamic(_)
        | EvmInstKind::EvmMalloc(_)
        | EvmInstKind::EvmCalldataLoad(_)
        | EvmInstKind::EvmCodeLoad(_)
        | EvmInstKind::EvmSelfDestruct(_) => Some(&[E]),
        EvmInstKind::EvmCalldataCopy(_)
        | EvmInstKind::EvmCodeCopy(_)
        | EvmInstKind::EvmReturnDataCopy(_) => Some(&[P, E, E]),
        EvmInstKind::EvmExtCodeCopy(_) => Some(&[E, P, E, E]),
        EvmInstKind::EvmLog1(_) => Some(&[P, E, P]),
        EvmInstKind::EvmLog2(_) => Some(&[P, E, P, P]),
        EvmInstKind::EvmLog3(_) => Some(&[P, E, P, P, P]),
        EvmInstKind::EvmLog4(_) => Some(&[P, E, P, P, P, P]),
        EvmInstKind::EvmCreate(_) => Some(&[E, P, E]),
        EvmInstKind::EvmCreate2(_) => Some(&[E, P, E, E]),
        EvmInstKind::EvmCall(_) | EvmInstKind::EvmCallCode(_) => Some(&[E, E, E, P, E, P, E]),
        EvmInstKind::EvmDelegateCall(_) | EvmInstKind::EvmStaticCall(_) => {
            Some(&[E, E, P, E, P, E])
        }
    }
}

struct FunctionLegalizer<'a> {
    ctx: &'a ModuleCtx,
    func: &'a mut Function,
    types: &'a mut TypeLegalizer,
    provenance: SecondaryMap<ValueId, Option<ScalarWidth>>,
    /// The reads of an `i1` member.
    bool_member_reads: FxHashSet<InstId>,
    /// The `insert_value`s and `bitcast`s that put an `i1` into an aggregate.
    widened_aggregate_members: FxHashSet<InstId>,
    /// The `i1` reads that only stores use, and the words they read, which those stores copy.
    bool_word_copies: FxHashSet<ValueId>,
}

impl<'a> FunctionLegalizer<'a> {
    fn new(func: &'a mut Function, ctx: &'a ModuleCtx, types: &'a mut TypeLegalizer) -> Self {
        let mut provenance = SecondaryMap::new();
        let values: Vec<_> = func.dfg.value_ids().collect();
        for value in values {
            provenance[value] = scalar_width_for_type(ctx, func.dfg.value_ty(value));
        }

        let bool_member_reads = bool_member_reads(ctx, func);
        let widened_aggregate_members = widened_aggregate_members(ctx, func);
        let bool_word_copies = bool_word_copies(func, &bool_member_reads);
        Self {
            ctx,
            func,
            types,
            provenance,
            bool_member_reads,
            widened_aggregate_members,
            bool_word_copies,
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
                Value::Zero { ty } => Value::Zero {
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
        self.normalize_effect_operands(inst);
        if self.bool_member_reads.contains(&inst) {
            self.rewrite_bool_member_read(inst);
            return;
        }
        if self.widened_aggregate_members.contains(&inst) {
            self.widen_aggregate_member(inst);
            return;
        }
        let is = self.evm_inst_set();

        if let Some(make) = downcast::<&AggMake>(is, self.func.dfg.inst(inst)).cloned() {
            self.legalize_agg_make(inst, make);
            return;
        }

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
        if let Some((base, exponent)) =
            downcast::<&EvmExp>(is, self.func.dfg.inst(inst)).map(|i| (*i.base(), *i.exponent()))
            && let Some(width @ ScalarWidth::Narrow(_)) = self.single_result_width(inst)
        {
            // EXP wraps at 256 bits; restore the declared width. Boolean
            // exponentiation already produces a canonical zero or one.
            let raw = self.insert_before_one(
                inst,
                EvmExp::new(is, base, exponent),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let result = self.normalize_and_retag_width(inst, raw, width);
            self.replace_with_aliases(inst, &[result]);
            return;
        }
        if let Some(width @ (ScalarWidth::Bool | ScalarWidth::Narrow(_))) =
            self.single_result_width(inst)
            && gives_wider_word(is.resolve_inst(self.func.dfg.inst(inst)), width)
        {
            // The word is cut to the result type, as the interpreter does.
            let copy = self.func.dfg.clone_inst(inst);
            let copy = self.func.dfg.make_inst_dyn(copy);
            let raw =
                self.place_before(inst, copy, &[Type::I256], &[Some(ScalarWidth::Full256)])[0];
            let result = self.word_to_width(inst, raw, width);
            self.replace_with_aliases(inst, &[result]);
            return;
        }
        if let Some((lhs, rhs)) =
            downcast::<&EvmSdiv>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_evm_sdiv(inst, lhs, rhs);
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
            downcast::<&EvmSmod>(is, self.func.dfg.inst(inst)).map(|i| (*i.lhs(), *i.rhs()))
        {
            self.rewrite_evm_smod(inst, lhs, rhs);
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
        if let Some(offset) =
            downcast::<&EvmCodeLoad>(is, self.func.dfg.inst(inst)).map(|i| *i.code_offset())
        {
            let value = emit_const_load_from_addr(self.func, inst, offset, Type::I256, None);
            self.replace_with_aliases(inst, &[value]);
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
        if let Some((dest, src, len)) = downcast::<&Memcopy>(is, self.func.dfg.inst(inst))
            .map(|i| (*i.dest(), *i.src(), *i.len()))
        {
            self.func.dfg.replace_inst(
                inst,
                Box::new(EvmMcopy::new(self.evm_inst_set(), dest, src, len)),
            );
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
        } else if let Some((cond, then, otherwise)) =
            downcast::<&logic::Select>(is, self.func.dfg.inst(inst))
                .map(|i| (*i.cond(), *i.then_value(), *i.else_value()))
        {
            self.rewrite_select(inst, cond, then, otherwise);
        } else if let Some(arg) =
            downcast::<&logic::Not>(is, self.func.dfg.inst(inst)).map(|i| *i.arg())
        {
            self.rewrite_not(inst, arg);
        } else if let Some(arg) =
            downcast::<&logic::Bswap>(is, self.func.dfg.inst(inst)).map(|i| *i.arg())
        {
            self.rewrite_bswap(inst, arg);
        } else if let Some(arg) =
            downcast::<&logic::Clz>(is, self.func.dfg.inst(inst)).map(|i| *i.arg())
        {
            self.rewrite_clz(inst, arg);
        } else if let Some(arg) =
            downcast::<&logic::Ctz>(is, self.func.dfg.inst(inst)).map(|i| *i.arg())
        {
            self.rewrite_ctz(inst, arg);
        } else if downcast::<&Freeze>(is, self.func.dfg.inst(inst)).is_some() {
            self.rewrite_freeze(inst);
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
        self.place_before(before, inst, result_tys, widths)
    }

    /// Places `inst`, which has no results yet, before `before` and gives it results.
    fn place_before(
        &mut self,
        before: InstId,
        inst: InstId,
        result_tys: &[Type],
        widths: &[Option<ScalarWidth>],
    ) -> SmallVec<[ValueId; 2]> {
        self.func.propagate_inst_attribution(inst, before);
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

    /// Makes each narrow operand that sets what an effect does a value of its type. An `i1`
    /// needs no mask: every `i1` is a compare, a constant or a word bitcast to `i1`.
    fn normalize_effect_operands(&mut self, inst: InstId) {
        let is = self.evm_inst_set();
        let Some(uses) = operand_uses(is.resolve_inst(self.func.dfg.inst(inst))) else {
            return;
        };
        let operands = self.func.dfg.inst(inst).collect_values();
        assert_eq!(
            uses.len(),
            operands.len(),
            "the operand uses of `{}` do not match its operands",
            self.func.dfg.inst(inst).as_text()
        );
        let mut masked = SmallVec::<[(usize, ValueId); 2]>::new();
        for (pos, (&operand, &usage)) in operands.iter().zip(uses).enumerate() {
            if usage == OperandUse::Effect
                && self.func.dfg.value_imm(operand).is_none()
                && !matches!(self.func.dfg.value(operand), Value::Zero { .. })
                && let Some(ScalarWidth::Narrow(bits)) = self.width_of(operand)
            {
                let mask = self.mask_value(bits);
                let value = self.insert_before_one(
                    inst,
                    And::new(is, operand, mask),
                    Type::I256,
                    Some(ScalarWidth::Narrow(bits)),
                );
                masked.push((pos, value));
            }
        }
        if masked.is_empty() {
            return;
        }
        let mut pos = 0;
        self.func
            .dfg
            .inst_mut(inst)
            .for_each_value_mut(&mut |value| {
                if let Some(&(_, masked)) = masked.iter().find(|&&(at, _)| at == pos) {
                    *value = masked;
                }
                pos += 1;
            });
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

    /// A full-width unsigned product by 2^k overflows exactly when any of
    /// the input's top k bits are set. Avoid multiplying and dividing back.
    fn full_width_pow2_product(
        &mut self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Option<(ValueId, ValueId)> {
        let (value, shift) =
            [(lhs, rhs), (rhs, lhs)]
                .into_iter()
                .find_map(|(value, constant)| {
                    let constant = self.func.dfg.value_imm(constant)?.as_i256().to_u256();
                    if constant <= U256::one()
                        || constant & (constant - U256::one()) != U256::zero()
                    {
                        return None;
                    }
                    Some((value, constant.trailing_zeros() as u16))
                })?;
        let low_shift = self.shift_value(shift);
        let high_shift = self.shift_value(256 - shift);
        let result = self.insert_before_one(
            inst,
            arith::Shl::new(self.evm_inst_set(), low_shift, value),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        // Widening retags a narrow value with OR zero. Look through that
        // identity to retain the source width's proof that the product fits.
        let range_value = self
            .func
            .dfg
            .value_inst(value)
            .and_then(|inst| self.func.dfg.downcast::<&Or>(inst))
            .filter(|or| {
                self.func
                    .dfg
                    .value_imm(*or.rhs())
                    .is_some_and(Immediate::is_zero)
            })
            .map_or(value, |or| *or.lhs());
        if self.value_fits_narrow_locally(range_value, 256 - shift) {
            let overflow = self.func.dfg.make_imm_value(Immediate::zero(Type::I1));
            self.provenance[overflow] = Some(ScalarWidth::Bool);
            return Some((result, overflow));
        }
        let high = self.insert_before_one(
            inst,
            arith::Shr::new(self.evm_inst_set(), high_shift, value),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let zero = self.zero_i256();
        let overflow = self.insert_before_one(
            inst,
            Ne::new(self.evm_inst_set(), high, zero),
            Type::I1,
            Some(ScalarWidth::Bool),
        );
        Some((result, overflow))
    }

    fn rewrite_umulo(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        let result_width = self
            .width_of(self.func.dfg.inst_results(inst)[0])
            .expect("missing result width");
        if result_width == ScalarWidth::Full256
            && let Some((result, overflow)) = self.full_width_pow2_product(inst, lhs, rhs)
        {
            self.replace_with_aliases(inst, &[result, overflow]);
            return;
        }
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
        if width == ScalarWidth::Full256
            && let Some((raw, overflow)) = self.full_width_pow2_product(inst, lhs, rhs)
        {
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

    fn rewrite_evm_sdiv(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        self.rewrite_signed_div_mod(inst, lhs, rhs, true);
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

    fn rewrite_evm_smod(&mut self, inst: InstId, lhs: ValueId, rhs: ValueId) {
        self.rewrite_signed_div_mod(inst, lhs, rhs, false);
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
            ScalarWidth::Bool => self.replace_with_aliases(inst, &[arg]),
            ScalarWidth::Full256 | ScalarWidth::Narrow(_) => {
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

    /// `else ^ ((then ^ else) & -cond)` on frozen arms: the result depends on
    /// both, and an unspecified arm would make it unspecified where the other
    /// is chosen. The operands are normalized to the result's width, and so is
    /// their masked difference.
    fn rewrite_select(&mut self, inst: InstId, cond: ValueId, then: ValueId, otherwise: ValueId) {
        let Some(width) = self.single_result_width(inst) else {
            return;
        };
        let ty = self.func.dfg.value_ty(then);
        let mut freeze = |value| {
            if self.func.dfg.value_is_imm(value) {
                return value;
            }
            let width = self.width_of(value);
            self.insert_before_one(inst, Freeze::new(self.evm_inst_set(), value), ty, width)
        };
        let (then, otherwise) = (freeze(then), freeze(otherwise));
        let mask = self.bool_to_mask_i256(inst, cond);
        let delta = self.insert_before_one(
            inst,
            Xor::new(self.evm_inst_set(), then, otherwise),
            ty,
            Some(width),
        );
        let masked = self.insert_before_one(
            inst,
            And::new(self.evm_inst_set(), delta, mask),
            ty,
            Some(width),
        );
        let result = self.insert_before_one(
            inst,
            Xor::new(self.evm_inst_set(), otherwise, masked),
            ty,
            Some(width),
        );
        self.replace_with_aliases(inst, &[result]);
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

    /// The EVM has no byte swap. Each round swaps the halves of every lane,
    /// from the whole value down to byte pairs; a canonical narrow value stays
    /// within its width throughout.
    fn rewrite_bswap(&mut self, inst: InstId, arg: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing bswap result width");
        let bits = match width {
            ScalarWidth::Bool => panic!("bswap does not support i1"),
            ScalarWidth::Narrow(8) => {
                self.replace_with_aliases(inst, &[arg]);
                return;
            }
            ScalarWidth::Narrow(bits) => bits,
            ScalarWidth::Full256 => 256,
        };
        let mut word = arg;
        for half in iter::successors(Some(bits / 2), |&half| (half > 8).then_some(half / 2)) {
            let shift = self.shift_value(half);
            let lane = low_mask(half);
            let mask = (0..bits)
                .step_by(usize::from(half) * 2)
                .fold(U256::zero(), |mask, offset| {
                    mask | (lane << usize::from(offset))
                });
            let mask = self.imm_i256(mask);
            let high = self.insert_before_one(
                inst,
                arith::Shr::new(self.evm_inst_set(), shift, word),
                Type::I256,
                Some(width),
            );
            let high = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), high, mask),
                Type::I256,
                Some(width),
            );
            let low = self.insert_before_one(
                inst,
                And::new(self.evm_inst_set(), word, mask),
                Type::I256,
                Some(width),
            );
            let low = self.insert_before_one(
                inst,
                arith::Shl::new(self.evm_inst_set(), shift, low),
                Type::I256,
                Some(width),
            );
            word = self.insert_before_one(
                inst,
                Or::new(self.evm_inst_set(), high, low),
                Type::I256,
                Some(width),
            );
        }
        self.replace_with_aliases(inst, &[word]);
    }

    /// `CLZ` counts the zeros of the whole word, and a canonical narrow value
    /// is zero above its width, so its count is `CLZ` less the bits above the
    /// width. A bool has a leading zero when it is zero.
    fn rewrite_clz(&mut self, inst: InstId, arg: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing clz result width");
        let result = match width {
            ScalarWidth::Full256 => return,
            ScalarWidth::Bool => self.insert_before_one(
                inst,
                IsZero::new(self.evm_inst_set(), arg),
                Type::I1,
                Some(width),
            ),
            ScalarWidth::Narrow(bits) => {
                let count = self.insert_before_one(
                    inst,
                    logic::Clz::new(self.evm_inst_set(), arg),
                    Type::I256,
                    Some(ScalarWidth::Full256),
                );
                let above = self.imm_i256(U256::from(256 - bits));
                self.insert_before_one(
                    inst,
                    Sub::new(self.evm_inst_set(), count, above),
                    Type::I256,
                    Some(width),
                )
            }
        };
        self.replace_with_aliases(inst, &[result]);
    }

    /// The EVM has no trailing-zero count. The bits below the lowest set bit
    /// of `x`, `(x - 1) & !x` within the width, are as many as its trailing
    /// zeros, and `CLZ` counts the rest of the word; zero gives all of the
    /// width's bits. A bool has a trailing zero when it is zero.
    fn rewrite_ctz(&mut self, inst: InstId, arg: ValueId) {
        let width = self
            .single_result_width(inst)
            .expect("missing ctz result width");
        let flipped = match width {
            ScalarWidth::Bool => {
                let result = self.insert_before_one(
                    inst,
                    IsZero::new(self.evm_inst_set(), arg),
                    Type::I1,
                    Some(width),
                );
                self.replace_with_aliases(inst, &[result]);
                return;
            }
            ScalarWidth::Narrow(bits) => {
                let mask = self.mask_value(bits);
                self.insert_before_one(
                    inst,
                    Xor::new(self.evm_inst_set(), arg, mask),
                    Type::I256,
                    Some(width),
                )
            }
            ScalarWidth::Full256 => self.insert_before_one(
                inst,
                logic::Not::new(self.evm_inst_set(), arg),
                Type::I256,
                Some(width),
            ),
        };
        let one = self.one_i256();
        let below = self.insert_before_one(
            inst,
            Sub::new(self.evm_inst_set(), arg, one),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let low = self.insert_before_one(
            inst,
            And::new(self.evm_inst_set(), below, flipped),
            Type::I256,
            Some(width),
        );
        let leading = self.insert_before_one(
            inst,
            logic::Clz::new(self.evm_inst_set(), low),
            Type::I256,
            Some(ScalarWidth::Full256),
        );
        let word_bits = self.imm_i256(U256::from(256));
        let result = self.insert_before_one(
            inst,
            Sub::new(self.evm_inst_set(), word_bits, leading),
            Type::I256,
            Some(width),
        );
        self.replace_with_aliases(inst, &[result]);
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
                let result = self.word_to_width(inst, raw, width);
                self.replace_with_aliases(inst, &[result]);
            }
        }
    }

    /// The value of `width` that `inst` gives for `word`: its low bits, or for an `i1` its low
    /// bit.
    fn word_to_width(&mut self, inst: InstId, word: ValueId, width: ScalarWidth) -> ValueId {
        if width == ScalarWidth::Bool {
            self.bool_from_word(inst, word)
        } else {
            self.normalize_and_retag_width(inst, word, width)
        }
    }

    /// The `i1` that `inst` reads from `word`: the word itself when only stores of it as an `i1`
    /// use it, or else its low bit, which a `bitcast` to `i1` keeps.
    fn bool_from_word(&mut self, inst: InstId, word: ValueId) -> ValueId {
        let result = self
            .func
            .dfg
            .inst_result(inst)
            .expect("an `i1` read has a result");
        if self.bool_word_copies.contains(&result) {
            self.bool_word_copies.insert(word);
            return word;
        }
        self.insert_before_one(
            inst,
            Bitcast::new(self.evm_inst_set(), word, Type::I1),
            Type::I1,
            Some(ScalarWidth::Bool),
        )
    }

    /// Masks the word a narrow integer freeze makes concrete, and lowers `freeze undef`. The zero
    /// that replaces `freeze undef` may be an immediate no value had before; it takes the freeze's
    /// width.
    fn rewrite_freeze(&mut self, inst: InstId) {
        let width = self.single_result_width(inst);
        let arg = *downcast::<&Freeze>(self.evm_inst_set(), self.func.dfg.inst(inst))
            .expect("a freeze")
            .arg();
        // A `zero` is a constant, and a frozen constant is itself.
        if matches!(self.func.dfg.value(arg), Value::Zero { .. }) {
            self.replace_with_aliases(inst, &[arg]);
            return;
        }
        // A narrow word is a value of its type or holds the unspecified value, and `freeze` makes
        // it a value of its type. The mask is on a word-typed freeze, so it is not skipped on the
        // width the argument is tagged with; known bits may drop it later.
        if let Some(width @ ScalarWidth::Narrow(_)) = width
            && !matches!(self.func.dfg.value(arg), Value::Undef { .. })
        {
            let frozen = self.insert_before_one(
                inst,
                Freeze::new(self.evm_inst_set(), arg),
                Type::I256,
                Some(ScalarWidth::Full256),
            );
            let result = self.normalize_and_retag_width(inst, frozen, width);
            self.replace_with_aliases(inst, &[result]);
            return;
        }
        if let Some(lowered) = lower_frozen_undef(self.func, inst)
            && self.width_of(lowered).is_none()
        {
            self.provenance[lowered] = width;
        }
    }

    /// Reads an `i1` member of an aggregate as the word it is, then keeps its low bit through a
    /// `bitcast` to `i1`.
    fn rewrite_bool_member_read(&mut self, inst: InstId) {
        let is = self.evm_inst_set();
        let raw = if let Some(extract) = downcast::<&ExtractValue>(is, self.func.dfg.inst(inst)) {
            let (dest, idx) = (*extract.dest(), *extract.idx());
            self.insert_before_one(
                inst,
                ExtractValue::new(is, dest, idx),
                Type::I256,
                Some(ScalarWidth::Full256),
            )
        } else {
            let from = *downcast::<&Bitcast>(is, self.func.dfg.inst(inst))
                .expect("an `i1` member read is an extract or a bitcast")
                .from();
            self.insert_before_one(
                inst,
                Bitcast::new(is, from, Type::I256),
                Type::I256,
                Some(ScalarWidth::Full256),
            )
        };
        let result = self.bool_from_word(inst, raw);
        self.replace_with_aliases(inst, &[result]);
    }

    /// The word that `inst` stores for `value`, an `i1`: the word a copied `i1` was read from, or
    /// else the `i1` widened through a `bitcast`.
    fn word_from_bool(&mut self, inst: InstId, value: ValueId) -> ValueId {
        if self.bool_word_copies.contains(&value) {
            return value;
        }
        self.insert_before_one(
            inst,
            Bitcast::new(self.evm_inst_set(), value, Type::I256),
            Type::I256,
            Some(ScalarWidth::Full256),
        )
    }

    /// Builds an `agg.make` of the legalized type, whose `i1` members are words: an `i1`
    /// operand is the word it was copied from or widens through a `bitcast`, as one inserted
    /// does. An `undef.i1` becomes `undef.i256`; memory legalization stores nothing for it, as
    /// for any `undef` operand, and a read keeps the low bit of whatever word the slot holds, an
    /// `i1` either way.
    fn legalize_agg_make(&mut self, inst: InstId, make: AggMake) {
        let values = make
            .values()
            .iter()
            .map(|&value| {
                if self.func.dfg.value_ty(value) != Type::I1 {
                    value
                } else if matches!(self.func.dfg.value(value), Value::Undef { .. }) {
                    self.func.dfg.make_undef_value(Type::I256)
                } else if matches!(self.func.dfg.value(value), Value::Zero { .. }) {
                    self.func.dfg.make_zero_value(Type::I256)
                } else {
                    self.word_from_bool(inst, value)
                }
            })
            .collect();
        let ty = self.types.legalize_type(self.ctx, *make.ty());
        self.func.dfg.replace_inst(
            inst,
            Box::new(AggMake::new_unchecked(self.evm_inst_set(), ty, values)),
        );
    }

    /// Widens an `i1` put into an aggregate, whose `i1` members are words.
    fn widen_aggregate_member(&mut self, inst: InstId) {
        let is = self.evm_inst_set();
        if let Some(insert) = downcast::<&InsertValue>(is, self.func.dfg.inst(inst)) {
            let (dest, idx, value) = (*insert.dest(), *insert.idx(), *insert.value());
            let word = self.word_from_bool(inst, value);
            self.func
                .dfg
                .replace_inst(inst, Box::new(InsertValue::new(is, dest, idx, word)));
        } else {
            let bitcast = *downcast::<&Bitcast>(is, self.func.dfg.inst(inst))
                .expect("a widened member is inserted or bitcast");
            let (from, ty) = (*bitcast.from(), *bitcast.ty());
            let word = self.word_from_bool(inst, from);
            let ty = self.types.legalize_type(self.ctx, ty);
            self.func
                .dfg
                .replace_inst(inst, Box::new(Bitcast::new(is, word, ty)));
        }
    }

    fn rewrite_mstore(&mut self, inst: InstId, addr: ValueId, value: ValueId, ty: Type) {
        // Memory holds words: an `i1` is stored as the word it widens to, and a narrower integer
        // is already a word of its type.
        let (value, ty) = match self.types.legalize_type(self.ctx, ty) {
            Type::I1 => (self.word_from_bool(inst, value), Type::I256),
            ty => (value, ty),
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
    use super::{legalize_evm_section, operand_uses};
    use sonatina_ir::{
        Function, InstSetExt,
        ir_writer::FuncWriter,
        isa::{Isa, evm::Evm},
        module::FuncRef,
    };
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

    const FROZEN_UNDEF: &str = r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
block0:
    v0.*i256 = freeze undef.*i256;
    v1.i256 = ptr_to_int v0 i256;
    v2.i256 = freeze undef.i256;
    v3.i256 = add v1 v2;
    return v3;
}
"#;

    fn assert_frozen_undef_lowered(dumped: &str) {
        assert!(!dumped.contains("freeze"), "{dumped}");
        assert!(
            dumped.contains("v0.*i256 = int_to_ptr 0.i256 *i256;"),
            "{dumped}"
        );
        assert!(dumped.contains("add v1 0.i256;"), "{dumped}");
    }

    #[test]
    fn memory_copies_lower_to_mcopy() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256, v2.i256) {
block0:
    memcopy v0 v1 v2;
    return;
}
"#,
            "entry",
        );
        assert!(dumped.contains("evm_mcopy v0 v1 v2;"), "{dumped}");
        assert!(!dumped.contains("memcopy"), "{dumped}");
    }

    #[test]
    fn frozen_undef_pointers_lower_to_null() {
        assert_frozen_undef_lowered(&legalize_and_dump(FROZEN_UNDEF, "entry"));
    }

    #[test]
    fn late_frozen_undef_pointers_lower_to_null() {
        let parsed = parse(FROZEN_UNDEF);
        let func_ref = find_func(&parsed, "entry");
        let dumped = parsed.module.func_store.modify(func_ref, |function| {
            super::lower_late_freezes(function);
            dump_func(function, func_ref)
        });
        assert_frozen_undef_lowered(&dumped);
    }

    #[test]
    fn late_freezes_of_frozen_values_lower() {
        let parsed = parse(
            r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
block0:
    v0.i256 = freeze undef.i256;
    v1.i256 = freeze v0;
    return v1;
}
"#,
        );
        let func_ref = find_func(&parsed, "entry");
        let dumped = parsed.module.func_store.modify(func_ref, |function| {
            super::lower_late_freezes(function);
            dump_func(function, func_ref)
        });
        assert!(dumped.contains("return 0.i256;"), "{dumped}");
    }

    /// A freeze of a value that may be unspecified stays until the last IR
    /// pass: `br v2` would branch on `undef` on the path from `block1`.
    const FROZEN_PHI: &str = r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v2.i256 = phi (undef.i256 block1) (v1 block2);
    v3.i256 = freeze v2;
    br v3 block4 block5;
block4:
    return 1.i256;
block5:
    return 2.i256;
}
"#;

    #[test]
    fn freezes_of_values_stay_through_legalization() {
        let dumped = legalize_and_dump(FROZEN_PHI, "entry");
        assert!(dumped.contains("v3.i256 = freeze v2;"), "{dumped}");
        assert!(dumped.contains("br v3 block4 block5;"), "{dumped}");
    }

    #[test]
    fn late_freezes_of_values_lower_to_their_argument() {
        let parsed = parse(FROZEN_PHI);
        let func_ref = find_func(&parsed, "entry");
        let dumped = parsed.module.func_store.modify(func_ref, |function| {
            super::lower_late_freezes(function);
            dump_func(function, func_ref)
        });
        assert!(!dumped.contains("freeze"), "{dumped}");
        assert!(dumped.contains("br v2 block4 block5;"), "{dumped}");
    }

    /// The xor form depends on both arms: unfrozen, `undef` in the arm not
    /// chosen would make the branch on the result undefined.
    #[test]
    fn selects_freeze_their_arms() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    v2.i256 = select v0 v1 undef.i256;
    br v2 block1 block2;
block1:
    return 1.i256;
block2:
    return 2.i256;
}
"#,
            "entry",
        );
        assert!(dumped.contains("= freeze v1;"), "{dumped}");
        assert!(dumped.contains("= freeze undef.i256;"), "{dumped}");
        assert!(!dumped.contains("select"), "{dumped}");
        assert!(!dumped.contains("xor v1"), "{dumped}");
        assert!(!dumped.contains("xor undef"), "{dumped}");
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

    #[test]
    fn full_width_power_of_two_products_use_high_bit_checks() {
        for shift in [1, 5, 64, 128, 255] {
            let constant = sonatina_ir::U256::one() << shift;
            for swapped in [false, true] {
                let operands = if swapped {
                    format!("{constant}.i256 v0")
                } else {
                    format!("v0 {constant}.i256")
                };
                let source = format!(
                    "target = \"evm-ethereum-osaka\"\nfunc public %entry(v0.i256) -> i256 {{\nblock0:\n (v1.i256, v2.i1) = umulo {operands};\n v3.i256 = zext v2 i256;\n v4.i256 = add v1 v3;\n return v4;\n}}"
                );
                let dumped = legalize_and_dump(&source, "entry");
                assert!(dumped.contains(&format!("shl {shift}.i256 v0")), "{dumped}");
                assert!(
                    dumped.contains(&format!("shr {}.i256 v0", 256 - shift)),
                    "{dumped}"
                );
                assert!(!dumped.contains("evm_udiv"), "{dumped}");
                let source = format!(
                    "target = \"evm-ethereum-osaka\"\nfunc public %entry(v0.i256) -> i256 {{\nblock0:\n v1.i256 = umulsat {operands};\n return v1;\n}}"
                );
                let dumped = legalize_and_dump(&source, "entry");
                assert!(
                    dumped.contains(&format!("shr {}.i256 v0", 256 - shift)),
                    "{dumped}"
                );
                assert!(!dumped.contains("evm_udiv"), "{dumped}");
            }
        }
    }

    #[test]
    fn widened_small_products_keep_overflow_proven_false() {
        let dumped = legalize_and_dump(
            r#"
target = "evm-ethereum-osaka"
func public %entry(v0.i8) -> i1 {
block0:
    v1.i256 = zext v0 i256;
    (v2.i256, v3.i1) = umulo v1 4.i256;
    return v3;
}
"#,
            "entry",
        );
        assert!(dumped.contains("return 0.i1;"), "{dumped}");
    }
    #[test]
    fn proven_false_overflow_flag_can_be_zero_extended() {
        assert_proven_false_overflow_flag_can_be_extended("zext");
    }

    #[test]
    fn proven_false_overflow_flag_can_be_sign_extended() {
        assert_proven_false_overflow_flag_can_be_extended("sext");
    }

    fn assert_proven_false_overflow_flag_can_be_extended(extension: &str) {
        for swapped in [false, true] {
            let operands = if swapped { "4.i256 v1" } else { "v1 4.i256" };
            // No pre-existing i1 constant may supply the new false flag's width.
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %entry(v0.i8) -> i256 {{\nblock0:\n v1.i256 = zext v0 i256;\n (v2.i256, v3.i1) = umulo {operands};\n v4.i256 = {extension} v3 i256;\n return v4;\n}}"
            );
            let dumped = legalize_and_dump(&source, "entry");
            assert!(!dumped.contains("umulo"), "{dumped}");
            assert!(
                !dumped.contains(" = zext ") && !dumped.contains(" = sext "),
                "{dumped}"
            );
            assert!(dumped.contains("0.i1"), "{dumped}");
        }
    }

    /// Every instruction with an operand that sets what an effect does, one of each.
    const EFFECT_OPERANDS: &str = r#"
target = "evm-ethereum-osaka"

func public %accesses(v0.i256, v1.*i256) {
    block0:
        v2.i256 = mload v1 i256;
        mstore v1 v0 i256;
        memzero v1 v0;
        memcopy v1 v1 v0;
        v3.*i8 = mem.alloc_dynamic v0;
        v4.i256 = evm_mload v0;
        evm_mstore v0 v0;
        evm_mstore8 v0 v0;
        v5.i256 = evm_sload v0;
        evm_sstore v0 v0;
        v6.i256 = evm_tload v0;
        evm_tstore v0 v0;
        v7.i256 = evm_keccak256 v0 v0;
        evm_log0 v0 v0;
        evm_log1 v0 v0 v0;
        evm_log2 v0 v0 v0 v0;
        evm_log3 v0 v0 v0 v0 v0;
        evm_log4 v0 v0 v0 v0 v0 v0;
        evm_mcopy v0 v0 v0;
        v8.*i8 = evm_malloc v0;
        v9.i256 = evm_calldata_load v0;
        v10.i256 = evm_code_load v0;
        evm_calldata_copy v0 v0 v0;
        evm_code_copy v0 v0 v0;
        evm_return_data_copy v0 v0 v0;
        evm_ext_code_copy v0 v0 v0 v0;
        v11.i256 = evm_create v0 v0 v0;
        v12.i256 = evm_create2 v0 v0 v0 v0;
        v13.i256 = evm_call v0 v0 v0 v0 v0 v0 v0;
        v14.i256 = evm_call_code v0 v0 v0 v0 v0 v0 v0;
        v15.i256 = evm_delegate_call v0 v0 v0 v0 v0 v0;
        v16.i256 = evm_static_call v0 v0 v0 v0 v0 v0;
        evm_return v0 v0;
}

func public %reverts(v0.i256) {
    block0:
        evm_revert v0 v0;
}

func public %self_destructs(v0.i256) {
    block0:
        evm_self_destruct v0;
}
"#;

    #[test]
    fn operand_uses_match_operands() {
        let parsed = parse(EFFECT_OPERANDS);
        let is = Evm::new(parsed.module.ctx.triple).inst_set();
        let mut classified = 0;
        for func_ref in parsed.module.funcs() {
            parsed.module.func_store.view(func_ref, |function| {
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        let data = function.dfg.inst(inst);
                        let Some(uses) = operand_uses(is.resolve_inst(data)) else {
                            continue;
                        };
                        assert_eq!(
                            uses.len(),
                            data.collect_values().len(),
                            "operand uses of `{}`",
                            data.as_text()
                        );
                        classified += 1;
                    }
                }
            });
        }
        // Every kind `operand_uses` gives a list for occurs above.
        assert_eq!(classified, 35);
    }
}
