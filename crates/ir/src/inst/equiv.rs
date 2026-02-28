use std::any::{Any, TypeId};

use smallvec::SmallVec;

use crate::{BlockId, Type, ValueId, module::FuncRef};

use super::{
    Inst,
    cast::{Bitcast, IntToPtr, PtrToInt, Sext, Trunc, Zext},
    control_flow::{Call, Phi},
    data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryInstKind {
    Neg,
    Not,
    IsZero,
    EvmClz,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryInstKind {
    Add,
    Mul,
    Sub,
    Sdiv,
    Udiv,
    Umod,
    Smod,
    Shl,
    Shr,
    Sar,
    Lt,
    Gt,
    Slt,
    Sgt,
    Le,
    Ge,
    Sle,
    Sge,
    Eq,
    Ne,
    And,
    Or,
    Xor,
    EvmUdiv,
    EvmSdiv,
    EvmUmod,
    EvmSmod,
    EvmExp,
    EvmByte,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastInstKind {
    Sext,
    Zext,
    Trunc,
    Bitcast,
    IntToPtr,
    PtrToInt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstClassKind {
    Unary(UnaryInstKind),
    Binary(BinaryInstKind),
    Cast(CastInstKind),
    Phi,
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OwnedInstKey {
    opcode: TypeId,
    opcode_text: &'static str,
    values: SmallVec<[ValueId; 2]>,
    result_ty: Option<Type>,
    cast_ty: Option<Type>,
    phi_args: Vec<(ValueId, BlockId)>,
    callee: Option<FuncRef>,
    opaque_data: Option<OpaqueInstData>,
    kind: InstClassKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OpaqueInstData {
    GetFunctionPtr(FuncRef),
    SymAddr(SymbolRef),
    SymSize(SymbolRef),
}

impl OwnedInstKey {
    pub fn from_inst(inst: &dyn Inst, result_ty: Option<Type>) -> Self {
        let mut key = Self {
            opcode: inst.type_id(),
            opcode_text: inst.as_text(),
            values: inst.collect_values(),
            result_ty,
            cast_ty: cast_ty(inst),
            phi_args: Vec::new(),
            callee: None,
            opaque_data: opaque_data(inst),
            kind: inst.kind(),
        };

        if let Some(phi) = downcast_ref::<Phi>(inst) {
            key.phi_args = phi.args().to_vec();
        }

        if let Some(call) = downcast_ref::<Call>(inst) {
            key.callee = Some(*call.callee());
        }

        key
    }

    pub fn opcode_text(&self) -> &'static str {
        self.opcode_text
    }

    pub fn values(&self) -> &[ValueId] {
        &self.values
    }

    pub fn with_values(&self, values: Vec<ValueId>) -> Option<Self> {
        if matches!(self.kind, InstClassKind::Phi) || self.values.len() != values.len() {
            return None;
        }

        let mut key = self.clone();
        key.values = values.into_iter().collect();
        Some(key)
    }

    pub fn result_ty(&self) -> Option<Type> {
        self.result_ty
    }

    pub fn callee(&self) -> Option<FuncRef> {
        self.callee
    }

    pub fn kind(&self) -> InstClassKind {
        self.kind
    }

    pub fn is_commutative_binary(&self) -> bool {
        matches!(
            self.kind,
            InstClassKind::Binary(
                BinaryInstKind::Add
                    | BinaryInstKind::Mul
                    | BinaryInstKind::Eq
                    | BinaryInstKind::Ne
                    | BinaryInstKind::And
                    | BinaryInstKind::Or
                    | BinaryInstKind::Xor
            )
        )
    }

    pub fn is_opaque(&self) -> bool {
        self.kind == InstClassKind::Opaque
    }

    pub fn unary_arg(&self) -> Option<ValueId> {
        if matches!(self.kind, InstClassKind::Unary(_)) && self.values.len() == 1 {
            Some(self.values[0])
        } else {
            None
        }
    }

    pub fn with_unary_arg(&self, arg: ValueId) -> Option<Self> {
        if !matches!(self.kind, InstClassKind::Unary(_)) || self.values.len() != 1 {
            return None;
        }

        let mut key = self.clone();
        key.values[0] = arg;
        Some(key)
    }

    pub fn binary_args(&self) -> Option<(ValueId, ValueId)> {
        if matches!(self.kind, InstClassKind::Binary(_)) && self.values.len() == 2 {
            Some((self.values[0], self.values[1]))
        } else {
            None
        }
    }

    pub fn with_binary_args(&self, lhs: ValueId, rhs: ValueId) -> Option<Self> {
        if !matches!(self.kind, InstClassKind::Binary(_)) || self.values.len() != 2 {
            return None;
        }

        let mut key = self.clone();
        key.values[0] = lhs;
        key.values[1] = rhs;
        Some(key)
    }

    pub fn cast_arg_ty(&self) -> Option<(ValueId, Type)> {
        if !matches!(self.kind, InstClassKind::Cast(_)) || self.values.len() != 1 {
            return None;
        }

        Some((self.values[0], self.cast_ty?))
    }

    pub fn with_cast_arg(&self, arg: ValueId) -> Option<Self> {
        if !matches!(self.kind, InstClassKind::Cast(_)) || self.values.len() != 1 {
            return None;
        }

        let mut key = self.clone();
        key.values[0] = arg;
        Some(key)
    }

    pub fn phi_args(&self) -> Option<&[(ValueId, BlockId)]> {
        matches!(self.kind, InstClassKind::Phi).then_some(self.phi_args.as_slice())
    }

    pub fn with_phi_args(&self, phi_args: Vec<(ValueId, BlockId)>) -> Option<Self> {
        if !matches!(self.kind, InstClassKind::Phi) {
            return None;
        }

        let mut key = self.clone();
        key.values = phi_args
            .iter()
            .map(|(value, _)| *value)
            .collect::<SmallVec<[ValueId; 2]>>();
        key.phi_args = phi_args;
        Some(key)
    }
}

pub trait InstKeyExt {
    fn owned_key(&self, result_ty: Option<Type>) -> OwnedInstKey;
}

impl InstKeyExt for dyn Inst {
    fn owned_key(&self, result_ty: Option<Type>) -> OwnedInstKey {
        OwnedInstKey::from_inst(self, result_ty)
    }
}

impl<T: Inst> InstKeyExt for T {
    fn owned_key(&self, result_ty: Option<Type>) -> OwnedInstKey {
        OwnedInstKey::from_inst(self, result_ty)
    }
}

fn downcast_ref<T: 'static>(inst: &dyn Inst) -> Option<&T> {
    let any = inst as &dyn Any;
    any.downcast_ref::<T>()
}

fn cast_ty(inst: &dyn Inst) -> Option<Type> {
    if let Some(inst) = downcast_ref::<Sext>(inst) {
        return Some(*inst.ty());
    }
    if let Some(inst) = downcast_ref::<Zext>(inst) {
        return Some(*inst.ty());
    }
    if let Some(inst) = downcast_ref::<Trunc>(inst) {
        return Some(*inst.ty());
    }
    if let Some(inst) = downcast_ref::<Bitcast>(inst) {
        return Some(*inst.ty());
    }
    if let Some(inst) = downcast_ref::<IntToPtr>(inst) {
        return Some(*inst.ty());
    }
    if let Some(inst) = downcast_ref::<PtrToInt>(inst) {
        return Some(*inst.ty());
    }
    None
}

fn opaque_data(inst: &dyn Inst) -> Option<OpaqueInstData> {
    if let Some(inst) = downcast_ref::<GetFunctionPtr>(inst) {
        return Some(OpaqueInstData::GetFunctionPtr(*inst.func()));
    }
    if let Some(inst) = downcast_ref::<SymAddr>(inst) {
        return Some(OpaqueInstData::SymAddr(inst.sym().clone()));
    }
    if let Some(inst) = downcast_ref::<SymSize>(inst) {
        return Some(OpaqueInstData::SymSize(inst.sym().clone()));
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::{
        EmbedSymbol, GlobalVariableRef,
        builder::test_util::test_isa,
        inst::{
            data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
            inst_set::InstSetBase,
        },
        isa::Isa,
        module::FuncRef,
    };

    use super::OwnedInstKey;

    #[test]
    fn opaque_key_distinguishes_get_function_ptr_targets() {
        let isa = test_isa();
        let is = isa.inst_set();
        let i1 = GetFunctionPtr::new(is.has_get_function_ptr().unwrap(), FuncRef::from_u32(1));
        let i2 = GetFunctionPtr::new(is.has_get_function_ptr().unwrap(), FuncRef::from_u32(2));
        let i3 = GetFunctionPtr::new(is.has_get_function_ptr().unwrap(), FuncRef::from_u32(1));

        let k1 = OwnedInstKey::from_inst(&i1, None);
        let k2 = OwnedInstKey::from_inst(&i2, None);
        let k3 = OwnedInstKey::from_inst(&i3, None);
        assert_ne!(k1, k2);
        assert_eq!(k1, k3);
    }

    #[test]
    fn opaque_key_distinguishes_sym_addr_symbol_refs() {
        let isa = test_isa();
        let is = isa.inst_set();
        let by_func = SymAddr::new(
            is.has_sym_addr().unwrap(),
            SymbolRef::Func(FuncRef::from_u32(10)),
        );
        let by_global = SymAddr::new(
            is.has_sym_addr().unwrap(),
            SymbolRef::Global(GlobalVariableRef::from_u32(10)),
        );
        let by_embed = SymAddr::new(
            is.has_sym_addr().unwrap(),
            SymbolRef::Embed(EmbedSymbol::from("foo")),
        );

        assert_ne!(
            OwnedInstKey::from_inst(&by_func, None),
            OwnedInstKey::from_inst(&by_global, None)
        );
        assert_ne!(
            OwnedInstKey::from_inst(&by_global, None),
            OwnedInstKey::from_inst(&by_embed, None)
        );
    }

    #[test]
    fn opaque_key_distinguishes_sym_size_symbol_refs() {
        let isa = test_isa();
        let is = isa.inst_set();
        let by_func = SymSize::new(
            is.has_sym_size().unwrap(),
            SymbolRef::Func(FuncRef::from_u32(10)),
        );
        let by_global = SymSize::new(
            is.has_sym_size().unwrap(),
            SymbolRef::Global(GlobalVariableRef::from_u32(10)),
        );
        let by_embed = SymSize::new(
            is.has_sym_size().unwrap(),
            SymbolRef::Embed(EmbedSymbol::from("foo")),
        );

        assert_ne!(
            OwnedInstKey::from_inst(&by_func, None),
            OwnedInstKey::from_inst(&by_global, None)
        );
        assert_ne!(
            OwnedInstKey::from_inst(&by_global, None),
            OwnedInstKey::from_inst(&by_embed, None)
        );
    }
}
