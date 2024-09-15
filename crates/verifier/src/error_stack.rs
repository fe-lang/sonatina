use cranelift_entity::{PrimaryMap, SecondaryMap};
use smallvec::SmallVec;
use sonatina_ir::{module::FuncRef, types::CompoundType, Block, Function, Insn, Value};

use crate::error::{kind::IrSource, Error, ErrorData, ErrorRef};

#[derive(Debug, Default)]
pub struct ErrorStack {
    pub block: SecondaryMap<Block, SmallVec<[ErrorRef; 8]>>,
    pub insn: SecondaryMap<Insn, SmallVec<[ErrorRef; 8]>>,
    pub callee: SecondaryMap<FuncRef, SmallVec<[ErrorRef; 8]>>,
    pub ssa: SecondaryMap<Value, SmallVec<[ErrorRef; 8]>>,
    pub ty: SmallVec<[ErrorRef; 8]>,
    pub cmpd_ty: SecondaryMap<CompoundType, SmallVec<[ErrorRef; 8]>>,
    pub errors: PrimaryMap<ErrorRef, ErrorData>,
}

impl ErrorStack {
    pub fn push(&mut self, err: ErrorData) -> ErrorRef {
        let ir_src = err.kind.ir_source();
        let err_ref = self.errors.push(err);
        match ir_src {
            IrSource::Block(b) => self.block[b].push(err_ref),
            IrSource::Insn(i) => self.insn[i].push(err_ref),
            IrSource::Callee(f) => self.callee[f].push(err_ref),
            IrSource::Value(v) => self.ssa[v].push(err_ref),
            IrSource::Type => self.ty.push(err_ref),
            IrSource::CompoundType(cmpd_ty) => self.cmpd_ty[cmpd_ty].push(err_ref),
        }

        err_ref
    }

    pub fn block_errs_iter<'a: 'b, 'b>(
        &'b self,
        func: &'a Function,
    ) -> impl Iterator<Item = Error<'a>> + 'b {
        self.block.values().flat_map(|errs| {
            errs.iter()
                .map(|err_ref| Error::new(self.errors[*err_ref], func))
        })
    }

    pub fn insn_errs_iter<'a: 'b, 'b>(
        &'b self,
        func: &'a Function,
    ) -> impl Iterator<Item = Error<'a>> + 'b {
        self.insn.values().flat_map(|errs| {
            errs.iter()
                .map(|err_ref| Error::new(self.errors[*err_ref], func))
        })
    }

    pub fn callee_errs_iter<'a: 'b, 'b>(
        &'b self,
        func: &'a Function,
    ) -> impl Iterator<Item = Error<'a>> + 'b {
        self.callee.values().flat_map(|errs| {
            errs.iter()
                .map(|err_ref| Error::new(self.errors[*err_ref], func))
        })
    }

    pub fn ssa_errs_iter<'a: 'b, 'b>(
        &'b self,
        func: &'a Function,
    ) -> impl Iterator<Item = Error<'a>> + 'b {
        self.ssa.values().flat_map(|errs| {
            errs.iter()
                .map(|err_ref| Error::new(self.errors[*err_ref], func))
        })
    }

    pub fn ty_errs_iter<'a: 'b, 'b>(
        &'b self,
        func: &'a Function,
    ) -> impl Iterator<Item = Error<'a>> + 'b {
        self.ty
            .iter()
            .map(|err_ref| Error::new(self.errors[*err_ref], func))
    }
}
