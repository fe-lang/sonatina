use cranelift_entity::PrimaryMap;
use sonatina_ir::{module::FuncRef, Function};

use crate::error::{Error, ErrorData, ErrorRef};

#[derive(Debug, Default)]
pub struct ErrorStack {
    pub fatal_error: Option<ErrorData>,
    pub non_fatal_errors: PrimaryMap<ErrorRef, ErrorData>,
}

impl ErrorStack {
    pub fn push(&mut self, err: ErrorData) -> ErrorRef {
        self.non_fatal_errors.push(err)
    }

    pub fn into_errs_iter(
        self,
        func: &Function,
        func_ref: FuncRef,
    ) -> impl IntoIterator<Item = Error<'_>> {
        self.non_fatal_errors
            .into_iter()
            .map(move |(_, err)| Error::new(err, func, func_ref))
    }
}
