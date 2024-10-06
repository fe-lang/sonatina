use cranelift_entity::PrimaryMap;
use sonatina_ir::Function;

use crate::error::{Error, ErrorData, ErrorRef};

#[derive(Debug, Default)]
pub struct ErrorStack {
    pub errors: PrimaryMap<ErrorRef, ErrorData>,
}

impl ErrorStack {
    pub fn push(&mut self, err: ErrorData) -> ErrorRef {
        self.errors.push(err)
    }

    pub fn into_errs_iter<'a>(self, func: &'a Function) -> impl IntoIterator<Item = Error<'a>> {
        self.errors
            .into_iter()
            .map(|(_, err)| Error::new(err, func))
    }
}
