use crate::Type;

#[derive(Debug)]
pub struct TargetIsa {
    type_provider: Box<dyn IsaSpecificTypeProvider>,
}

impl TargetIsa {
    pub fn new(type_provider: Box<dyn IsaSpecificTypeProvider>) -> Self {
        Self { type_provider }
    }
    pub fn type_provider(&self) -> &dyn IsaSpecificTypeProvider {
        self.type_provider.as_ref()
    }
}

pub trait IsaSpecificTypeProvider: std::fmt::Debug {
    fn hash_type(&self) -> Type;
    fn address_type(&self) -> Type;
    fn balance_type(&self) -> Type;
    fn gas_type(&self) -> Type;
}
