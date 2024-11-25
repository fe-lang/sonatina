use std::{fmt, io};

use cranelift_entity::PrimaryMap;
use rustc_hash::FxHashMap;

use crate::{ir_writer::WriteWithModule, module::ModuleCtx, Immediate, Linkage, Type};

#[derive(Debug, Default)]
pub struct GlobalVariableStore {
    gv_data: PrimaryMap<GlobalVariable, GlobalVariableData>,
    symbols: FxHashMap<String, GlobalVariable>,
}

impl GlobalVariableStore {
    pub fn make_gv(&mut self, gv_data: GlobalVariableData) -> GlobalVariable {
        match self.symbols.entry(gv_data.symbol.to_string()) {
            std::collections::hash_map::Entry::Occupied(_) => {
                panic!("duplicate global symbol `{}`", gv_data.symbol);
            }
            std::collections::hash_map::Entry::Vacant(v) => {
                let gv = self.gv_data.push(gv_data);
                v.insert(gv);
                gv
            }
        }
    }

    pub fn gv_data(&self, gv: GlobalVariable) -> &GlobalVariableData {
        &self.gv_data[gv]
    }

    pub fn gv_by_symbol(&self, symbol: &str) -> Option<GlobalVariable> {
        self.symbols.get(symbol).copied()
    }

    pub fn init_data(&self, gv: GlobalVariable) -> Option<&GvInitializer> {
        self.gv_data[gv].data.as_ref()
    }

    pub fn is_const(&self, gv: GlobalVariable) -> bool {
        self.gv_data[gv].is_const
    }

    pub fn ty(&self, gv: GlobalVariable) -> Type {
        self.gv_data[gv].ty
    }

    pub fn all_gv_data(&self) -> impl Iterator<Item = &GlobalVariableData> {
        self.gv_data.values()
    }
}

/// An opaque reference to [`GlobalVariableData`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct GlobalVariable(pub u32);
cranelift_entity::entity_impl!(GlobalVariable);

impl WriteWithModule for GlobalVariable {
    fn write(&self, module: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        module.with_gv_store(|s| s.gv_data(*self).write(module, w))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GlobalVariableData {
    pub symbol: String,
    pub ty: Type,
    pub linkage: Linkage,
    pub is_const: bool,
    pub data: Option<GvInitializer>,
}

impl GlobalVariableData {
    pub fn new(
        symbol: String,
        ty: Type,
        linkage: Linkage,
        is_const: bool,
        data: Option<GvInitializer>,
    ) -> Self {
        Self {
            symbol,
            ty,
            linkage,
            is_const,
            data,
        }
    }

    pub fn constant(symbol: String, ty: Type, linkage: Linkage, data: GvInitializer) -> Self {
        Self {
            symbol,
            ty,
            linkage,
            is_const: true,
            data: Some(data),
        }
    }
}

impl WriteWithModule for GlobalVariableData {
    fn write(&self, module: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        write!(w, "global {} ", self.linkage)?;
        if self.is_const {
            write!(w, "const ")?;
        }
        self.ty.write(module, &mut *w)?;

        write!(w, " %{}", self.symbol)?;
        if let Some(data) = &self.data {
            write!(w, " = {data}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GvInitializer {
    Immediate(Immediate),
    Array(Vec<GvInitializer>),
    Struct(Vec<GvInitializer>),
}

impl GvInitializer {
    pub fn make_imm(data: impl Into<Immediate>) -> Self {
        Self::Immediate(data.into())
    }

    pub fn make_array(data: Vec<GvInitializer>) -> Self {
        Self::Array(data)
    }

    pub fn make_struct(data: Vec<GvInitializer>) -> Self {
        Self::Struct(data)
    }
}

impl fmt::Display for GvInitializer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Immediate(data) => write!(f, "{}", data),
            Self::Array(data) => {
                write!(f, "[")?;
                for (i, v) in data.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Self::Struct(data) => {
                write!(f, "{{")?;
                for (i, v) in data.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{builder::test_util::test_isa, module::ModuleCtx};

    #[test]
    fn display_gv() {
        let ctx = ModuleCtx::new(&test_isa());

        let cv = GvInitializer::make_imm(1618i32);
        let gv = ctx.with_gv_store_mut(|s| {
            s.make_gv(GlobalVariableData::new(
                String::from("foo"),
                Type::I32,
                Linkage::Public,
                true,
                Some(cv),
            ))
        });

        assert_eq!(gv.dump_string(&ctx), "global public const i32 %foo = 1618");
    }

    #[test]
    fn display_gv_array() {
        let ctx = ModuleCtx::new(&test_isa());

        let cv0 = GvInitializer::make_imm(8i32);
        let cv1 = GvInitializer::make_imm(4i32);
        let cv2 = GvInitializer::make_imm(2i32);
        let const_arr = GvInitializer::make_array(vec![cv0, cv1, cv2]);
        let ty = ctx.with_ty_store_mut(|s| s.make_array(Type::I32, 3));
        let gv = ctx.with_gv_store_mut(|s| {
            s.make_gv(GlobalVariableData::new(
                String::from("foo"),
                ty,
                Linkage::Private,
                true,
                Some(const_arr),
            ))
        });

        assert_eq!(
            gv.dump_string(&ctx),
            "global private const [i32; 3] %foo = [8, 4, 2]"
        );
    }
}
