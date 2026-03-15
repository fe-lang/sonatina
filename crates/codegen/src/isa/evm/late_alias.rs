use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstSetExt, Type, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::ModuleCtx,
};

use crate::bitset::BitSet;

#[derive(Clone)]
pub(crate) struct LateValueAliasMap {
    rep_of: SecondaryMap<ValueId, Option<ValueId>>,
}

pub fn canonicalize_alias_value(
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
    value: ValueId,
) -> ValueId {
    let mut current = value;
    loop {
        let next = value_aliases[current].unwrap_or(current);
        if next == current {
            return current;
        }
        current = next;
    }
}

pub(crate) fn normalize_alias_map(
    function: &Function,
    value_aliases: &mut SecondaryMap<ValueId, Option<ValueId>>,
) {
    for value in function.dfg.value_ids() {
        let mut seen: BitSet<ValueId> = BitSet::default();
        let mut path = SmallVec::<[ValueId; 8]>::new();
        let mut current = value;
        let mut rep = None;
        loop {
            if !seen.insert(current) {
                // Invalid alias cycles should not be canonicalized to an arbitrary value from
                // outside the cycle. Keep all traversed values self-canonical.
                for v in path.iter().copied() {
                    value_aliases[v] = Some(v);
                }
                break;
            }
            path.push(current);
            let next = value_aliases[current].unwrap_or(current);
            if next == current {
                rep = Some(current);
                break;
            }
            current = next;
        }
        if let Some(rep) = rep {
            for v in path {
                value_aliases[v] = Some(rep);
            }
        }
    }

    #[cfg(debug_assertions)]
    for value in function.dfg.value_ids() {
        let rep = value_aliases[value].unwrap_or(value);
        debug_assert_eq!(
            value_aliases[rep].unwrap_or(rep),
            rep,
            "value alias map is not one-hop canonical for v{}",
            value.as_u32()
        );
    }
}

impl LateValueAliasMap {
    pub(crate) fn identity(function: &Function) -> Self {
        let mut rep_of: SecondaryMap<ValueId, Option<ValueId>> = SecondaryMap::new();
        for v in function.dfg.value_ids() {
            rep_of[v] = Some(v);
        }
        Self { rep_of }
    }

    pub(crate) fn rep(&self, value: ValueId) -> ValueId {
        canonicalize_alias_value(&self.rep_of, value)
    }

    pub(crate) fn map(&self) -> &SecondaryMap<ValueId, Option<ValueId>> {
        &self.rep_of
    }
}

fn scalar_bit_width(ty: Type, module: &ModuleCtx) -> Option<u16> {
    let bits = match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        Type::EnumTag(_) => return None,
        Type::Unit => 0,
        Type::Compound(_) if ty.is_pointer(module) => 256,
        Type::Compound(_) => return None,
    };
    Some(bits)
}

pub(crate) fn compute_evm_late_aliases(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
) -> LateValueAliasMap {
    let mut aliases = LateValueAliasMap::identity(function);

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let [result] = function.dfg.inst_results(inst) else {
                continue;
            };

            let alias_from = match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
                EvmInstKind::Bitcast(bitcast) => Some(*bitcast.from()),
                EvmInstKind::IntToPtr(int_to_ptr) => {
                    let src = *int_to_ptr.from();
                    let src_bits = scalar_bit_width(function.dfg.value_ty(src), module);
                    (src_bits == Some(256)).then_some(src)
                }
                EvmInstKind::PtrToInt(ptr_to_int) => {
                    let dst_bits = scalar_bit_width(*ptr_to_int.ty(), module);
                    (dst_bits == Some(256)).then_some(*ptr_to_int.from())
                }
                _ => None,
            };

            let Some(from) = alias_from else {
                continue;
            };

            let from_rep = aliases.rep(from);
            aliases.rep_of[*result] = Some(from_rep);
        }
    }

    aliases
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    #[test]
    fn transitive_noop_cast_chain_collapses() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.*i8, v2.i64) {
block0:
    v3.*i8 = int_to_ptr v0 *i8;
    v4.i256 = ptr_to_int v3 i256;
    v5.*i8 = bitcast v4 *i8;
    v6.i64 = ptr_to_int v1 i64;
    v7.*i8 = int_to_ptr v2 *i8;
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("function exists");

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        parsed.module.func_store.view(func_ref, |function| {
            let aliases = compute_evm_late_aliases(function, &parsed.module.ctx, &isa);

            let v = |name: &str| parsed.debug.value(func_ref, name).expect("value exists");

            assert_eq!(aliases.rep(v("v3")), v("v0"));
            assert_eq!(aliases.rep(v("v4")), v("v0"));
            assert_eq!(aliases.rep(v("v5")), v("v0"));

            // Non-noop width-changing casts must not alias.
            assert_eq!(aliases.rep(v("v6")), v("v6"));
            assert_eq!(aliases.rep(v("v7")), v("v7"));
        });
    }
}
