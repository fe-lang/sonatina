use sonatina_ir::{I256, Immediate, Type, U256};

pub(super) fn evm_scalar_word_bits(imm: Immediate) -> Option<U256> {
    match imm.ty() {
        Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::I256 => {
            Some(imm.zext(Type::I256).as_i256().to_u256())
        }
        Type::EnumTag(_) | Type::Compound(_) | Type::Unit => None,
    }
}

pub(super) fn evm_scalar_word_bytes(imm: Immediate) -> Option<[u8; 32]> {
    Some(evm_scalar_word_bits(imm)?.to_big_endian())
}

pub(super) fn legalize_evm_scalar_immediate(imm: Immediate) -> Option<Immediate> {
    match imm.ty() {
        Type::I1 => Some(imm),
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::I256 => Some(
            Immediate::from_i256(I256::from_u256(evm_scalar_word_bits(imm)?), Type::I256),
        ),
        Type::EnumTag(_) | Type::Compound(_) | Type::Unit => None,
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{I256, Immediate};

    use super::{evm_scalar_word_bytes, legalize_evm_scalar_immediate};

    #[test]
    fn evm_scalar_words_zero_extend_narrow_and_bool_immediates() {
        let word = evm_scalar_word_bytes(Immediate::I16(-2)).expect("narrow scalar should encode");
        assert!(word[..30].iter().all(|&byte| byte == 0));
        assert_eq!(&word[30..], &[0xff, 0xfe]);

        let word = evm_scalar_word_bytes(Immediate::I1(true)).expect("bool should encode");
        assert!(word[..31].iter().all(|&byte| byte == 0));
        assert_eq!(word[31], 1);
    }

    #[test]
    fn legalize_evm_scalar_immediate_uses_the_same_word_bits() {
        assert_eq!(
            legalize_evm_scalar_immediate(Immediate::I1(true)),
            Some(Immediate::I1(true))
        );
        assert_eq!(
            legalize_evm_scalar_immediate(Immediate::I16(-2)),
            Some(Immediate::I256(I256::from(0xfffeu16)))
        );
    }
}
