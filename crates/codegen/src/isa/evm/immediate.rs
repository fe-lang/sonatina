use smallvec::{SmallVec, smallvec};
use sonatina_ir::{I256, Immediate, U256};

// Shifted materialization saves deploy bytes but pays an extra runtime SHL.
// Require a clear win so this only fires for large left-aligned constants.
const SHIFTED_IMMEDIATE_MIN_BYTE_SAVINGS: u32 = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ImmediateMaterializationCost {
    pub(crate) gas: u32,
    pub(crate) bytes: u32,
}

impl ImmediateMaterializationCost {
    fn add(self, rhs: Self) -> Self {
        Self {
            gas: self.gas + rhs.gas,
            bytes: self.bytes + rhs.bytes,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ImmediateMaterializationPlan {
    Plain(SmallVec<[u8; 8]>),
    SignExtend(SmallVec<[u8; 8]>),
    Not(SmallVec<[u8; 8]>),
    Shl {
        value: SmallVec<[u8; 8]>,
        shift: SmallVec<[u8; 4]>,
    },
}

impl ImmediateMaterializationPlan {
    pub(crate) fn cost(&self) -> ImmediateMaterializationCost {
        match self {
            Self::Plain(bytes) => push_cost(bytes),
            Self::SignExtend(bytes) => push_cost(bytes)
                .add(push_cost(&u32_to_be((bytes.len() - 1) as u32)))
                .add(ImmediateMaterializationCost { gas: 5, bytes: 1 }),
            Self::Not(bytes) => {
                push_cost(bytes).add(ImmediateMaterializationCost { gas: 3, bytes: 1 })
            }
            Self::Shl { value, shift } => push_cost(value)
                .add(push_cost(shift))
                .add(ImmediateMaterializationCost { gas: 3, bytes: 1 }),
        }
    }

    pub(crate) fn byte_len(&self) -> usize {
        self.cost().bytes as usize
    }
}

pub(crate) fn immediate_materialization_plan(imm: Immediate) -> ImmediateMaterializationPlan {
    let baseline = baseline_materialization_plan(imm);
    shifted_materialization_plan(imm.as_i256(), &baseline).unwrap_or(baseline)
}

pub(crate) fn immediate_materialization_cost_i256(value: I256) -> ImmediateMaterializationCost {
    immediate_materialization_plan_i256(value).cost()
}

pub(crate) fn immediate_materialization_code_len(imm: Immediate) -> usize {
    immediate_materialization_plan(imm).byte_len()
}

fn immediate_materialization_plan_i256(value: I256) -> ImmediateMaterializationPlan {
    let baseline = baseline_i256_materialization_plan(value);
    shifted_materialization_plan(value, &baseline).unwrap_or(baseline)
}

fn baseline_materialization_plan(imm: Immediate) -> ImmediateMaterializationPlan {
    if imm.is_zero() {
        return ImmediateMaterializationPlan::Plain(smallvec![0]);
    }

    let bytes = immediate_bytes(imm);
    if let Some(bytes) = compact_not_push_bytes(imm, &bytes) {
        return ImmediateMaterializationPlan::Not(bytes);
    }
    if imm.is_negative() && bytes.len() < 32 {
        ImmediateMaterializationPlan::SignExtend(bytes)
    } else {
        ImmediateMaterializationPlan::Plain(bytes)
    }
}

fn baseline_i256_materialization_plan(value: I256) -> ImmediateMaterializationPlan {
    if value.is_zero() {
        return ImmediateMaterializationPlan::Plain(smallvec![0]);
    }

    let bytes = shrink_bytes(&value.to_u256().to_big_endian());
    if let Some(bytes) = compact_not_i256_bytes(value, &bytes) {
        return ImmediateMaterializationPlan::Not(bytes);
    }
    if value.is_negative() && bytes.len() < 32 {
        ImmediateMaterializationPlan::SignExtend(bytes)
    } else {
        ImmediateMaterializationPlan::Plain(bytes)
    }
}

fn shifted_materialization_plan(
    value: I256,
    baseline: &ImmediateMaterializationPlan,
) -> Option<ImmediateMaterializationPlan> {
    let word = value.to_u256();
    if word.is_zero() {
        return None;
    }

    let shift_bits = trailing_zero_bits(word);
    if shift_bits == 0 {
        return None;
    }

    let base = word >> shift_bits as usize;
    debug_assert!(!base.is_zero());
    let shifted = ImmediateMaterializationPlan::Shl {
        value: u256_to_be(&base),
        shift: u32_to_be(shift_bits),
    };
    let baseline_cost = baseline.cost();
    let shifted_cost = shifted.cost();
    (baseline_cost.bytes >= shifted_cost.bytes + SHIFTED_IMMEDIATE_MIN_BYTE_SAVINGS)
        .then_some(shifted)
}

fn immediate_bytes(imm: Immediate) -> SmallVec<[u8; 8]> {
    match imm {
        Immediate::I1(v) => smallvec![v as u8],
        Immediate::I8(v) => SmallVec::from_slice(&v.to_be_bytes()),
        Immediate::I16(v) => shrink_bytes(&v.to_be_bytes()),
        Immediate::I32(v) => shrink_bytes(&v.to_be_bytes()),
        Immediate::I64(v) => shrink_bytes(&v.to_be_bytes()),
        Immediate::I128(v) => shrink_bytes(&v.to_be_bytes()),
        Immediate::I256(v) => shrink_bytes(&v.to_u256().to_big_endian()),
        Immediate::EnumTag { value, .. } => shrink_bytes(&value.to_u256().to_big_endian()),
    }
}

fn compact_not_push_bytes(imm: Immediate, bytes: &[u8]) -> Option<SmallVec<[u8; 8]>> {
    let Immediate::I256(value) = imm else {
        return None;
    };
    compact_not_i256_bytes(value, bytes)
}

fn compact_not_i256_bytes(value: I256, bytes: &[u8]) -> Option<SmallVec<[u8; 8]>> {
    if !value.is_negative() {
        return None;
    }

    let not_bytes = u256_to_be(&!value.to_u256());
    let current_len = baseline_i256_push_len(value, bytes);
    let not_len = push_len(&not_bytes) + 1;
    (not_len < current_len).then_some(not_bytes)
}

fn baseline_i256_push_len(value: I256, bytes: &[u8]) -> usize {
    let mut len = push_len(bytes);
    if value.is_negative() && bytes.len() < 32 {
        len += push_len(&u32_to_be((bytes.len() - 1) as u32)) + 1;
    }
    len
}

fn push_cost(bytes: &[u8]) -> ImmediateMaterializationCost {
    if bytes == [0] {
        ImmediateMaterializationCost { gas: 2, bytes: 1 }
    } else {
        ImmediateMaterializationCost {
            gas: 3,
            bytes: bytes.len() as u32 + 1,
        }
    }
}

fn push_len(bytes: &[u8]) -> usize {
    push_cost(bytes).bytes as usize
}

fn shrink_bytes(bytes: &[u8]) -> SmallVec<[u8; 8]> {
    assert!(!bytes.is_empty());

    let is_neg = bytes[0].leading_ones() > 0;
    let skip = if is_neg { 0xff } else { 0x00 };
    let mut bytes = bytes
        .iter()
        .copied()
        .skip_while(|b| *b == skip)
        .collect::<SmallVec<[u8; 8]>>();

    if is_neg && bytes.first().map(|&b| b < 0x80).unwrap_or(true) {
        bytes.insert(0, 0xff);
    }
    bytes
}

fn trailing_zero_bits(value: U256) -> u32 {
    let bytes = value.to_big_endian();
    let mut bits = 0u32;
    for byte in bytes.into_iter().rev() {
        if byte == 0 {
            bits += 8;
        } else {
            bits += byte.trailing_zeros();
            break;
        }
    }
    debug_assert!(bits < 256);
    bits
}

pub(crate) fn u32_to_be(num: u32) -> SmallVec<[u8; 4]> {
    if num == 0 {
        smallvec![0]
    } else {
        num.to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect()
    }
}

pub(crate) fn u256_to_be(num: &U256) -> SmallVec<[u8; 8]> {
    if num.is_zero() {
        smallvec![0]
    } else {
        let b = num.to_big_endian();
        b.into_iter().skip_while(|b| *b == 0).collect()
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Type;

    use super::*;

    #[test]
    fn i256_negative_mask_push_uses_compact_not_form() {
        let mask = Immediate::from_i256(!I256::from(31u8), Type::I256);

        assert_eq!(
            immediate_materialization_plan(mask),
            ImmediateMaterializationPlan::Not(smallvec![0x1f])
        );
    }

    #[test]
    fn i256_negative_one_push_uses_compact_not_form() {
        let minus_one = Immediate::from_i256(I256::from(-1i8), Type::I256);

        assert_eq!(
            immediate_materialization_plan(minus_one),
            ImmediateMaterializationPlan::Not(smallvec![0])
        );
    }

    #[test]
    fn non_i256_negative_push_keeps_signextend_form() {
        assert_eq!(
            immediate_materialization_plan(Immediate::I8(-32)),
            ImmediateMaterializationPlan::SignExtend(smallvec![0xe0])
        );
    }

    #[test]
    fn positive_high_bit_i256_push_stays_plain() {
        let value = Immediate::from_i256(I256::from(0xe0u16), Type::I256);

        assert_eq!(
            immediate_materialization_plan(value),
            ImmediateMaterializationPlan::Plain(smallvec![0xe0])
        );
    }

    #[test]
    fn selector_word_uses_shifted_materialization() {
        let selector = I256::from_u256(U256::from(0x8c379a0u32) << 224usize);
        assert_eq!(
            immediate_materialization_plan(Immediate::I256(selector)),
            ImmediateMaterializationPlan::Shl {
                value: smallvec![0x46, 0x1b, 0xcd],
                shift: smallvec![0xe5],
            }
        );
    }

    #[test]
    fn abi_offset_word_uses_shifted_materialization() {
        let offset = I256::from_u256(U256::from(0x20u8) << 224usize);
        assert_eq!(
            immediate_materialization_plan(Immediate::I256(offset)),
            ImmediateMaterializationPlan::Shl {
                value: smallvec![0x01],
                shift: smallvec![0xe5],
            }
        );
    }

    #[test]
    fn panic_code_word_uses_shifted_materialization() {
        let code = I256::from_u256(U256::from(1u8) << 224usize);
        assert_eq!(
            immediate_materialization_plan(Immediate::I256(code)),
            ImmediateMaterializationPlan::Shl {
                value: smallvec![0x01],
                shift: smallvec![0xe0],
            }
        );
    }

    #[test]
    fn small_shifted_constant_stays_plain() {
        assert_eq!(
            immediate_materialization_plan(Immediate::I256(I256::from(0x100u16))),
            ImmediateMaterializationPlan::Plain(smallvec![0x01, 0x00])
        );
    }

    #[test]
    fn dense_hash_like_word_stays_plain() {
        let value = I256::from_u256(
            U256::from_dec_str(
                "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            )
            .unwrap(),
        );

        assert!(matches!(
            immediate_materialization_plan(Immediate::I256(value)),
            ImmediateMaterializationPlan::Plain(_)
        ));
    }
}
