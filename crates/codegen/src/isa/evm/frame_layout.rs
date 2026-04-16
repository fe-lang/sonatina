use std::num::NonZeroU32;

use super::WORD_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct DynamicFrameLayout {
    local_words: NonZeroU32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct FrameLocalWord(u32);

impl DynamicFrameLayout {
    const LINK_WORDS: u32 = 1;

    pub(crate) fn new(local_words: u32) -> Option<Self> {
        Some(Self {
            local_words: NonZeroU32::new(local_words)?,
        })
    }

    pub(crate) fn local_words(self) -> u32 {
        self.local_words.get()
    }

    pub(crate) fn total_words(self) -> u32 {
        self.local_words()
            .checked_add(Self::LINK_WORDS)
            .expect("dynamic frame size overflow")
    }

    pub(crate) fn frame_bytes(self) -> u32 {
        self.total_words()
            .checked_mul(WORD_BYTES)
            .expect("dynamic frame byte size overflow")
    }

    pub(crate) fn caller_link_sp_relative_bytes(self) -> u32 {
        Self::LINK_WORDS
            .checked_mul(WORD_BYTES)
            .expect("dynamic frame link byte offset overflow")
    }

    pub(crate) fn local_word(self, offset_words: u32) -> Option<FrameLocalWord> {
        (offset_words < self.local_words()).then_some(FrameLocalWord(offset_words))
    }

    pub(crate) fn expect_local_word(self, offset_words: u32, context: &str) -> FrameLocalWord {
        self.local_word(offset_words).unwrap_or_else(|| {
            panic!(
                "{context} frame word offset {offset_words} out of range for local frame words {}",
                self.local_words()
            )
        })
    }

    pub(crate) fn sp_relative_bytes(self, local_word: FrameLocalWord) -> u32 {
        self.total_words()
            .checked_sub(local_word.0)
            .expect("dynamic frame local word offset overflow")
            .checked_mul(WORD_BYTES)
            .expect("dynamic frame local word byte offset overflow")
    }
}

impl FrameLocalWord {
    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::DynamicFrameLayout;

    #[test]
    fn dynamic_frame_layout_rejects_zero_local_words() {
        assert_eq!(DynamicFrameLayout::new(0), None);
    }

    #[test]
    fn dynamic_frame_layout_reports_total_words_and_link_slot() {
        let layout = DynamicFrameLayout::new(3).expect("layout");

        assert_eq!(layout.local_words(), 3);
        assert_eq!(layout.total_words(), 4);
        assert_eq!(layout.frame_bytes(), 128);
        assert_eq!(layout.caller_link_sp_relative_bytes(), 32);
    }

    #[test]
    fn dynamic_frame_layout_computes_sp_relative_bytes_for_local_words() {
        let layout = DynamicFrameLayout::new(3).expect("layout");
        let first = layout.expect_local_word(0, "test");
        let last = layout.expect_local_word(2, "test");

        assert_eq!(layout.sp_relative_bytes(first), 128);
        assert_eq!(layout.sp_relative_bytes(last), 64);
    }

    #[test]
    fn dynamic_frame_layout_rejects_out_of_range_local_words() {
        let layout = DynamicFrameLayout::new(2).expect("layout");

        assert_eq!(layout.local_word(2), None);
        assert_eq!(layout.expect_local_word(1, "test").as_u32(), 1);
    }
}
