use std::{collections::BTreeMap, ops::Range};

use crate::InstId;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DebugTag {
    SourceLoc(u32),
    InlineCallsite(u32),
    SemanticScope(u32),
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct DebugTags {
    tags: Vec<DebugTag>,
    insts: BTreeMap<InstId, Range<u32>>,
}

impl DebugTags {
    pub fn set(&mut self, inst: InstId, new_tags: impl IntoIterator<Item = DebugTag>) {
        let start = self.tags.len() as u32;
        self.tags.extend(new_tags);
        let end = self.tags.len() as u32;
        if end > start {
            self.insts.insert(inst, start..end);
        } else {
            self.insts.remove(&inst);
        }
    }

    pub fn get(&self, inst: InstId) -> &[DebugTag] {
        if let Some(range) = self.insts.get(&inst) {
            &self.tags[range.start as usize..range.end as usize]
        } else {
            &[]
        }
    }

    pub fn has(&self, inst: InstId) -> bool {
        self.insts.contains_key(&inst)
    }

    pub fn clone_tags(&mut self, from: InstId, to: InstId) {
        if let Some(range) = self.insts.get(&from).cloned() {
            self.insts.insert(to, range);
        } else {
            self.insts.remove(&to);
        }
    }

    /// Prepend tags from `prefix_inst` onto `target_inst`'s existing tags.
    /// Used during inlining: the callsite's tags are prepended to all inlined
    /// instructions, preserving the virtual call stack.
    pub fn prepend_tags(&mut self, prefix_inst: InstId, target_inst: InstId) {
        let prefix_tags: Vec<_> = self.get(prefix_inst).to_vec();
        if prefix_tags.is_empty() {
            return;
        }
        let existing_tags: Vec<_> = self.get(target_inst).to_vec();
        let start = self.tags.len() as u32;
        self.tags.extend(prefix_tags);
        self.tags.extend(existing_tags);
        let end = self.tags.len() as u32;
        self.insts.insert(target_inst, start..end);
    }

    pub fn is_empty(&self) -> bool {
        self.insts.is_empty()
    }

    pub fn clear(&mut self) {
        self.tags.clear();
        self.insts.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_and_get_tags() {
        let mut tags = DebugTags::default();
        let inst = InstId(0);
        tags.set(inst, [DebugTag::SourceLoc(42)]);
        assert_eq!(tags.get(inst), &[DebugTag::SourceLoc(42)]);
        assert!(tags.has(inst));
    }

    #[test]
    fn clone_tags_shares_range() {
        let mut tags = DebugTags::default();
        let from = InstId(0);
        let to = InstId(1);
        tags.set(
            from,
            [DebugTag::SourceLoc(10), DebugTag::InlineCallsite(20)],
        );
        tags.clone_tags(from, to);
        assert_eq!(tags.get(from), tags.get(to));
    }

    #[test]
    fn prepend_tags_preserves_order() {
        let mut tags = DebugTags::default();
        let callsite = InstId(0);
        let inlined = InstId(1);

        tags.set(callsite, [DebugTag::SourceLoc(100)]);
        tags.set(inlined, [DebugTag::SourceLoc(200)]);

        tags.prepend_tags(callsite, inlined);

        assert_eq!(
            tags.get(inlined),
            &[DebugTag::SourceLoc(100), DebugTag::SourceLoc(200)]
        );
    }

    #[test]
    fn empty_inst_returns_empty_slice() {
        let tags = DebugTags::default();
        assert!(tags.get(InstId(99)).is_empty());
        assert!(!tags.has(InstId(99)));
    }
}
