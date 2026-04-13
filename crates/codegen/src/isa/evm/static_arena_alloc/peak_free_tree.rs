use super::FreeSegment;

/// Augmented start-ordered treap used by the zero-min exact peak scorer.
///
/// `pack_zero_min_offset_peak_ranked` repeatedly frees interior holes and then allocates from the
/// leftmost free segment whose length is at least a requested size. The open tail at the current
/// `max_used` frontier is handled separately because allocating from that detached suffix can grow
/// the peak and must not interfere with interior leftmost-fit decisions.
///
/// This tree stores only interior free segments, keyed by `start`, with a subtree `max_len`
/// summary so the scorer can find the leftmost fitting hole in `O(log n)` without scanning. The
/// structure also preserves the packer's exact invariants: stored segments are disjoint,
/// non-adjacent, and any segment ending at `max_used` lives in `frontier` instead of the tree.
#[derive(Default)]
pub(super) struct PeakFreeTree {
    root: Option<u32>,
    nodes: Vec<PeakFreeNode>,
    frontier: Option<FreeSegment>,
}

#[derive(Clone, Copy, Debug)]
struct PeakFreeNode {
    seg: FreeSegment,
    prio: u64,
    parent: Option<u32>,
    left: Option<u32>,
    right: Option<u32>,
    max_len: u32,
}

impl PeakFreeTree {
    pub(super) fn reset(&mut self, capacity_hint: usize) {
        self.root = None;
        self.nodes.clear();
        self.frontier = None;
        if self.nodes.capacity() < capacity_hint {
            self.nodes.reserve(capacity_hint - self.nodes.capacity());
        }
    }

    pub(super) fn insert(&mut self, start: u32, len: u32, max_used: u32) {
        if len == 0 {
            return;
        }

        let mut segment = FreeSegment { start, len };
        if let Some(frontier) = self.frontier
            && segment.end() == frontier.start
        {
            self.frontier = None;
            segment.len = segment
                .len
                .checked_add(frontier.len)
                .expect("free segment overflow");
        }

        let succ_idx = self.lower_bound(segment.start);
        let pred_idx = succ_idx
            .and_then(|idx| self.predecessor(idx))
            .or_else(|| self.max_node(self.root));

        if let Some(pred_idx) = pred_idx {
            let pred = self.nodes[pred_idx as usize].seg;
            if pred.end() == segment.start {
                self.remove_node(pred_idx);
                segment.start = pred.start;
                segment.len = segment
                    .len
                    .checked_add(pred.len)
                    .expect("free segment overflow");
            }
        }

        if let Some(succ_idx) = succ_idx {
            let succ = self.nodes[succ_idx as usize].seg;
            if segment.end() == succ.start {
                self.remove_node(succ_idx);
                segment.len = segment
                    .len
                    .checked_add(succ.len)
                    .expect("free segment overflow");
            }
        }

        if segment.end() == max_used {
            self.frontier = Some(segment);
            return;
        }

        let node_idx = self.alloc_node(segment);
        self.insert_node(node_idx);
    }

    pub(super) fn take_fit_prefix(&mut self, size_words: u32) -> Option<u32> {
        let mut cursor = self.root;
        while let Some(idx) = cursor {
            let left = self.nodes[idx as usize].left;
            if self.max_len(left) >= size_words {
                cursor = left;
                continue;
            }
            let seg = self.nodes[idx as usize].seg;
            if seg.len >= size_words {
                if seg.len == size_words {
                    self.remove_node(idx);
                } else {
                    debug_assert!(size_words < seg.len);
                    // Prefix allocation leaves the segment end unchanged, so the node stays an
                    // interior hole and still satisfies the start-ordered BST invariant.
                    let new_start = seg
                        .start
                        .checked_add(size_words)
                        .expect("free segment overflow");
                    self.nodes[idx as usize].seg.start = new_start;
                    self.nodes[idx as usize].seg.len = seg
                        .len
                        .checked_sub(size_words)
                        .expect("free segment underflow");
                    self.recompute_upwards(Some(idx));
                }
                return Some(seg.start);
            }
            let right = self.nodes[idx as usize].right;
            if self.max_len(right) >= size_words {
                cursor = right;
                continue;
            }
            return None;
        }
        None
    }

    pub(super) fn take_frontier(&mut self) -> Option<FreeSegment> {
        self.frontier.take()
    }

    pub(super) fn restore_frontier(&mut self, segment: FreeSegment) {
        debug_assert!(self.frontier.is_none());
        self.frontier = Some(segment);
    }

    fn alloc_node(&mut self, seg: FreeSegment) -> u32 {
        let idx = self.nodes.len() as u32;
        self.nodes.push(PeakFreeNode {
            seg,
            prio: priority_for(seg.start),
            parent: None,
            left: None,
            right: None,
            max_len: seg.len,
        });
        idx
    }

    fn max_len(&self, root: Option<u32>) -> u32 {
        root.map_or(0, |idx| self.nodes[idx as usize].max_len)
    }

    fn recompute(&mut self, idx: u32) {
        let node = self.nodes[idx as usize];
        self.nodes[idx as usize].max_len = node
            .seg
            .len
            .max(self.max_len(node.left))
            .max(self.max_len(node.right));
    }

    fn update_parent(&mut self, child: Option<u32>, parent: Option<u32>) {
        if let Some(child) = child {
            self.nodes[child as usize].parent = parent;
        }
    }

    fn set_left(&mut self, parent: u32, child: Option<u32>) {
        self.nodes[parent as usize].left = child;
        self.update_parent(child, Some(parent));
    }

    fn set_right(&mut self, parent: u32, child: Option<u32>) {
        self.nodes[parent as usize].right = child;
        self.update_parent(child, Some(parent));
    }

    fn replace_child(&mut self, parent: Option<u32>, old: u32, new: Option<u32>) {
        if let Some(parent) = parent {
            if self.nodes[parent as usize].left == Some(old) {
                self.set_left(parent, new);
            } else {
                debug_assert_eq!(self.nodes[parent as usize].right, Some(old));
                self.set_right(parent, new);
            }
        } else {
            self.root = new;
            self.update_parent(new, None);
        }
    }

    fn recompute_upwards(&mut self, mut node: Option<u32>) {
        while let Some(idx) = node {
            self.recompute(idx);
            node = self.nodes[idx as usize].parent;
        }
    }

    fn rotate_left(&mut self, idx: u32) {
        let right = self.nodes[idx as usize]
            .right
            .expect("rotate_left requires right child");
        let parent = self.nodes[idx as usize].parent;
        let beta = self.nodes[right as usize].left;
        self.replace_child(parent, idx, Some(right));
        self.set_right(idx, beta);
        self.set_left(right, Some(idx));
        self.recompute(idx);
        self.recompute(right);
    }

    fn rotate_right(&mut self, idx: u32) {
        let left = self.nodes[idx as usize]
            .left
            .expect("rotate_right requires left child");
        let parent = self.nodes[idx as usize].parent;
        let beta = self.nodes[left as usize].right;
        self.replace_child(parent, idx, Some(left));
        self.set_left(idx, beta);
        self.set_right(left, Some(idx));
        self.recompute(idx);
        self.recompute(left);
    }

    fn lower_bound(&self, key: u32) -> Option<u32> {
        let mut cursor = self.root;
        let mut candidate = None;
        while let Some(idx) = cursor {
            let node = self.nodes[idx as usize];
            if node.seg.start < key {
                cursor = node.right;
            } else {
                candidate = Some(idx);
                cursor = node.left;
            }
        }
        candidate
    }

    fn max_node(&self, mut node: Option<u32>) -> Option<u32> {
        while let Some(idx) = node
            && let Some(right) = self.nodes[idx as usize].right
        {
            node = Some(right);
        }
        node
    }

    fn predecessor(&self, idx: u32) -> Option<u32> {
        if self.nodes[idx as usize].left.is_some() {
            return self.max_node(self.nodes[idx as usize].left);
        }
        let mut cursor = idx;
        let mut parent = self.nodes[cursor as usize].parent;
        while let Some(parent_idx) = parent {
            if self.nodes[parent_idx as usize].right == Some(cursor) {
                return Some(parent_idx);
            }
            cursor = parent_idx;
            parent = self.nodes[cursor as usize].parent;
        }
        None
    }

    fn insert_node(&mut self, node_idx: u32) {
        let start = self.nodes[node_idx as usize].seg.start;
        let Some(mut cursor) = self.root else {
            self.root = Some(node_idx);
            return;
        };
        loop {
            if start < self.nodes[cursor as usize].seg.start {
                if let Some(left) = self.nodes[cursor as usize].left {
                    cursor = left;
                } else {
                    self.set_left(cursor, Some(node_idx));
                    break;
                }
            } else if let Some(right) = self.nodes[cursor as usize].right {
                cursor = right;
            } else {
                self.set_right(cursor, Some(node_idx));
                break;
            }
        }

        while let Some(parent) = self.nodes[node_idx as usize].parent {
            if self.nodes[parent as usize].prio <= self.nodes[node_idx as usize].prio {
                break;
            }
            if self.nodes[parent as usize].left == Some(node_idx) {
                self.rotate_right(parent);
            } else {
                self.rotate_left(parent);
            }
        }
        self.recompute_upwards(Some(node_idx));
    }

    fn remove_node(&mut self, idx: u32) {
        while self.nodes[idx as usize].left.is_some() || self.nodes[idx as usize].right.is_some() {
            match (
                self.nodes[idx as usize].left,
                self.nodes[idx as usize].right,
            ) {
                (Some(left), Some(right)) => {
                    if self.nodes[left as usize].prio <= self.nodes[right as usize].prio {
                        self.rotate_right(idx);
                    } else {
                        self.rotate_left(idx);
                    }
                }
                (Some(_), None) => self.rotate_right(idx),
                (None, Some(_)) => self.rotate_left(idx),
                (None, None) => unreachable!(),
            }
        }

        let parent = self.nodes[idx as usize].parent;
        self.replace_child(parent, idx, None);
        self.nodes[idx as usize].parent = None;
        self.recompute_upwards(parent);
    }
}

fn priority_for(start: u32) -> u64 {
    let mut x = u64::from(start).wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}
