#[derive(Clone, Default)]
pub(crate) struct FuncDynSpPlan {
    pub(crate) entry_init: Option<DynSpInitKind>,
    pub(crate) entry_live_frame: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DynSpInitKind {
    Always,
    Checked,
}
