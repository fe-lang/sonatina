//! Loops over a module's functions that use rayon's thread pool only when the
//! module has enough instructions to repay it.

use rayon::prelude::*;

use crate::module::FuncStore;

/// The fewest instructions a module needs before loops over its functions run
/// on rayon's thread pool. Entering the pool wakes its workers, which spin
/// before they sleep again; for a smaller module that costs more CPU than the
/// loop saves in wall time.
pub const MIN_PARALLEL_INSTS: usize = 8192;

/// Whether a loop over `items` of the module whose functions `funcs` holds
/// runs on the pool.
pub fn is_parallel(funcs: &FuncStore, items: usize) -> bool {
    items > 1 && funcs.inst_count() >= MIN_PARALLEL_INSTS
}

/// `items.iter().map(f).collect()`, on the pool for a large module. The
/// results keep the items' order.
pub fn map<T, R, F>(funcs: &FuncStore, items: &[T], f: F) -> Vec<R>
where
    T: Sync,
    R: Send,
    F: Fn(&T) -> R + Sync + Send,
{
    if is_parallel(funcs, items.len()) {
        items.par_iter().map(f).collect()
    } else {
        items.iter().map(f).collect()
    }
}

/// `items.into_iter().map(f).collect()`, on the pool for a large module. The
/// results keep the items' order.
pub fn map_owned<T, R, F>(funcs: &FuncStore, items: Vec<T>, f: F) -> Vec<R>
where
    T: Send,
    R: Send,
    F: Fn(T) -> R + Sync + Send,
{
    if is_parallel(funcs, items.len()) {
        items.into_par_iter().map(f).collect()
    } else {
        items.into_iter().map(f).collect()
    }
}

/// The items `keep` accepts, in order, on the pool for a large module.
pub fn filter<T, F>(funcs: &FuncStore, items: &[T], keep: F) -> Vec<T>
where
    T: Copy + Send + Sync,
    F: Fn(&T) -> bool + Sync + Send,
{
    if is_parallel(funcs, items.len()) {
        items.par_iter().copied().filter(keep).collect()
    } else {
        items.iter().copied().filter(keep).collect()
    }
}

/// Runs `f` on every item, on the pool for a large module.
pub fn for_each<T, F>(funcs: &FuncStore, items: &[T], f: F)
where
    T: Sync,
    F: Fn(&T) + Sync + Send,
{
    if is_parallel(funcs, items.len()) {
        items.par_iter().for_each(f);
    } else {
        items.iter().for_each(f);
    }
}
