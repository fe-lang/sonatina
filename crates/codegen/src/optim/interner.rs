use std::hash::Hash;

use cranelift_entity::{EntityRef, PrimaryMap};
use fxhash::FxHashMap;

#[derive(Debug)]
pub(super) struct Interner<K, V>
where
    K: EntityRef,
{
    map: FxHashMap<V, K>,
    store: PrimaryMap<K, V>,
}

impl<K, V> Interner<K, V>
where
    K: EntityRef,
    V: Eq + Hash + Clone,
{
    pub(super) fn intern(&mut self, value: V) -> K {
        if let Some(&key) = self.map.get(&value) {
            key
        } else {
            let key = self.store.push(value.clone());
            self.map.insert(value, key);
            key
        }
    }

    pub(super) fn get(&self, key: K) -> &V {
        &self.store[key]
    }

    pub(super) fn clear(&mut self) {
        self.map.clear();
        self.store.clear();
    }
}

impl<K, V> Default for Interner<K, V>
where
    K: EntityRef,
{
    fn default() -> Self {
        Self {
            map: FxHashMap::default(),
            store: PrimaryMap::default(),
        }
    }
}
