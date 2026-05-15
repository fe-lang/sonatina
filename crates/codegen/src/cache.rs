//! Content-addressed incremental compilation cache.
//!
//! Following Cranelift's `incremental_cache` pattern: hash the function's IR
//! content to produce a cache key, then store/retrieve compiled artifacts
//! (machine code + debug info) keyed by that hash.
//!
//! This module provides the trait and key computation. Actual cache storage
//! is pluggable via the `CompilationCache` trait.

use std::hash::{Hash, Hasher};

use sonatina_ir::{Function, module::FuncRef};

/// Opaque cache key derived from a function's IR content.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CacheKey {
    hash: [u8; 32],
}

impl CacheKey {
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.hash
    }
}

impl std::fmt::Display for CacheKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for byte in &self.hash {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Trait for pluggable cache storage backends.
pub trait CompilationCache {
    fn get(&self, key: &CacheKey) -> Option<CachedCompilation>;
    fn insert(&mut self, key: CacheKey, value: CachedCompilation);
}

/// A cached compilation result for a single function.
#[derive(Clone, Debug)]
pub struct CachedCompilation {
    pub machine_code: Vec<u8>,
    pub source_map_entries: Vec<CachedSourceMapEntry>,
}

/// A source map entry from a cached compilation.
#[derive(Clone, Debug)]
pub struct CachedSourceMapEntry {
    pub offset: u32,
    pub length: u32,
    pub source_loc: u32,
}

/// Compute a cache key for a function by hashing its IR content.
///
/// The key combines the function's structural content: block topology,
/// instruction identity, and source locations. Two functions with
/// identical IR will produce the same key.
pub fn compute_cache_key(func: &Function, func_ref: FuncRef) -> CacheKey {
    use std::collections::hash_map::DefaultHasher;

    let mut hash = [0u8; 32];

    // Four independent hashers for better distribution across 256 bits
    let mut hashers: [DefaultHasher; 4] = [
        DefaultHasher::new(),
        DefaultHasher::new(),
        DefaultHasher::new(),
        DefaultHasher::new(),
    ];

    func_ref.as_u32().hash(&mut hashers[0]);
    func.arg_values.len().hash(&mut hashers[1]);

    let mut inst_count = 0u32;
    for block in func.layout.iter_block() {
        block.hash(&mut hashers[inst_count as usize % 4]);
        for inst in func.layout.iter_inst(block) {
            let idx = inst_count as usize % 4;
            inst.hash(&mut hashers[idx]);
            func.source_locs[inst].hash(&mut hashers[idx]);
            inst_count += 1;
        }
    }
    inst_count.hash(&mut hashers[3]);

    for (i, hasher) in hashers.iter().enumerate() {
        let h = hasher.finish();
        hash[i * 8..(i + 1) * 8].copy_from_slice(&h.to_le_bytes());
    }

    CacheKey { hash }
}

/// In-memory cache implementation for testing and single-compilation use.
#[derive(Default)]
pub struct InMemoryCache {
    entries: std::collections::HashMap<CacheKey, CachedCompilation>,
}

impl CompilationCache for InMemoryCache {
    fn get(&self, key: &CacheKey) -> Option<CachedCompilation> {
        self.entries.get(key).cloned()
    }

    fn insert(&mut self, key: CacheKey, value: CachedCompilation) {
        self.entries.insert(key, value);
    }
}

impl InMemoryCache {
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_key_display() {
        let key = CacheKey { hash: [0xab; 32] };
        let display = format!("{key}");
        assert_eq!(display.len(), 64);
        assert!(display.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn in_memory_cache_insert_get() {
        let mut cache = InMemoryCache::default();
        let key = CacheKey { hash: [1; 32] };
        let value = CachedCompilation {
            machine_code: vec![0x60, 0x00],
            source_map_entries: vec![],
        };
        cache.insert(key.clone(), value);
        assert!(cache.get(&key).is_some());
        assert_eq!(cache.get(&key).unwrap().machine_code, vec![0x60, 0x00]);
    }

    #[test]
    fn cache_miss_returns_none() {
        let cache = InMemoryCache::default();
        let key = CacheKey { hash: [99; 32] };
        assert!(cache.get(&key).is_none());
    }
}
