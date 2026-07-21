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

impl CachedCompilation {
    /// Serialize to a binary blob for persistent storage.
    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        let code_len = self.machine_code.len() as u32;
        buf.extend_from_slice(&code_len.to_le_bytes());
        buf.extend_from_slice(&self.machine_code);
        let entries_len = self.source_map_entries.len() as u32;
        buf.extend_from_slice(&entries_len.to_le_bytes());
        for entry in &self.source_map_entries {
            buf.extend_from_slice(&entry.offset.to_le_bytes());
            buf.extend_from_slice(&entry.length.to_le_bytes());
            buf.extend_from_slice(&entry.source_loc.to_le_bytes());
        }
        buf
    }

    /// Deserialize from a binary blob.
    pub fn deserialize(data: &[u8]) -> Option<Self> {
        let mut pos = 0;
        if data.len() < 4 {
            return None;
        }
        let code_len = u32::from_le_bytes(data[pos..pos + 4].try_into().ok()?) as usize;
        pos += 4;
        if data.len() < pos + code_len {
            return None;
        }
        let machine_code = data[pos..pos + code_len].to_vec();
        pos += code_len;
        if data.len() < pos + 4 {
            return None;
        }
        let entries_len = u32::from_le_bytes(data[pos..pos + 4].try_into().ok()?) as usize;
        pos += 4;
        let mut source_map_entries = Vec::with_capacity(entries_len);
        for _ in 0..entries_len {
            if data.len() < pos + 12 {
                return None;
            }
            let offset = u32::from_le_bytes(data[pos..pos + 4].try_into().ok()?);
            let length = u32::from_le_bytes(data[pos + 4..pos + 8].try_into().ok()?);
            let source_loc = u32::from_le_bytes(data[pos + 8..pos + 12].try_into().ok()?);
            source_map_entries.push(CachedSourceMapEntry {
                offset,
                length,
                source_loc,
            });
            pos += 12;
        }
        Some(CachedCompilation {
            machine_code,
            source_map_entries,
        })
    }
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
    fn cached_compilation_serialization_round_trip() {
        let original = CachedCompilation {
            machine_code: vec![0x60, 0x00, 0x60, 0x01, 0x01],
            source_map_entries: vec![
                CachedSourceMapEntry {
                    offset: 0,
                    length: 2,
                    source_loc: 42,
                },
                CachedSourceMapEntry {
                    offset: 2,
                    length: 3,
                    source_loc: 100,
                },
            ],
        };
        let serialized = original.serialize();
        let deserialized = CachedCompilation::deserialize(&serialized).unwrap();
        assert_eq!(deserialized.machine_code, original.machine_code);
        assert_eq!(deserialized.source_map_entries.len(), 2);
        assert_eq!(deserialized.source_map_entries[0].source_loc, 42);
        assert_eq!(deserialized.source_map_entries[1].offset, 2);
    }

    #[test]
    fn cache_miss_returns_none() {
        let cache = InMemoryCache::default();
        let key = CacheKey { hash: [99; 32] };
        assert!(cache.get(&key).is_none());
    }
}
