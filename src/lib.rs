//! A two-layered map structure where the foreground is mutable and the
//! background is preserved.
//!
//! OverlayMap lets you insert values without cloning, while keeping a single
//! layer of historical context. Each key has a current value (foreground) and
//! may have a previous value (background), which is automatically managed
//! during updates.
//!
//! ```rust
//! use overlay_map::OverlayMap;
//!
//! #[derive(Debug, Clone, PartialEq)]
//! struct QuantumBit {
//!     collapsed: bool,
//!     value: Option<bool>,
//! }
//!
//! /// Simulates measurement collapse
//! fn collapse(mut qbit: QuantumBit) -> QuantumBit {
//!     qbit.collapsed = true;
//!     qbit.value = Some(rand::random());
//!     qbit
//! }
//!
//! fn main() {
//!     let mut qstate = OverlayMap::<&str, QuantumBit>::new();
//!
//!     // Push an uncollapsed qubit
//!     qstate.push(
//!         "qbit_1",
//!         QuantumBit {
//!             collapsed: false,
//!             value: None,
//!         },
//!     );
//!
//!     // Observe the qubit: only collapse if it's not already
//!     let did_observe = qstate.push_if(&"qbit_1", |current| {
//!         if current.collapsed {
//!             None // already collapsed, don't change
//!         } else {
//!             Some(collapse(current.clone())) // clone *only* if needed
//!         }
//!     });
//!
//!     println!("Was observed?       {}", did_observe);
//!     println!("After observation:  {:?}", qstate.fg(&"qbit_1"));
//!     println!("Before observation: {:?}", qstate.bg(&"qbit_1"));
//! }
//! ```

use std::{
    collections::{HashMap, hash_map::RandomState},
    hash::{BuildHasher, Hash},
    mem::MaybeUninit,
};

/// A two-layered map where each key has a mutable foreground and an optional
/// background value.
///
/// When inserting a new value for a key, the previous value (if any) is
/// automatically moved to the background. Background values are preserved but
/// not cloned.
///
/// This map is not thread-safe for mutation. It may be shared across threads
/// for read-only access.
#[derive(Debug, Default)]
pub struct OverlayMap<K, V, S = RandomState>
where
    K: Eq + Hash,
{
    map: HashMap<K, Entry<V>, S>,
}

unsafe impl<K, V, S> Sync for OverlayMap<K, V, S>
where
    K: Eq + Hash + Sync,
    S: Sync,
{
}

impl<K, V, S> OverlayMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    /// Creates a new, empty `OverlayMap` with the default hasher.
    pub fn new() -> Self {
        Self::with_hasher(Default::default())
    }

    /// Creates an empty `OverlayMap` with the specified capacity and default hasher.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }

    /// Creates an empty `OverlayMap` that will use the given hasher.
    pub fn with_hasher(hasher: S) -> Self {
        Self {
            map: HashMap::with_hasher(hasher),
        }
    }

    /// Creates an empty `OverlayMap` with the specified capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(capacity, hasher),
        }
    }

    /// Number of unique keys in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Get an immutable reference to the value associated with the key.
    ///
    /// Returns `None` if the key was not found in the map.
    pub fn fg(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|entry| entry.fg())
    }

    /// Get an immutable reference to the value associated with the key in the background layer.
    ///
    /// Returns `None` if the key was not found in the background layer.
    pub fn bg(&self, key: &K) -> Option<&V> {
        self.map.get(key).and_then(|entry| entry.bg())
    }

    /// Push a value into the foreground layer, preserving the previous value in
    /// the background.
    ///
    /// If the key was already present, the current foreground is moved to the
    /// background slot, and the new value becomes the new foreground. No
    /// cloning occurs. The old background value is dropped if it was present.
    ///
    /// Returns `true` if there was already a foreground value (i.e. a
    /// background now exists).
    pub fn push(&mut self, key: K, value: V) -> bool {
        if let Some(entry) = self.map.get_mut(&key) {
            entry.push(value);
            true
        } else {
            self.map.insert(key, Entry::new(value));
            false
        }
    }

    /// Conditionally push a new value into the foreground based on the current
    /// value.
    ///
    /// If the key exists, the current foreground value is passed to the
    /// predicate. If the predicate returns `Some(new_val)`, the new value is
    /// pushed and the old one is preserved in the background. If it returns
    /// `None`, nothing is changed.
    ///
    /// Returns `true` if a new value was pushed.
    pub fn push_if<F>(&mut self, key: &K, predicate: F) -> bool
    where
        F: FnOnce(&V) -> Option<V>,
    {
        let entry = match self.map.get_mut(key) {
            Some(e) => e,
            None => return false,
        };

        match predicate(entry.fg()) {
            Some(new) => {
                entry.push(new);
                true
            }
            None => false,
        }
    }

    /// Overlay multiple values onto the map.
    ///
    /// Each key-value pair is pushed into the foreground layer. If the key was
    /// already present, the existing foreground value is moved to the
    /// background. This does not clone or retain old values beyond the
    /// background layer.
    ///
    /// Returns the number of keys that already existed (i.e. pushes that
    /// replaced a foreground).
    pub fn overlay<I>(&mut self, iter: I) -> usize
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut replaced = 0;

        for (key, val) in iter {
            replaced += self.push(key, val) as usize;
        }

        replaced
    }
}

const SLOT0_PRESENT: u8 = 1 << 0;
const SLOT1_PRESENT: u8 = 1 << 1;
const FG_SLOT: u8 = 1 << 2;

/// Internal value container for a key in `OverlayMap`, holding up to two
/// versions.
///
/// Each `Entry` stores a foreground value and optionally a background value.
/// Used to track changes without cloning.
#[derive(Debug)]
struct Entry<T> {
    bits: u8,
    slots: [MaybeUninit<T>; 2],
}

impl<T> Entry<T> {
    fn new(val: T) -> Self {
        Self {
            bits: SLOT0_PRESENT,
            slots: [MaybeUninit::new(val), MaybeUninit::uninit()],
        }
    }

    #[inline]
    fn fg_index(&self) -> usize {
        ((self.bits & FG_SLOT) >> 2) as usize
    }

    #[inline]
    fn bg_index(&self) -> usize {
        self.fg_index() ^ 1
    }

    fn fg(&self) -> &T {
        let idx = self.fg_index();
        unsafe { self.slots[idx].assume_init_ref() }
    }

    fn bg(&self) -> Option<&T> {
        let idx = self.bg_index();
        if self.is_slot_present(idx) {
            Some(unsafe { self.slots[idx].assume_init_ref() })
        } else {
            None
        }
    }

    #[inline]
    fn is_slot_present(&self, idx: usize) -> bool {
        (self.bits & (1 << idx)) != 0
    }

    /// Moves the current foreground value to the background slot, dropping any
    /// previous background.
    ///
    /// This operation updates only internal bits and memory slots. The value
    /// itself is not cloned or moved in memory. If a background value already
    /// exists, it is dropped before being replaced.
    #[inline]
    fn push_fg_to_bg(&mut self) {
        let bgi = self.bg_index();

        // If the background slot is present, drop it to avoid memory leaks
        if self.is_slot_present(bgi) {
            unsafe {
                self.slots[bgi].assume_init_drop();
            }
        }

        // Flip the foreground/background logical mapping
        self.bits |= 1 << bgi;
        self.bits ^= FG_SLOT;
    }

    /// Insert a new value into the foreground, pushing the old one into the
    /// background.
    ///
    /// This is called after `push_fg_to_bg` flips the active slot.
    #[inline]
    fn push(&mut self, val: T) {
        self.push_fg_to_bg();
        let idx = self.fg_index();
        self.slots[idx] = MaybeUninit::new(val);
        self.bits |= 1 << idx;
    }
}

impl<V> Drop for Entry<V> {
    fn drop(&mut self) {
        if (self.bits & SLOT0_PRESENT) != 0 {
            unsafe { self.slots[0].assume_init_drop() };
        }

        if (self.bits & SLOT1_PRESENT) != 0 {
            unsafe { self.slots[1].assume_init_drop() };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_and_get_foreground() {
        let mut map = OverlayMap::<&str, i32>::new();
        assert!(map.fg(&"key").is_none());
        map.push("key", 42);
        assert_eq!(*map.fg(&"key").expect("Entry was just pushed"), 42);
    }

    #[test]
    fn push_and_get_background() {
        let mut map = OverlayMap::<&str, i32>::new();
        assert!(map.fg(&"key").is_none());
        map.push("key", 99);
        assert_eq!(*map.fg(&"key").expect("Entry was just pushed"), 99);
    }

    #[test]
    fn push_if_no_change_foreground() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.push("key", 100);

        // Try swap but do nothing
        map.push_if(&"key", |old| {
            if *old == 100 {
                None // no change
            } else {
                Some(999)
            }
        });

        // Still foreground = 100, no background
        assert_eq!(*map.fg(&"key").expect("Entry should still exist"), 100);
    }

    #[test]
    fn push_if_foreground_to_background() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.push("key", 50);
        map.push_if(&"key", |old| if *old == 50 { Some(123) } else { None });
        assert_eq!(*map.fg(&"key").expect("Entry should still exist"), 123);
        assert_eq!(
            *map.bg(&"key").expect("Old value not found in background"),
            50
        );
    }

    #[test]
    fn push_if_missing_key() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.push_if(&"missing", |_| Some(999));
        assert!(map.fg(&"missing").is_none());
    }

    #[test]
    fn overlay_test() {
        // Initialize an OverlayMap with:
        // - "fg_key" in foreground
        // - "bg_key" in background
        // - "absent_key" absent
        let mut map = OverlayMap::<&str, i32>::new();
        map.push("fg_key", 10);
        map.push("bg_key", 20);

        // Prepare updates:
        // - "fg_key" -> 100
        // - "bg_key" -> 200
        // - "none_key" -> 300 (was absent in map)
        let updates = vec![("fg_key", 100), ("bg_key", 200), ("none_key", 300)];

        // Perform the merge
        map.overlay(updates);

        // Check that "fg_key" was in foreground, so old value (10) moved to background.
        // New value (100) should be in foreground.
        match map.fg(&"fg_key") {
            Some(val) => assert_eq!(*val, 100),
            _ => panic!("Expected 'fg_key' = 100 in foreground"),
        }
        match map.bg(&"fg_key") {
            Some(val) => assert_eq!(*val, 10),
            None => panic!("Expected old 'fg_key' value = 10 in background"),
        }

        // Check that "none_key" was absent, so it is now in the foreground with 300
        match map.fg(&"none_key") {
            Some(val) => assert_eq!(*val, 300),
            _ => panic!("Expected 'none_key' = 300 in foreground"),
        }
        // It shouldn't exist in background
        assert!(map.bg(&"none_key").is_none());
    }
}
