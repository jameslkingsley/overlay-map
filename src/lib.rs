//! This module provides an `OverlayMap` structure that allows for a two-layered map, where
//! the foreground layer is mutable and the background layer is immutable.

use std::{
    collections::{HashMap, hash_map::RandomState},
    hash::{BuildHasher, Hash},
    mem::MaybeUninit,
};

// TODO Zero-cost rollback/commits

/// A map with two layers: foreground for recent changes, background for original values.
///
/// **Note:** This map is not thread-safe for mutation, but can be safely shared across threads
/// if only read from.
#[derive(Debug, Default)]
pub struct OverlayMap<K, V, S = RandomState>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    map: HashMap<K, Entry<V>, S>,
}

unsafe impl<K, V, S> Sync for OverlayMap<K, V, S>
where
    K: Eq + Hash + Clone + Sync,
    V: Clone + Default,
    S: BuildHasher + Clone + Sync,
{
}

impl<K, V, S> OverlayMap<K, V, S>
where
    K: Eq + Hash + Clone,
    V: Clone + Default,
    S: BuildHasher + Clone,
{
    /// Create a new `OverlayMap` with a default hasher.
    pub fn new() -> Self
    where
        S: Default,
    {
        Self {
            map: HashMap::with_hasher(S::default()),
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
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|entry| entry.get_foreground())
    }

    /// Get an immutable reference to the value associated with the key in the foreground layer.
    ///
    /// Returns `None` if the key was not found in the map.
    pub fn get_foreground(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|entry| entry.get_foreground())
    }

    /// Get an immutable reference to the value associated with the key in the background layer.
    ///
    /// Returns `None` if the key was not found in the background layer.
    pub fn get_background(&self, key: &K) -> Option<&V> {
        self.map.get(key).and_then(|entry| entry.get_background())
    }

    /// Insert a value into the map.
    ///
    /// Insertion is zero-copy, meaning the value is moved into the map and any
    /// existing value is moved into the background layer without cloning.
    ///
    /// The insertion order is as follows:
    ///
    /// - If the key is not present, the value is inserted into the foreground
    /// - If the key is present in the foreground, the existing value is moved
    ///   to the background and the new value is inserted into the foreground
    /// - If the key is present in the background, the new value is inserted into the foreground
    pub fn insert(&mut self, key: K, value: V) -> usize {
        if let Some(entry) = self.map.get_mut(&key) {
            entry.insert_foreground(value);
            1
        } else {
            self.map.insert(key, Entry::new(value));
            0
        }
    }

    /// Extend the map by merging another `HashMap` into it.
    ///
    /// Insertion logic follows the same rules as `insert`.
    pub fn extend(&mut self, other: HashMap<K, V, S>) -> usize {
        let mut swaps = 0;

        for (key, new) in other {
            swaps += self.insert(key, new);
        }

        swaps
    }

    /// Try to swap the value associated with the key using the given predicate.
    pub fn try_swap<F>(&mut self, key: &K, predicate: F) -> usize
    where
        F: FnOnce(&V) -> Option<V>,
    {
        let entry = match self.map.get_mut(key) {
            Some(e) => e,
            None => return 0,
        };

        match predicate(entry.get_foreground()) {
            Some(new) => {
                entry.insert_foreground(new);
                1
            }
            None => 0,
        }
    }
}

const SLOT0_PRESENT: u8 = 1 << 0;
const SLOT1_PRESENT: u8 = 1 << 1;
const FG_SLOT: u8 = 1 << 2;

/// An entry in the `OverlayMap` that can hold a value in either the foreground,
/// background, or both layers.
///
/// Due to the use of unsafe pointers, this struct's alignment must be
/// consistent.
#[repr(C)]
#[derive(Debug)]
pub struct Entry<T> {
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
    fn foreground_index(&self) -> usize {
        ((self.bits & FG_SLOT) >> 2) as usize
    }

    #[inline]
    fn background_index(&self) -> usize {
        self.foreground_index() ^ 1
    }

    fn get_foreground(&self) -> &T {
        let idx = self.foreground_index();
        unsafe { self.slots[idx].assume_init_ref() }
    }

    fn get_background(&self) -> Option<&T> {
        let idx = self.background_index();
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

    /// Push the current foreground into background (if present) by simply toggling bits,
    /// then flips the FG slot bit so new data can go in the “other” slot.
    ///
    /// After this, both slots will be present if FG was present before (so old FG
    /// remains in the old slot, but we label it background now). The actual
    /// memory never moves.
    #[inline]
    pub fn push_fg_to_bg(&mut self) {
        let bgi = self.background_index();

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

    #[inline]
    fn insert_foreground(&mut self, val: T) {
        self.push_fg_to_bg();
        let idx = self.foreground_index();
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
    fn insert_and_get_foreground() {
        let mut map = OverlayMap::<&str, i32>::new();
        assert!(map.get(&"key").is_none());
        map.insert("key", 42);
        assert_eq!(*map.get(&"key").expect("Entry was just inserted"), 42);
    }

    #[test]
    fn insert_and_get_background() {
        let mut map = OverlayMap::<&str, i32>::new();
        assert!(map.get(&"key").is_none());
        map.insert("key", 99);
        assert_eq!(*map.get(&"key").expect("Entry was just inserted"), 99);
    }

    #[test]
    fn try_swap_no_change_foreground() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.insert("key", 100);

        // Try swap but do nothing
        map.try_swap(&"key", |old| {
            if *old == 100 {
                None // no change
            } else {
                Some(999)
            }
        });

        // Still foreground = 100, no background
        assert_eq!(*map.get(&"key").expect("Entry should still exist"), 100);
    }

    #[test]
    fn try_swap_foreground_to_background() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.insert("key", 50);
        map.try_swap(&"key", |old| if *old == 50 { Some(123) } else { None });
        assert_eq!(*map.get(&"key").expect("Entry should still exist"), 123);
        assert_eq!(
            *map.get_background(&"key")
                .expect("Old value not found in background"),
            50
        );
    }

    #[test]
    fn try_swap_missing_key() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.try_swap(&"missing", |_| Some(999));
        assert!(map.get(&"missing").is_none());
    }

    #[test]
    fn extend_swap_test() {
        // Initialize an OverlayMap with:
        // - "fg_key" in foreground
        // - "bg_key" in background
        // - "absent_key" absent
        let mut map = OverlayMap::<&str, i32>::new();
        map.insert("fg_key", 10);
        map.insert("bg_key", 20);

        // Prepare updates:
        // - "fg_key" -> 100
        // - "bg_key" -> 200
        // - "none_key" -> 300 (was absent in map)
        let mut updates = HashMap::default();
        updates.insert("fg_key", 100);
        updates.insert("bg_key", 200);
        updates.insert("none_key", 300);

        // Perform the merge
        map.extend(updates);

        // Check that "fg_key" was in foreground, so old value (10) moved to background.
        // New value (100) should be in foreground.
        match map.get_foreground(&"fg_key") {
            Some(val) => assert_eq!(*val, 100),
            _ => panic!("Expected 'fg_key' = 100 in foreground"),
        }
        match map.get_background(&"fg_key") {
            Some(val) => assert_eq!(*val, 10),
            None => panic!("Expected old 'fg_key' value = 10 in background"),
        }

        // Check that "none_key" was absent, so it is now in the foreground with 300
        match map.get_foreground(&"none_key") {
            Some(val) => assert_eq!(*val, 300),
            _ => panic!("Expected 'none_key' = 300 in foreground"),
        }
        // It shouldn't exist in background
        assert!(map.get_background(&"none_key").is_none());
    }
}
