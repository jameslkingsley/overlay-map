//! This module provides an `OverlayMap` structure that allows for a two-layered map, where
//! the foreground layer is mutable and the background layer is immutable.

use std::{
    collections::{HashMap, hash_map::RandomState},
    hash::{BuildHasher, Hash},
    mem::MaybeUninit,
};

#[repr(u8)]
#[derive(Debug)]
pub enum Layer {
    Foreground,
    Background,
    Both,
}

#[repr(C)]
#[derive(Debug)]
pub struct Entry<T> {
    layer: Layer,
    foreground: MaybeUninit<T>,
    background: MaybeUninit<T>,
}

impl<T> Entry<T> {
    unsafe fn new_foreground(val: T) -> Self {
        Self {
            layer: Layer::Foreground,
            foreground: MaybeUninit::new(val),
            background: MaybeUninit::uninit(),
        }
    }

    unsafe fn insert_foreground(&mut self, val: T) {
        match self.layer {
            Layer::Background => {
                self.foreground = MaybeUninit::new(val);
                self.layer = Layer::Both;
            }
            Layer::Foreground => unsafe {
                self.foreground.assume_init_drop();
                self.foreground = MaybeUninit::new(val);
            },
            Layer::Both => unsafe {
                self.foreground.assume_init_drop();
                self.foreground = MaybeUninit::new(val);
            },
        }
    }

    unsafe fn insert_background(&mut self, val: T) {
        match self.layer {
            Layer::Foreground => {
                self.background = MaybeUninit::new(val);
                self.layer = Layer::Both;
            }
            Layer::Background => unsafe {
                self.background.assume_init_drop();
                self.background = MaybeUninit::new(val);
            },
            Layer::Both => unsafe {
                self.background.assume_init_drop();
                self.background = MaybeUninit::new(val);
            },
        }
    }

    unsafe fn get_foreground(&self) -> Option<&T> {
        match self.layer {
            Layer::Foreground | Layer::Both => Some(unsafe { self.foreground.assume_init_ref() }),
            _ => None,
        }
    }

    unsafe fn get_background(&self) -> Option<&T> {
        match self.layer {
            Layer::Background | Layer::Both => Some(unsafe { self.background.assume_init_ref() }),
            _ => None,
        }
    }

    unsafe fn get_foreground_mut(&mut self) -> Option<&mut T> {
        match self.layer {
            Layer::Foreground | Layer::Both => Some(unsafe { &mut *self.foreground.as_mut_ptr() }),
            _ => None,
        }
    }
}

impl<V> Drop for Entry<V> {
    fn drop(&mut self) {
        unsafe {
            match self.layer {
                Layer::Foreground => {
                    self.foreground.assume_init_drop();
                }
                Layer::Background => {
                    self.background.assume_init_drop();
                }
                Layer::Both => {
                    self.foreground.assume_init_drop();
                    self.background.assume_init_drop();
                }
            }
        }
    }
}

/// A map with two layers: foreground for recent changes, background for original values.
///
/// **Note:** This map is not thread-safe for mutation, but can be safely shared across threads
/// if only read from.
#[derive(Debug)]
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

    /// Create a new `OverlayMap` with a custom hasher.
    pub fn with_hasher(hasher: S) -> Self {
        Self {
            map: HashMap::with_hasher(hasher.clone()),
        }
    }

    /// Number of unique keys in foreground or background.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.map
            .get(key)
            .map(|entry| unsafe { entry.get_foreground().or_else(|| entry.get_background()) })
            .flatten()
    }

    pub fn get_foreground(&self, key: &K) -> Option<&V> {
        self.map
            .get(key)
            .and_then(|entry| unsafe { entry.get_foreground() })
    }

    pub fn get_background(&self, key: &K) -> Option<&V> {
        self.map
            .get(key)
            .and_then(|entry| unsafe { entry.get_background() })
    }

    pub fn insert(&mut self, key: K, value: V) {
        if let Some(entry) = self.map.get_mut(&key) {
            match entry.layer {
                Layer::Foreground => unsafe {
                    let fg_ptr = entry.get_foreground_mut().unwrap() as *mut V;
                    let old_val = std::ptr::read(fg_ptr);
                    entry.insert_background(old_val);
                    entry.insert_foreground(value);
                },
                Layer::Background => unsafe {
                    entry.insert_foreground(value);
                },
                Layer::Both => unsafe {
                    let fg_ptr = entry.get_foreground_mut().unwrap() as *mut V;
                    let old_val = std::ptr::read(fg_ptr);
                    entry.insert_background(old_val);
                    entry.insert_foreground(value);
                },
            }
        } else {
            self.map
                .insert(key, unsafe { Entry::new_foreground(value) });
        }
    }

    pub fn try_swap<F>(&mut self, key: &K, f: F) -> usize
    where
        F: FnOnce(&V) -> Option<V>,
    {
        if let Some(entry) = self.map.get_mut(&key) {
            match entry.layer {
                Layer::Foreground => unsafe {
                    let fg_ptr = entry.get_foreground().unwrap() as *const V;
                    let old_val = std::ptr::read(fg_ptr);
                    if let Some(new_val) = f(&old_val) {
                        entry.insert_background(old_val);
                        entry.insert_foreground(new_val);
                        1
                    } else {
                        0
                    }
                },
                Layer::Background => unsafe {
                    let bg_ptr = entry.get_background().unwrap() as *const V;
                    let bg_val = std::ptr::read(bg_ptr);
                    if let Some(new_val) = f(&bg_val) {
                        entry.insert_foreground(new_val);
                        1
                    } else {
                        0
                    }
                },
                Layer::Both => unsafe {
                    let fg_ptr = entry.get_foreground_mut().unwrap() as *mut V;
                    let old_val = std::ptr::read(fg_ptr);
                    if let Some(new_val) = f(&old_val) {
                        entry.insert_background(old_val);
                        entry.insert_foreground(new_val);
                        1
                    } else {
                        0
                    }
                },
            }
        } else {
            0
        }
    }

    pub fn extend_swap(&mut self, other: HashMap<K, V, S>) -> usize {
        let mut swaps = 0;

        for (key, new_val) in other {
            if let Some(entry) = self.map.get_mut(&key) {
                match entry.layer {
                    Layer::Foreground => unsafe {
                        let fg_ptr = entry.get_foreground_mut().unwrap() as *mut V;
                        let old_val = std::ptr::read(fg_ptr);
                        entry.insert_background(old_val);
                        entry.insert_foreground(new_val);
                        swaps += 1;
                    },
                    Layer::Background => unsafe {
                        entry.insert_foreground(new_val);
                    },
                    Layer::Both => unsafe {
                        let fg_ptr = entry.get_foreground_mut().unwrap() as *mut V;
                        let old_val = std::ptr::read(fg_ptr);
                        entry.insert_background(old_val);
                        entry.insert_foreground(new_val);
                        swaps += 1;
                    },
                }
            } else {
                self.map
                    .insert(key.clone(), unsafe { Entry::new_foreground(new_val) });
            }
        }

        swaps
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
        map.extend_swap(updates);

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
