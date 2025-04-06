//! A two-layered map structure where the foreground is mutable and the
//! background is preserved.
//!
//! OverlayMap lets you insert values without cloning, while keeping a single
//! layer of historical context. Each key has a current value (foreground) and
//! may have a previous value (background), which is automatically managed
//! during updates.
//!
//! ```rust
//! use overlay_map::Overlay;
//!
//! let mut door = Overlay::new_fg("Alice");
//! println!("Present: {:?}, {:?}", door.fg(), door.bg());
//!
//! for name in ["Bob", "Carol", "Dave", "Eve"] {
//!     if let Some(evicted) = door.swap(name) {
//!         println!("{evicted} left");
//!     }
//!     println!("Present: {:?}, {:?}", door.bg(), door.fg());
//! }
//!
//! while let Some(pulled) = door.pull() {
//!     println!("{pulled} left");
//! }
//!
//! println!("Present: {:?}, {:?}", door.bg(), door.fg());
//! ```

use std::{
    hash::{BuildHasher, Hash},
    mem::MaybeUninit,
};

use hashbrown::{DefaultHashBuilder, HashMap, hash_map::RawEntryMut};

/// A two-layered map where each key holds a current (foreground) and optional historical (background) value.
///
/// `OverlayMap` is a high-performance associative container designed for efficient, non-cloning updates
/// and reversible state transitions. When inserting a new value for an existing key, the current
/// foreground is automatically moved to the background. This allows you to update state while
/// preserving a previous version — useful for rollback, previews, speculative updates, or undo systems.
///
/// All operations are zero-copy and allocation-free beyond what the internal map requires. Background
/// values are stored in-place and never cloned or reallocated.
///
/// Internally, each key maps to an [`Overlay<V>`] that manages the foreground and background slots.
/// The API provides full control over pushing, pulling, and swapping values, with minimal overhead.
///
/// # Features
///
/// - Efficient push/pull/swap operations
/// - No cloning or heap allocation for values
/// - Zero-cost foreground/background transitions
/// - Map keys only retained when a value is present
///
/// # Example
///
/// ```
/// use overlay_map::OverlayMap;
///
/// let mut map = OverlayMap::new();
///
/// // Insert a new value
/// map.push("player", 1);
///
/// // Overwrite it — original goes to background
/// map.push("player", 2);
///
/// assert_eq!(map.fg(&"player"), Some(&2));
/// assert_eq!(map.bg(&"player"), Some(&1));
///
/// // Pull removes the current foreground and promotes background
/// let pulled = map.pull(&"player");
/// assert_eq!(pulled, Some(2));
/// assert_eq!(map.fg(&"player"), Some(&1));
///
/// // Pull again — entry is now removed
/// let pulled = map.pull(&"player");
/// assert_eq!(pulled, Some(1));
/// assert_eq!(map.fg(&"player"), None);
/// ```
#[derive(Debug, Default)]
pub struct OverlayMap<K, V, S = DefaultHashBuilder>
where
    K: Eq + Hash,
{
    map: HashMap<K, Overlay<V>, S>,
}

/// `OverlayMap` is `Sync` because all access to internal state is gated through `&self`
/// for read-only operations, and mutation requires exclusive access via `&mut self`.
///
/// - The underlying `HashMap` is not `Sync` by default, but we do not expose any interior
///   mutability or unsynchronized shared mutation.
/// - All mutation methods (e.g., `push`, `pull`, `swap`) require `&mut self`.
/// - Shared access via `&OverlayMap` only allows read-only operations like `fg`, `bg`, `len`,
///   and `is_empty`, which do not mutate internal state.
/// - `Overlay<T>` is also safe for concurrent read access and does not use interior mutability.
unsafe impl<K, V, S> Sync for OverlayMap<K, V, S>
where
    K: Eq + Hash + Sync,
    S: Sync,
{
}

impl<K, V> OverlayMap<K, V, DefaultHashBuilder>
where
    K: Eq + Hash,
{
    /// Creates a new, empty `OverlayMap` using the default hasher.
    pub fn new() -> Self {
        Self::with_hasher(DefaultHashBuilder::default())
    }
}

impl<K, V, S> OverlayMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
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
    #[inline]
    pub fn fg(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|entry| entry.fg_unchecked())
    }

    /// Get an immutable reference to the value associated with the key in the background layer.
    ///
    /// Returns `None` if the key was not found in the background layer.
    #[inline]
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
    /// background now definitely exists).
    #[inline]
    pub fn push(&mut self, key: K, value: V) -> bool {
        match self.map.raw_entry_mut().from_key(&key) {
            RawEntryMut::Occupied(mut occupied) => {
                occupied.get_mut().push(value);
                true
            }
            RawEntryMut::Vacant(vacant) => {
                vacant.insert(key, Overlay::new_fg(value));
                false
            }
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

        match predicate(entry.fg_unchecked()) {
            Some(new) => {
                entry.push(new);
                true
            }
            None => false,
        }
    }

    /// Pulls the foreground value for a key, promoting the background to foreground if present.
    ///
    /// This removes and returns the current foreground value for the given key. If a background
    /// value exists, it is promoted to foreground. If the key has no background after the pull,
    /// the key is removed from the map entirely.
    ///
    /// # Returns
    ///
    /// - `Some(value)` if the key existed and a foreground value was pulled.
    /// - `None` if the key did not exist.
    ///
    /// # Invariants
    ///
    /// - After this operation, the key is only retained if a background value was available
    ///   to promote.
    /// - Keys in the map always have at least one value (foreground), unless removed by `pull`.
    ///
    /// # Example
    ///
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::<&str, i32>::new();
    /// map.push("key", 1);
    /// map.push("key", 2);
    ///
    /// assert_eq!(map.fg(&"key"), Some(&2));
    /// assert_eq!(map.bg(&"key"), Some(&1));
    ///
    /// let pulled = map.pull(&"key");
    /// assert_eq!(pulled, Some(2));
    /// assert_eq!(map.fg(&"key"), Some(&1)); // background promoted
    ///
    /// let pulled = map.pull(&"key");
    /// assert_eq!(pulled, Some(1));
    /// assert_eq!(map.fg(&"key"), None); // entry removed
    /// ```
    #[inline]
    pub fn pull(&mut self, key: &K) -> Option<V> {
        match self.map.raw_entry_mut().from_key(key) {
            RawEntryMut::Occupied(mut occupied) => {
                let entry = occupied.get_mut();
                let evicted = entry.pull_unchecked();
                if entry.is_empty() {
                    occupied.remove();
                }
                Some(evicted)
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Conditionally pulls the foreground value for a key, promoting the background if present.
    ///
    /// If the key exists and the provided predicate returns `true` for the current foreground,
    /// this removes and returns the foreground value. The background (if any) is promoted to
    /// foreground, and the key is removed from the map if no background remains.
    ///
    /// If the predicate returns `false` or the key does not exist, the map is left unchanged.
    ///
    /// # Returns
    ///
    /// - `Some(value)` if the predicate matched and the foreground was pulled.
    /// - `None` if the key was not found or the predicate returned `false`.
    ///
    /// # Invariants
    ///
    /// - After this operation, the key is only retained if a background value was available
    ///   to promote.
    /// - Keys in the map always have at least one value (foreground), unless removed by `pull_if`.
    ///
    /// # Example
    ///
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::<&str, i32>::new();
    /// map.push("key", 10);
    /// map.push("key", 20);
    ///
    /// // Only pull if the foreground is 20
    /// let pulled = map.pull_if(&"key", |v| *v == 20);
    /// assert_eq!(pulled, Some(20));
    /// assert_eq!(map.fg(&"key"), Some(&10));
    ///
    /// // Predicate does not match: nothing is pulled
    /// let pulled = map.pull_if(&"key", |v| *v == 999);
    /// assert_eq!(pulled, None);
    /// assert_eq!(map.fg(&"key"), Some(&10));
    ///
    /// // Pull remaining value, removing the key
    /// let pulled = map.pull_if(&"key", |_| true);
    /// assert_eq!(pulled, Some(10));
    /// assert_eq!(map.fg(&"key"), None);
    /// ```
    pub fn pull_if<F>(&mut self, key: &K, predicate: F) -> Option<V>
    where
        F: FnOnce(&V) -> bool,
    {
        match self.map.raw_entry_mut().from_key(key) {
            RawEntryMut::Occupied(mut occupied) => {
                let entry = occupied.get_mut();
                if predicate(entry.fg_unchecked()) {
                    let evicted = entry.pull_unchecked();
                    if entry.is_empty() {
                        occupied.remove();
                    }
                    Some(evicted)
                } else {
                    None
                }
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Swap a value into the foreground layer, preserving the previous value in
    /// the background, and returning the evicted background value if present.
    ///
    /// If the key was already present, the current foreground is moved to the
    /// background slot, and the new value becomes the new foreground. No
    /// cloning occurs. The old background value is returned if present.
    #[inline]
    pub fn swap(&mut self, key: K, value: V) -> Option<V> {
        match self.map.raw_entry_mut().from_key(&key) {
            RawEntryMut::Occupied(mut occupied) => occupied.get_mut().swap(value),
            RawEntryMut::Vacant(vacant) => {
                vacant.insert(key, Overlay::new_fg(value));
                None
            }
        }
    }

    /// Conditionally swap a new value into the foreground based on the current
    /// value.
    ///
    /// If the key exists, the current foreground value is passed to the
    /// predicate. If the predicate returns `Some(new_val)`, the new value is
    /// pushed and the old one is preserved in the background. If it returns
    /// `None`, nothing is changed.
    ///
    /// The evicted background value is returned if present.
    pub fn swap_if<F>(&mut self, key: &K, predicate: F) -> Option<V>
    where
        F: FnOnce(&V) -> Option<V>,
    {
        let entry = self.map.get_mut(key)?;
        match predicate(entry.fg_unchecked()) {
            Some(new) => entry.swap(new),
            None => None,
        }
    }

    /// Flips the foreground and background values for the given key, if present.
    ///
    /// This operation swaps the logical roles of the foreground and background values
    /// for the specified key. If the key is present in the map, the values are flipped:
    ///
    /// - The background becomes the new foreground
    /// - The foreground becomes the new background
    ///
    /// This does **not** move, clone, or reallocate any values — it is a zero-cost operation
    /// that simply toggles the internal bit mask controlling foreground/background interpretation.
    ///
    /// If the key is not present in the map, or if it has no background value, the operation
    /// has no effect.
    ///
    /// # Example
    ///
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::new();
    /// map.push("slot", 1);
    /// map.push("slot", 2); // now: fg = 2, bg = 1
    ///
    /// map.flip(&"slot");
    ///
    /// assert_eq!(map.fg(&"slot"), Some(&1));
    /// assert_eq!(map.bg(&"slot"), Some(&2));
    /// ```
    pub fn flip(&mut self, key: &K) {
        if let Some(entry) = self.map.get_mut(key) {
            entry.flip();
        }
    }

    /// Extends the map with a sequence of key-value pairs, counting foreground replacements.
    ///
    /// Each `(K, V)` pair is pushed into the foreground. If a key already exists,
    /// the current foreground is moved to the background, and the new value becomes
    /// the new foreground. If the key is new, it is inserted without affecting any background.
    ///
    /// This method returns the number of keys that were already present — i.e., how many
    /// pushes replaced an existing foreground value.
    ///
    /// No cloning or heap allocation is performed beyond what's necessary for the `HashMap`.
    ///
    /// # Example
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::new();
    /// map.push("a", 1);
    ///
    /// let replaced = map.extend_count([("a", 2), ("b", 3)]);
    /// assert_eq!(replaced, 1); // "a" was already present, "b" was new
    ///
    /// assert_eq!(map.fg(&"a"), Some(&2));
    /// assert_eq!(map.bg(&"a"), Some(&1));
    /// assert_eq!(map.fg(&"b"), Some(&3));
    /// ```
    pub fn extend_count<I>(&mut self, iter: I) -> usize
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

impl<K, V, S> Clone for OverlayMap<K, V, S>
where
    K: Clone + Eq + Hash,
    V: Clone,
    S: Clone + BuildHasher,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<K, V, S> PartialEq for OverlayMap<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<K, V, S> Eq for OverlayMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S> Extend<(K, V)> for OverlayMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    /// Inserts each `(K, V)` pair into the map by pushing the value into the foreground layer.
    ///
    /// This behaves the same as calling push for each element in the iterator. If a key
    /// already exists, the current foreground value is moved to the background, and the
    /// new value becomes the foreground. If the key is new, it is inserted.
    ///
    /// This implementation does **not** return any count of replaced entries — if you need that,
    /// use [`extend_count`](Self::extend_count) instead.
    ///
    /// # Example
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::new();
    /// map.extend([("x", 1), ("y", 2)]);
    ///
    /// assert_eq!(map.fg(&"x"), Some(&1));
    /// assert_eq!(map.fg(&"y"), Some(&2));
    /// ```
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.push(k, v);
        }
    }
}

impl<K, V, S> IntoIterator for OverlayMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    type Item = (K, Overlay<V>);
    type IntoIter = hashbrown::hash_map::IntoIter<K, Overlay<V>>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

const SLOT0_PRESENT: u8 = 1 << 0;
const SLOT1_PRESENT: u8 = 1 << 1;
const SLOT_MASK: u8 = SLOT0_PRESENT | SLOT1_PRESENT;
const FG_SLOT: u8 = 1 << 2;

/// A two-layer value container used by [`OverlayMap`] to manage current and historical values.
///
/// `Overlay<T>` stores up to two values:
///
/// - A **foreground** value representing the current state.
/// - An optional **background** value representing the previous state.
///
/// When used through [`OverlayMap`], each key maps to an `Overlay<T>` to track updates
/// without requiring clones or reallocations. You can also use `Overlay<T>` standalone
/// to manage two-layer state transitions for any value type.
///
/// Values are moved, never cloned. All operations (push, pull, swap) are zero-cost and
/// memory-efficient.
///
/// # Use Cases
///
/// - Managing current and previous state in UI or simulation logic
/// - Efficient delta tracking for configs, game state, etc.
/// - Avoiding `Option<(T, T)>` or custom wrappers with cloning overhead
///
/// # Examples
///
/// ```
/// use overlay_map::Overlay;
///
/// let mut entry = Overlay::new_fg("current");
/// entry.push("next"); // moves "current" into background
///
/// assert_eq!(entry.fg(), Some(&"next"));
/// assert_eq!(entry.bg(), Some(&"current"));
///
/// let pulled = entry.pull();
/// assert_eq!(pulled, Some("next"));
/// assert_eq!(entry.fg(), Some(&"current"));
/// ```
#[derive(Debug)]
pub struct Overlay<T> {
    bits: u8,
    slots: [MaybeUninit<T>; 2],
}

impl<T> Overlay<T> {
    /// Creates a new `Overlay` with no values.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry: Overlay<&str> = Overlay::new_empty();
    /// assert!(entry.is_empty());
    /// assert_eq!(entry.fg(), None);
    /// assert_eq!(entry.bg(), None);
    /// ```
    pub fn new_empty() -> Self {
        Self {
            bits: 0,
            slots: [MaybeUninit::uninit(), MaybeUninit::uninit()],
        }
    }

    /// Creates a new `Overlay` with a foreground value and no background.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry = Overlay::new_fg("fg");
    /// assert_eq!(entry.fg(), Some(&"fg"));
    /// assert_eq!(entry.bg(), None);
    /// ```
    pub fn new_fg(val: T) -> Self {
        Self {
            bits: SLOT0_PRESENT,
            slots: [MaybeUninit::new(val), MaybeUninit::uninit()],
        }
    }

    /// Creates a new `Overlay` with both foreground and background values.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry = Overlay::new_both("fg", "bg");
    /// assert_eq!(entry.fg(), Some(&"fg"));
    /// assert_eq!(entry.bg(), Some(&"bg"));
    /// ```
    pub fn new_both(fg: T, bg: T) -> Self {
        Self {
            bits: SLOT0_PRESENT | SLOT1_PRESENT,
            slots: [MaybeUninit::new(fg), MaybeUninit::new(bg)],
        }
    }

    /// Returns a reference to the current foreground value, if present.
    ///
    /// This returns `Some(&T)` only if the foreground slot contains a value.
    /// If the slot is logically empty, returns `None`. This is a safe version that
    /// checks the presence bits before accessing memory.
    ///
    /// # Safety
    /// This function is fully safe and performs a presence check before dereferencing.
    ///
    /// # Returns
    /// - `Some(&T)` if the foreground slot is initialized
    /// - `None` if the foreground slot is uninitialized
    ///
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::new();
    /// map.push("x", 10);
    /// map.push("x", 20);
    /// assert_eq!(map.fg(&"x"), Some(&20));
    /// assert_eq!(map.bg(&"x"), Some(&10));
    /// ```
    #[inline]
    pub fn fg(&self) -> Option<&T> {
        let idx = self.fg_index();
        if self.is_slot_present(idx) {
            Some(unsafe { self.slots[idx].assume_init_ref() })
        } else {
            None
        }
    }

    /// Returns a reference to the foreground value **without checking** if it is present.
    ///
    /// # Safety
    /// This function **assumes** the foreground slot is initialized. Calling this when
    /// the slot is uninitialized (i.e. after a `pull()` without a background, or
    /// after constructing an empty `Overlay`) results in **undefined behavior**.
    ///
    /// Use [`fg`](Self::fg) if you are not certain the slot is populated.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry = Overlay::new_both("fg", "bg");
    /// assert_eq!(entry.fg_unchecked(), &"fg");
    /// assert_eq!(entry.bg_unchecked(), &"bg");
    /// ```
    #[inline]
    pub fn fg_unchecked(&self) -> &T {
        let idx = self.fg_index();
        unsafe { self.slots[idx].assume_init_ref() }
    }

    /// Returns a reference to the background value, if present.
    ///
    /// Returns `Some(&T)` only if the background slot is initialized.
    ///
    /// ```
    /// use overlay_map::OverlayMap;
    ///
    /// let mut map = OverlayMap::new();
    /// map.push("x", 10);
    /// map.push("x", 20);
    /// assert_eq!(map.fg(&"x"), Some(&20));
    /// assert_eq!(map.bg(&"x"), Some(&10));
    /// ```
    #[inline]
    pub fn bg(&self) -> Option<&T> {
        let idx = self.bg_index();
        if self.is_slot_present(idx) {
            Some(unsafe { self.slots[idx].assume_init_ref() })
        } else {
            None
        }
    }

    /// Returns a reference to the background value **without checking** if it is present.
    ///
    /// # Safety
    /// This assumes the background slot is initialized. Calling this when it is not
    /// will cause **undefined behavior**.
    ///
    /// Prefer [`bg`](Self::bg) if you're unsure whether the background is set.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry = Overlay::new_both("fg", "bg");
    /// assert_eq!(entry.fg_unchecked(), &"fg");
    /// assert_eq!(entry.bg_unchecked(), &"bg");
    /// ```
    #[inline]
    pub fn bg_unchecked(&self) -> &T {
        let idx = self.bg_index();
        unsafe { self.slots[idx].assume_init_ref() }
    }

    /// Returns `true` if both slots are empty.
    ///
    /// This is used to determine whether the entry contains any values
    /// at all. It does not consider which slot is foreground or background.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_fg("fg");
    /// assert!(!entry.is_empty());
    /// entry.pull();
    /// assert!(entry.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        (self.bits & SLOT_MASK) == 0
    }

    /// Returns `true` if both foreground and background values are currently present.
    ///
    /// This is useful for determining whether [`clear_unchecked`](Self::clear_unchecked)
    /// is safe to call.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// assert!(entry.is_full());
    ///
    /// entry.pull();
    /// assert!(!entry.is_full()); // background promoted, only one value remains
    /// ```
    #[inline]
    pub fn is_full(&self) -> bool {
        (self.bits & SLOT_MASK) == SLOT_MASK
    }

    /// Clears the overlay, dropping any foreground and background values.
    ///
    /// This is the most efficient way to reset the overlay to an empty state. It
    /// avoids value movement or promotion and directly drops the contents of both
    /// slots (if present). After calling `clear`, the overlay will report as empty,
    /// and both `fg()` and `bg()` will return `None`.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// assert_eq!(entry.fg(), Some(&"a"));
    /// assert_eq!(entry.bg(), Some(&"b"));
    ///
    /// entry.clear();
    ///
    /// assert_eq!(entry.fg(), None);
    /// assert_eq!(entry.bg(), None);
    /// assert!(entry.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        if (self.bits & SLOT0_PRESENT) != 0 {
            unsafe { self.slots[0].assume_init_drop() };
        }
        if (self.bits & SLOT1_PRESENT) != 0 {
            unsafe { self.slots[1].assume_init_drop() };
        }
        self.bits = 0;
    }

    /// Clears the overlay without checking which slots are present.
    ///
    /// This is an **unsafe**, ultra-fast variant of [`Overlay::clear`] that skips
    /// all internal presence checks. It will **unconditionally drop** both slots,
    /// regardless of whether they are actually initialized.
    ///
    /// # Safety
    ///
    /// You must guarantee that both the **foreground** and **background** values
    /// are currently present in the overlay. Calling this when either layer is
    /// missing will result in **undefined behavior**, such as memory corruption
    /// or double-drop.
    ///
    /// This is intended for use in performance-critical contexts where you already
    /// know the exact slot state — for example, if you've just cloned from a known
    /// full overlay, or you're clearing a batch of overlays all known to be full.
    ///
    /// For a safe version, use [`clear`](Self::clear).
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// entry.clear_unchecked(); // caller guarantees both slots are present
    ///
    /// assert!(entry.is_empty());
    /// ```
    ///
    /// # See Also
    /// - [`Overlay::clear`] — safe version with slot checks
    /// - [`Overlay::is_empty`] — to check for emptiness before clearing
    #[inline]
    pub fn clear_unchecked(&mut self) {
        unsafe {
            self.slots[0].assume_init_drop();
            self.slots[1].assume_init_drop();
        }
        self.bits = 0;
    }

    /// Push a value into the foreground layer, preserving the previous foreground in the background.
    ///
    /// If the foreground slot already contains a value, it is moved into the background slot.
    /// The new value is then written into the foreground slot. Any previous background value
    /// will be dropped to make room—no cloning is performed at any point.
    ///
    /// This operation is always safe, even if the entry is empty. If no foreground is currently
    /// present, the value will simply be inserted.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_fg("a");
    /// entry.push("b");
    ///
    /// assert_eq!(entry.fg(), Some(&"b"));
    /// assert_eq!(entry.bg(), Some(&"a"));
    /// ```
    #[inline]
    pub fn push(&mut self, val: T) {
        self.push_fg_to_bg();
        let idx = self.fg_index();
        self.slots[idx] = MaybeUninit::new(val);
        self.bits |= 1 << idx;
    }

    /// Safely pull the current foreground value out, promoting the background to foreground if present.
    ///
    /// If the foreground value is present, it is removed and returned. The background (if any) is
    /// promoted to the foreground. If neither value remains, the entry becomes empty.
    ///
    /// Returns `None` if the foreground was not present.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// let pulled = entry.pull();
    ///
    /// assert_eq!(pulled, Some("a"));
    /// assert_eq!(entry.fg(), Some(&"b")); // background promoted
    /// ```
    #[inline]
    pub fn pull(&mut self) -> Option<T> {
        let fgi = self.fg_index();
        if self.is_slot_present(fgi) {
            self.bits ^= FG_SLOT | (1 << fgi);
            Some(unsafe { self.slots[fgi].assume_init_read() })
        } else {
            None
        }
    }

    /// Pull the current foreground value without checking if it is present.
    ///
    /// # Safety
    /// The caller must ensure the foreground slot is present. If it is not, this will result
    /// in undefined behavior.
    ///
    /// See [`Self::pull`] for a safe alternative.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("fg", "bg");
    /// let pulled = entry.pull_unchecked();
    /// assert_eq!(pulled, "fg");
    /// assert_eq!(entry.fg(), Some(&"bg"));
    /// ```
    #[inline]
    pub fn pull_unchecked(&mut self) -> T {
        let fgi = self.fg_index();
        self.bits ^= FG_SLOT | (1 << fgi);
        unsafe { self.slots[fgi].assume_init_read() }
    }

    /// Swap in a new foreground value, returning the old background if present.
    ///
    /// If a background value exists, it is evicted and returned. The new value is written into
    /// the background slot, which is then promoted to become the new foreground. The current
    /// foreground is preserved in-place.
    ///
    /// If no background was present, this behaves like a standard push operation,
    /// and `None` is returned.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// let evicted = entry.swap("c");
    ///
    /// assert_eq!(evicted, Some("b"));
    /// assert_eq!(entry.fg(), Some(&"c"));
    /// assert_eq!(entry.bg(), Some(&"a"));
    /// ```
    #[inline]
    pub fn swap(&mut self, val: T) -> Option<T> {
        let bgi = self.bg_index();
        if self.is_slot_present(bgi) {
            let evicted = unsafe { self.slots[bgi].assume_init_read() };
            self.slots[bgi] = MaybeUninit::new(val);
            self.flip_unchecked();
            Some(evicted)
        } else {
            self.push(val);
            None
        }
    }

    /// Get an iterator over the foreground and background values.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry = Overlay::new_both("fg", "bg");
    /// let values: Vec<_> = entry.iter().cloned().collect();
    /// assert_eq!(values, vec!["fg", "bg"]);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.fg().into_iter().chain(self.bg())
    }

    /// Flips the foreground and background layers, if both are present.
    ///
    /// This operation swaps the logical roles of the two slots:
    ///
    /// - The foreground becomes the background
    /// - The background becomes the foreground
    ///
    /// If only one value is present, the overlay remains unchanged to preserve
    /// the guarantee that a foreground value is always present when the overlay is in use.
    ///
    /// This is a zero-cost, branchless operation — no memory is moved, cloned, or reallocated.
    /// Internally, it simply toggles a bit flag **only if** both slots are occupied.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// assert_eq!(entry.fg(), Some(&"a"));
    /// assert_eq!(entry.bg(), Some(&"b"));
    ///
    /// entry.flip();
    ///
    /// assert_eq!(entry.fg(), Some(&"b"));
    /// assert_eq!(entry.bg(), Some(&"a"));
    ///
    /// // Flip has no effect when only one value is present
    /// let mut single = Overlay::new_fg("only");
    /// single.flip();
    /// assert_eq!(single.fg(), Some(&"only"));
    /// assert_eq!(single.bg(), None);
    /// ```
    #[inline]
    pub fn flip(&mut self) {
        if (self.bits & SLOT_MASK) == SLOT_MASK {
            self.bits ^= FG_SLOT;
        }
    }

    /// Flips the foreground and background slots **without checking** if both are present.
    ///
    /// This is the unchecked, zero-cost variant of [`flip`](Self::flip), intended for internal
    /// or performance-critical use when it is already known that both slots contain valid values.
    ///
    /// This method **does not perform any presence checks**. If one of the slots is uninitialized,
    /// calling this method results in **undefined behavior** when those slots are later accessed.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that:
    ///
    /// - Both slots (foreground and background) are currently initialized.
    /// - A subsequent use of `fg_unchecked` or `bg_unchecked` will not access uninitialized memory.
    ///
    /// # Example
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let mut entry = Overlay::new_both("a", "b");
    /// entry.flip_unchecked(); // swaps roles without checks
    /// assert_eq!(entry.fg(), Some(&"b"));
    /// assert_eq!(entry.bg(), Some(&"a"));
    /// ```
    #[inline]
    pub fn flip_unchecked(&mut self) {
        self.bits ^= FG_SLOT;
    }

    #[inline]
    fn fg_index(&self) -> usize {
        ((self.bits & FG_SLOT) >> 2) as usize
    }

    #[inline]
    fn bg_index(&self) -> usize {
        self.fg_index() ^ 1
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
        if self.is_slot_present(bgi) {
            unsafe {
                self.slots[bgi].assume_init_drop();
            }
        }
        self.flip_unchecked();
    }
}

impl<T> Default for Overlay<T> {
    fn default() -> Self {
        Self::new_empty()
    }
}

impl<T> From<T> for Overlay<T> {
    fn from(value: T) -> Self {
        Self::new_fg(value)
    }
}

impl<T: Clone> Clone for Overlay<T> {
    fn clone(&self) -> Self {
        let mut clone = Self::new_empty();
        clone.bits = self.bits;

        if self.is_slot_present(0) {
            clone.slots[0] = MaybeUninit::new(unsafe { self.slots[0].assume_init_ref().clone() });
        }

        if self.is_slot_present(1) {
            clone.slots[1] = MaybeUninit::new(unsafe { self.slots[1].assume_init_ref().clone() });
        }

        clone
    }
}

impl<T: PartialEq> PartialEq for Overlay<T> {
    fn eq(&self, other: &Self) -> bool {
        if (self.bits & SLOT_MASK) != (other.bits & SLOT_MASK) {
            return false;
        }
        self.fg() == other.fg() && self.bg() == other.bg()
    }
}

impl<T: Eq> Eq for Overlay<T> {}

impl<V> Drop for Overlay<V> {
    fn drop(&mut self) {
        if (self.bits & SLOT0_PRESENT) != 0 {
            unsafe { self.slots[0].assume_init_drop() };
        }

        if (self.bits & SLOT1_PRESENT) != 0 {
            unsafe { self.slots[1].assume_init_drop() };
        }
    }
}

pub struct OverlayIntoIter<T> {
    overlay: Overlay<T>,
}

impl<T> Iterator for OverlayIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.overlay.pull()
    }
}

impl<T> IntoIterator for Overlay<T> {
    type Item = T;
    type IntoIter = OverlayIntoIter<T>;

    /// Creates an iterator over the values in the overlay.
    ///
    /// ```
    /// use overlay_map::Overlay;
    ///
    /// let entry = Overlay::new_both("fg", "bg");
    /// let values: Vec<_> = entry.into_iter().collect();
    /// assert_eq!(values, vec!["fg", "bg"]);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        OverlayIntoIter { overlay: self }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integration_push_pull_cycle() {
        let mut map = OverlayMap::<&str, i32>::new();

        map.push("x", 1);
        map.push("x", 2);
        map.push("x", 3);

        assert_eq!(map.fg(&"x"), Some(&3));
        assert_eq!(map.bg(&"x"), Some(&2));

        let pulled = map.pull(&"x");
        assert_eq!(pulled, Some(3));
        assert_eq!(map.fg(&"x"), Some(&2));

        let pulled = map.pull(&"x");
        assert_eq!(pulled, Some(2));
        assert_eq!(map.fg(&"x"), None);
        assert!(map.is_empty());
    }

    #[test]
    fn extend_count_overlapping_and_new() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.push("a", 10);
        map.push("b", 20);

        let replaced = map.extend_count([("a", 100), ("c", 300), ("b", 200)]);
        assert_eq!(replaced, 2); // a and b existed

        assert_eq!(map.fg(&"a"), Some(&100));
        assert_eq!(map.bg(&"a"), Some(&10));

        assert_eq!(map.fg(&"b"), Some(&200));
        assert_eq!(map.bg(&"b"), Some(&20));

        assert_eq!(map.fg(&"c"), Some(&300));
        assert_eq!(map.bg(&"c"), None);
    }

    #[test]
    fn push_if_and_swap_if_logic() {
        let mut map = OverlayMap::<&str, i32>::new();
        map.push("key", 1);

        let pushed = map.push_if(&"key", |v| if *v < 5 { Some(*v + 10) } else { None });
        assert!(pushed);
        assert_eq!(map.fg(&"key"), Some(&11));
        assert_eq!(map.bg(&"key"), Some(&1));

        let evicted = map.swap_if(&"key", |v| if *v == 11 { Some(42) } else { None });
        assert_eq!(evicted, Some(1));
        assert_eq!(map.fg(&"key"), Some(&42));
        assert_eq!(map.bg(&"key"), Some(&11));
    }
}
