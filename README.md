# overlaymap

**overlaymap** is a two-layered map data structure for Rust that allows for non-destructive updates by maintaining both a **foreground** (mutable) and a **background** (read-only) value layer for each key.

It’s designed for scenarios where you want to:
- Apply temporary or just-in-time changes without mutating original data.
- Implement overlays, deltas, rollback-able changes, or speculative state changes.
- Avoid cloning/copying values unnecessarily on update.

> ⚠️ **Work in progress**: This library is still evolving. Planned features include rollback support and a wider API.

## 📦 Features

- ✅ Foreground and background storage per key
- ✅ On insert, the old foreground is pushed to background (only **one** previous value is retained — not a full history)
- ✅ If a key exists, its foreground is **always** present — no fallback logic is required during reads
- ✅ Zero-cost value swapping (via in-place pointer tricks)
- ✅ No cloning required on insert
- ✅ Optional conditional swaps (`try_swap`)
- ✅ Extendable from other maps

## 🚀 Example

```rust
use overlaymap::OverlayMap;

let mut map = OverlayMap::new();

map.insert("name", "Alice");
assert_eq!(map.get(&"name"), Some(&"Alice"));

// Update the value; old one is pushed to background
map.insert("name", "Bob");
assert_eq!(map.get(&"name"), Some(&"Bob"));
assert_eq!(map.get_background(&"name"), Some(&"Alice"));

// Conditionally swap with a predicate
map.try_swap(&"name", |current| {
    if *current == "Bob" {
        Some("Charlie")
    } else {
        None
    }
});

assert_eq!(map.get(&"name"), Some(&"Charlie"));
assert_eq!(map.get_background(&"name"), Some(&"Bob"));
```

## 🧠 Why?

This is useful when:
- You want to track *current vs previous* state (not full history).
- You're doing **speculative updates** or **rollback systems** (planned).
- You need **non-destructive overlays** (e.g. config layering, versioning, etc).
- You want to avoid expensive cloning when replacing data.

## 🔨 API Summary

- `insert(key, value)` — Inserts a value. Pushes existing foreground into background.
- `get(key)` / `get_foreground(key)` — Get the current value.
- `get_background(key)` — Get the previous value if available.
- `try_swap(key, predicate)` — Conditionally replace foreground based on the current value.
- `extend(other_map)` — Merge another `HashMap` into this one with the same semantics.

## 📚 Documentation

- [Docs.rs](https://docs.rs/overlaymap)
- [Crates.io](https://crates.io/crates/overlaymap)

## 🔒 License

MIT

## ✨ Contributing

Contributions, bug reports, and feature requests welcome.
Planned areas of work:
- Rollback support
- More expressive APIs
