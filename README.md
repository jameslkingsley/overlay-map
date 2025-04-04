# overlay-map

**overlay-map** is a two-layered map data structure for Rust that allows for non-destructive updates by maintaining both a **foreground** (mutable) and a **background** (read-only) value layer for each key.

It’s designed for scenarios where you want to:
- Apply temporary or just-in-time changes without mutating original data.
- Implement overlays, deltas, rollback-able changes, or speculative state changes.
- Avoid cloning/copying values unnecessarily on update.

> ⚠️ **Work in progress**: This library is still evolving. Planned features
> include thread-safe version, rollback support, and a wider API.

## 📦 Features

- ✅ Foreground and background storage per key
- ✅ On insert, the old foreground is pushed to background (only **one** previous value is retained — not a full history)
- ✅ If a key exists, its foreground is **always** present — no fallback logic is required during reads
- ✅ Zero-cost value pushing (via in-place pointer tricks)
- ✅ No cloning required on push
- ✅ Optional conditional pushes (`push_if`)
- ✅ Extendable from other maps

## 🚀 Example

```rust
use overlay_map::OverlayMap;

#[derive(Debug, Clone, PartialEq)]
struct QuantumBit {
    collapsed: bool,
    value: Option<bool>,
}

/// Simulates measurement collapse
fn collapse(mut qbit: QuantumBit) -> QuantumBit {
    qbit.collapsed = true;
    qbit.value = Some(rand::random());
    qbit
}

fn main() {
    let mut qstate = OverlayMap::<&str, QuantumBit>::new();

    // Push an uncollapsed qubit
    qstate.push(
        "qbit_1",
        QuantumBit {
            collapsed: false,
            value: None,
        },
    );

    // Observe the qubit: only collapse if it's not already
    let did_observe = qstate.push_if(&"qbit_1", |current| {
        if current.collapsed {
            None // already collapsed, don't change
        } else {
            Some(collapse(current.clone())) // clone *only* if needed
        }
    });

    println!("Was observed?       {}", did_observe);
    println!("After observation:  {:?}", qstate.fg(&"qbit_1"));
    println!("Before observation: {:?}", qstate.bg(&"qbit_1"));
}
```

## 🧠 Why?

This is useful when:
- You want to track *current vs previous* state (not full history).
- You're doing **speculative updates** or **rollback systems** (planned).
- You need **non-destructive overlays** (e.g. config layering, versioning, etc).
- You want to avoid expensive cloning when replacing data.

## 📚 Documentation

- [Docs.rs](https://docs.rs/overlay-map)
- [Crates.io](https://crates.io/crates/overlay-map)

## 🔒 License

MIT

## ✨ Contributing

Contributions, bug reports, and feature requests welcome.

Planned areas of work:
- Thread-safe version
- Rollback support
- More expressive APIs
