use std::collections::HashMap;

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use overlaymap::OverlayMap;

fn bench_overlaymap_insert(c: &mut Criterion) {
    const N: u64 = 10_000;

    c.bench_function("overlaymap_insert_10k_unique", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(black_box(i), black_box(i));
            }
        });
    });

    c.bench_function("overlaymap_insert_10k_overwrite", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i); // first insert
            }
            for i in 0..N {
                map.insert(black_box(i), black_box(i + 1)); // overwrite with new foreground
            }
        });
    });

    c.bench_function("overlaymap_insert_10k_mixed_existing", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            // Insert even keys first
            for i in (0..N).step_by(2) {
                map.insert(i, i);
            }
            // Insert everything (evens again and new odds)
            for i in 0..N {
                map.insert(black_box(i), black_box(i + 1));
            }
        });
    });

    c.bench_function("baseline_insert_10k_unique", |b| {
        b.iter(|| {
            let mut map = HashMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(black_box(i), black_box(i));
            }
        });
    });

    c.bench_function("baseline_insert_10k_overwrite", |b| {
        b.iter(|| {
            let mut map = HashMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i); // first insert
            }
            for i in 0..N {
                map.insert(black_box(i), black_box(i + 1)); // overwrite with new foreground
            }
        });
    });

    c.bench_function("baseline_insert_10k_mixed_existing", |b| {
        b.iter(|| {
            let mut map = HashMap::<u64, u64>::new();
            // Insert even keys first
            for i in (0..N).step_by(2) {
                map.insert(i, i);
            }
            // Insert everything (evens again and new odds)
            for i in 0..N {
                map.insert(black_box(i), black_box(i + 1));
            }
        });
    });
}

criterion_group!(benches, bench_overlaymap_insert);
criterion_main!(benches);
