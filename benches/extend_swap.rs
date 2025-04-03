use criterion::{Criterion, black_box, criterion_group, criterion_main};
use overlaymap::OverlayMap;
use std::collections::HashMap;

fn bench_overlaymap_extend_swap(c: &mut Criterion) {
    const N: u64 = 10_000;

    c.bench_function("extend_swap_all_new", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            let updates: HashMap<_, _> = (0..N).map(|i| (i, i)).collect();
            map.extend_swap(black_box(updates));
        });
    });

    c.bench_function("extend_swap_all_existing_foreground", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i);
            }
            let updates: HashMap<_, _> = (0..N).map(|i| (i, i + 1)).collect();
            map.extend_swap(black_box(updates));
        });
    });

    c.bench_function("extend_swap_all_existing_background", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i);
                map.insert(i, i); // promote old value to background
            }
            let updates: HashMap<_, _> = (0..N).map(|i| (i, i + 1)).collect();
            map.extend_swap(black_box(updates));
        });
    });

    c.bench_function("extend_swap_half_new_half_existing", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in (0..N).step_by(2) {
                map.insert(i, i);
            }
            let updates: HashMap<_, _> = (0..N).map(|i| (i, i + 2)).collect();
            map.extend_swap(black_box(updates));
        });
    });
}

criterion_group!(benches, bench_overlaymap_extend_swap);
criterion_main!(benches);
