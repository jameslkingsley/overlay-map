use criterion::{Criterion, black_box, criterion_group, criterion_main};
use overlaymap::OverlayMap;

fn bench_overlaymap_try_swap(c: &mut Criterion) {
    const N: u64 = 10_000;

    c.bench_function("try_swap_no_changes", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i); // insert into foreground
            }
            for i in 0..N {
                map.try_swap(&black_box(i), |old| {
                    if *old == i {
                        None // simulate no-op
                    } else {
                        Some(*old)
                    }
                });
            }
        });
    });

    c.bench_function("try_swap_all_change", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i); // insert into foreground
            }
            for i in 0..N {
                map.try_swap(&black_box(i), |old| Some(black_box(*old + 1)));
            }
        });
    });

    c.bench_function("try_swap_half_exist_half_missing", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            // Insert every other key
            for i in (0..N).step_by(2) {
                map.insert(i, i);
            }
            for i in 0..N {
                map.try_swap(&black_box(i), |old| Some(black_box(*old + 1)));
            }
        });
    });

    c.bench_function("try_swap_background_promote", |b| {
        b.iter(|| {
            let mut map = OverlayMap::<u64, u64>::new();
            for i in 0..N {
                map.insert(i, i);
                map.insert(i, i); // triggers background insertion via second insert
            }
            for i in 0..N {
                map.try_swap(&black_box(i), |old| Some(black_box(*old + 1)));
            }
        });
    });
}

criterion_group!(benches, bench_overlaymap_try_swap);
criterion_main!(benches);
