use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use overlay_map::Overlay;

fn bench_push(c: &mut Criterion) {
    let mut group = c.benchmark_group("push");

    group.bench_function("overlay", |b| {
        b.iter_batched(
            || Overlay::new_both(1, 2), // both fg and bg already present
            |mut overlay| {
                black_box(overlay.push(3)); // push evicts fg to bg
            },
            BatchSize::SmallInput,
        );
    });

    group.bench_function("tuple", |b| {
        b.iter_batched(
            || Some((2, Some(1))), // both fg and bg already present
            |mut val| {
                if let Some((fg, bg)) = &mut val {
                    *bg = Some(std::mem::replace(fg, 3)); // same logic: evict fg to bg
                }
                black_box(val);
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

fn bench_pull(c: &mut Criterion) {
    let mut group = c.benchmark_group("pull");

    group.bench_function("overlay", |b| {
        b.iter_batched(
            || Overlay::new_both(1, 2),
            |mut overlay| {
                black_box(overlay.pull());
            },
            BatchSize::SmallInput,
        );
    });

    group.bench_function("tuple", |b| {
        b.iter_batched(
            || Some((2, Some(1))),
            |mut val| {
                let result = if let Some((fg, bg)) = val.as_mut() {
                    let old = *fg;
                    if let Some(new_fg) = bg.take() {
                        *fg = new_fg;
                        Some(old)
                    } else {
                        val = None;
                        Some(old)
                    }
                } else {
                    None
                };
                black_box(val);
                black_box(result);
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

fn bench_swap(c: &mut Criterion) {
    let mut group = c.benchmark_group("swap");

    group.bench_function("overlay", |b| {
        b.iter_batched(
            || Overlay::new_both(1, 2),
            |mut overlay| {
                black_box(overlay.swap(3));
            },
            BatchSize::SmallInput,
        );
    });

    group.bench_function("tuple", |b| {
        b.iter_batched(
            || Some((2, Some(1))),
            |mut val| {
                let result = if let Some((fg, bg)) = &mut val {
                    let old_fg = *fg;
                    let old_bg = bg.replace(old_fg);
                    *fg = 3;
                    old_bg
                } else {
                    val = Some((3, None::<i32>));
                    None
                };
                black_box(val);
                black_box(result);
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

fn bench_flip(c: &mut Criterion) {
    let mut group = c.benchmark_group("flip");

    group.bench_function("overlay", |b| {
        b.iter_batched(
            || Overlay::new_both(1, 2),
            |mut overlay| {
                overlay.flip();
                black_box(overlay);
            },
            BatchSize::SmallInput,
        );
    });

    group.bench_function("tuple", |b| {
        b.iter_batched(
            || Some((1, Some(2))),
            |mut val| {
                if let Some((fg, bg)) = &mut val {
                    if let Some(actual_bg) = bg.take() {
                        std::mem::swap(fg, &mut *bg.get_or_insert(actual_bg));
                    }
                }
                black_box(val);
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

criterion_group!(benches, bench_push, bench_pull, bench_swap, bench_flip);
criterion_main!(benches);
