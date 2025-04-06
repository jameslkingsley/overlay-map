use divan::{AllocProfiler, black_box};
use overlay_map::Overlay;

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

#[divan::bench]
fn new_fg(bencher: divan::Bencher) {
    bencher.bench_local(|| black_box(Overlay::new_fg(black_box(1))));
}

#[divan::bench]
fn new_both(bencher: divan::Bencher) {
    bencher.bench_local(|| black_box(Overlay::new_both(black_box(1), black_box(2))));
}

#[divan::bench]
fn fg(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_fg(123))
        .bench_values(|entry| {
            black_box(entry.fg());
        });
}

#[divan::bench]
fn fg_unchecked(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_fg(123))
        .bench_values(|entry| {
            black_box(entry.fg_unchecked());
        });
}

#[divan::bench]
fn bg(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(123, 456))
        .bench_values(|entry| {
            black_box(entry.bg());
        });
}

#[divan::bench]
fn bg_unchecked(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(123, 456))
        .bench_values(|entry| {
            black_box(entry.bg_unchecked());
        });
}

#[divan::bench]
fn push(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_fg(1))
        .bench_values(|mut entry| {
            black_box(entry.push(black_box(2)));
        });
}

#[divan::bench]
fn pull(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(1, 2))
        .bench_values(|mut entry| {
            black_box(entry.pull());
        });
}

#[divan::bench]
fn pull_unchecked(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(1, 2))
        .bench_values(|mut entry| {
            black_box(entry.pull_unchecked());
        });
}

#[divan::bench]
fn swap(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(1, 2))
        .bench_values(|mut entry| {
            black_box(entry.swap(black_box(3)));
        });
}

#[divan::bench]
fn flip(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(1, 2))
        .bench_values(|mut entry| {
            entry.flip();
            black_box(entry);
        });
}

#[divan::bench]
fn clear(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(1, 2))
        .bench_values(|mut entry| {
            entry.clear();
            black_box(entry);
        });
}

#[divan::bench]
fn clear_unchecked(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_both(1, 2))
        .bench_values(|mut entry| {
            entry.clear_unchecked();
            black_box(entry);
        });
}

#[divan::bench]
fn is_empty(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| Overlay::new_fg(123))
        .bench_values(|entry| {
            black_box(entry.is_empty());
        });
}

fn main() {
    divan::main();
}
