use divan::{AllocProfiler, black_box};
use hashbrown::HashMap;
use nohash_hasher::BuildNoHashHasher;
use overlay_map::OverlayMap;

type Hasher = BuildNoHashHasher<u64>;

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

#[divan::bench]
fn get(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(123, 123);
            map
        })
        .bench_values(|map| {
            black_box(map.fg(&123));
        });
}

#[divan::bench]
fn push_new(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default()))
        .bench_values(|mut map| {
            black_box(map.push(black_box(1), black_box(1)));
        });
}

#[divan::bench]
fn push_existing(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map
        })
        .bench_values(|mut map| {
            black_box(map.push(black_box(1), black_box(2)));
        });
}

#[divan::bench]
fn swap(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map.push(1, 2);
            map
        })
        .bench_values(|mut map| {
            black_box(map.swap(1, 3));
        });
}

#[divan::bench]
fn extend_count(bencher: divan::Bencher) {
    let base = {
        let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
        map.push(1, 1);
        map
    };

    let other = {
        let mut m = HashMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
        m.insert(1, 1);
        m
    };

    bencher
        .with_inputs(move || (base.clone(), other.clone()))
        .bench_values(|(mut map, other)| {
            black_box(map.extend_count(other));
        });
}

#[divan::bench]
fn push_if(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map
        })
        .bench_values(|mut map| {
            black_box(map.push_if(&1, |v| Some(v + 1)));
        });
}

#[divan::bench]
fn pull(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map.push(1, 2);
            map
        })
        .bench_values(|mut map| {
            black_box(map.pull(&1));
        });
}

#[divan::bench]
fn pull_if(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map.push(1, 2);
            map
        })
        .bench_values(|mut map| {
            black_box(map.pull_if(&1, |v| *v == 2));
        });
}

#[divan::bench]
fn swap_if(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map.push(1, 2);
            map
        })
        .bench_values(|mut map| {
            black_box(map.swap_if(&1, |v| if *v == 2 { Some(99) } else { None }));
        });
}

#[divan::bench]
fn flip(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut map = OverlayMap::<u64, u64, Hasher>::with_hasher(Hasher::default());
            map.push(1, 1);
            map.push(1, 2);
            map
        })
        .bench_values(|mut map| {
            black_box(map.flip(&1));
        });
}

fn main() {
    divan::main();
}
