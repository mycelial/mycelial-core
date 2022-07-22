use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use mycelial_crdt::list;
use rand::prelude::*;

fn seed() -> [u8; 32] {
    [b'm', b'p', b'g', b'a', b'd', b't', b'j']
        .into_iter()
        .chain(std::iter::repeat(0))
        .take(32)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

fn append(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/append");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let list = &mut list::List::new(0);
            b.iter(|| {
                for _ in 0..size {
                    list.append(0.0.into()).expect("failed to append");
                }
            })
        });
    }
}

fn prepend(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/prepend");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let list = &mut list::List::new(0);
            b.iter(|| {
                for _ in 0..size {
                    list.prepend(0.0.into()).expect("failed to prepend");
                }
            })
        });
    }
}

fn insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/insert");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let list = &mut list::List::new(0);
            b.iter_batched(
                || {
                    let mut gen = rand::rngs::SmallRng::from_seed(seed());
                    (0..size)
                        .map(|sz| if sz == 0 { 0 } else { gen.gen::<usize>() % sz })
                        .collect::<Vec<usize>>()
                },
                |insert_positions| {
                    for pos in insert_positions {
                        list.insert(pos, 0.0.into()).expect("failed to insert");
                    }
                },
                BatchSize::SmallInput,
            )
        });
    }
}

fn delete(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/delete");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let mut list = list::List::new(0);
                    let mut gen = rand::rngs::SmallRng::from_seed(seed());
                    let deletions = (0..size)
                        .rev()
                        .map(|sz| {
                            list.prepend(0.0.into()).expect("failed to prepend");
                            if sz == 0 {
                                0
                            } else {
                                gen.gen::<usize>() % sz
                            }
                        })
                        .collect::<Vec<usize>>();
                    (list, deletions)
                },
                |(mut list, deletions)| {
                    for pos in deletions {
                        list.delete(pos).expect("failed to delete")
                    }
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish()
}

fn size(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/size");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let mut list = list::List::new(0);
                    (0..size).for_each(|_| {
                        list.prepend(0.0.into()).expect("failed to prepend");
                    });
                    list
                },
                |list| list.size(),
                BatchSize::SmallInput,
            );
        });
    }
    group.finish()
}

fn diff(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/diff");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let mut list = list::List::new(0);
                    (0..size).for_each(|_| {
                        list.prepend(0.0.into()).expect("failed to prepend");
                    });
                    (list, list::List::new(1).vclock().clone())
                },
                |(list, vclock)| {
                    let diff = list.diff(&vclock);
                    assert!(diff.len() == size);
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish()
}

fn apply(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/apply");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let mut list = list::List::new(0);
                    (0..size).for_each(|_| {
                        list.prepend(0.0.into()).expect("failed to prepend");
                    });
                    (list::List::new(1), list.diff(list::List::new(1).vclock()))
                },
                |(mut list, diff)| {
                    list.apply(&diff).expect("failed to apply");
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish()
}

fn to_vec(c: &mut Criterion) {
    let mut group = c.benchmark_group("list/to_vec");
    group.warm_up_time(std::time::Duration::from_millis(250));
    for size in [256, 512, 1024, 2048, 4096, 8128, 16384] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let mut list = list::List::new(0);
                    (0..size * 2).for_each(|_| {
                        list.prepend(0.0.into()).expect("failed to prepend");
                    });
                    (0..size).for_each(|_| list.delete(0).expect("failed to delete"));
                    list
                },
                |list| assert!(list.to_vec().len() == size),
                BatchSize::SmallInput,
            );
        });
    }
    group.finish()
}

criterion_group!(list, append, prepend, insert, delete, size, diff, apply, to_vec,);

criterion_main!(list);
