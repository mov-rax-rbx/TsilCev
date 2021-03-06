#![feature(drain_filter)]
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, BatchSize};
use std::collections::LinkedList;
use std::collections::VecDeque;
use std::iter::FromIterator;
use tsil_cev::TsilCev;

#[macro_use]
extern crate lazy_static;

#[derive(Debug, Clone, PartialEq)]
struct Test<'a> {
    f: f64,
    u: usize,
    line: &'a str,
}

const LINE: &'static str = "n.to_string()";

impl<'a> Test<'a> {
    #[inline]
    const fn new(n: usize) -> Self {
        Self {
            f: n as f64,
            u: n,
            line: LINE,
        }
    }
    #[inline]
    fn add_one(&mut self) {
        self.f += 1.0;
        self.u += 1;
    }
    #[inline]
    fn get_val(&self) -> usize {
        self.u
    }
}

const SIZE: usize = 1 << 20;
// const SIZE: usize = 570;
lazy_static! {
    static ref TEST_DATA: Vec<Test<'static>> =
        (0..SIZE).into_iter().map(|x| Test::new(x)).collect();
    static ref SAMPLE: Vec<usize> =
        (0..64).into_iter().rev().filter(|x| SIZE >> x != 0).map(|x| SIZE >> x).collect();
        // [SIZE].to_vec();
}

fn pop_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_front");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(&TEST_DATA[..i]);
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter_batched(|| tc.clone(), |mut tc| {
                for _ in 0..i {
                    tc.pop_front();
                }
            },
            BatchSize::LargeInput);
        });

        let dec = VecDeque::from_iter(TEST_DATA.iter().take(i).cloned());
        group.bench_function(BenchmarkId::new("VecDeque", i), |b| {
            b.iter_batched(|| dec.clone(), |mut dec| {
                for _ in 0..i {
                    dec.pop_front();
                }
            },
            BatchSize::LargeInput);
        });

        let ll = LinkedList::from_iter(TEST_DATA.iter().take(i).cloned());
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter_batched(|| ll.clone(), |mut ll| {
                for _ in 0..i {
                    ll.pop_front();
                }
            },
            BatchSize::LargeInput);
        });
    }

    group.finish();
}

fn push_back(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back");

    for &i in SAMPLE.iter() {

        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter_batched(|| TsilCev::new(), |mut tc| {
                for x in TEST_DATA.iter().take(i) {
                    tc.push_back(x);
                }
            },
            BatchSize::LargeInput);
        });

        group.bench_function(BenchmarkId::new("VecDeque", i), |b| {
            b.iter_batched(|| VecDeque::new(), |mut dec| {
                for x in TEST_DATA.iter().take(i) {
                    dec.push_back(x);
                }
            },
            BatchSize::LargeInput);
        });

        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter_batched(|| LinkedList::new(), |mut ll| {
                for x in TEST_DATA.iter().take(i) {
                    ll.push_back(x);
                }
            },
            BatchSize::LargeInput);
        });
    }

    group.finish();
}

fn from_iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_iter");

    for &i in SAMPLE.iter() {
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter(|| {
                let _ = TsilCev::from_iter(TEST_DATA.iter().take(i).cloned());
            });
        });

        group.bench_function(BenchmarkId::new("VecDeque", i), |b| {
            b.iter(|| {
                let _ = VecDeque::from_iter(TEST_DATA.iter().take(i).cloned());
            });
        });

        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter(|| {
                let _ = LinkedList::from_iter(TEST_DATA.iter().take(i).cloned());
            });
        });
    }

    group.finish();
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back() -> pop_back() -> push_front() -> pop_front()");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::with_capacity(i);
        group.bench_function(BenchmarkId::new("TsilCev with_capacity", i), |b| {
            b.iter_batched(|| tc.clone(), |mut tc| {
                for x in TEST_DATA.iter().take(i / 2) {
                    tc.push_back(x.clone());
                }
                for _ in TEST_DATA.iter().take(i / 4) {
                    tc.pop_front();
                }
                for x in TEST_DATA.iter().take(i / 2) {
                    tc.push_front(x.clone());
                }
                for _ in TEST_DATA.iter().take(i / 2) {
                    tc.pop_back();
                }
            },
            BatchSize::LargeInput);
        });

        let dec = VecDeque::with_capacity(i);
        group.bench_function(BenchmarkId::new("VecDeque with_capacity", i), |b| {
            b.iter_batched(|| dec.clone(), |mut dec| {
                for x in TEST_DATA.iter().take(i / 2) {
                    dec.push_back(x.clone());
                }
                for _ in TEST_DATA.iter().take(i / 4) {
                    dec.pop_front();
                }
                for x in TEST_DATA.iter().take(i / 2) {
                    dec.push_front(x.clone());
                }
                for _ in TEST_DATA.iter().take(i / 2) {
                    dec.pop_back();
                }
            },
            BatchSize::LargeInput);
        });

        let ll = LinkedList::new();
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter_batched(|| ll.clone(), |mut ll| {
                for x in TEST_DATA.iter().take(i / 2) {
                    ll.push_back(x.clone());
                }
                for _ in TEST_DATA.iter().take(i / 4) {
                    ll.pop_front();
                }
                for x in TEST_DATA.iter().take(i / 2) {
                    ll.push_front(x.clone());
                }
                for _ in TEST_DATA.iter().take(i / 2) {
                    ll.pop_back();
                }
            },
            BatchSize::LargeInput);
        });
    }

    group.finish();
}

fn remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("drain_filter");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(&TEST_DATA[..i]);
        group.bench_function(BenchmarkId::new("TsilCev LinkedList order", i), |b| {
            b.iter_batched(|| tc.clone(), |mut tc| {
                let _ = tc.drain_filter_tsil(|x| x.get_val() & 1 == 0);
            },
            BatchSize::LargeInput);
        });

        group.bench_function(BenchmarkId::new("TsilCev Vec order", i), |b| {
            b.iter_batched(|| tc.clone(), |mut tc| {
                let _ = tc.drain_filter_cev(|x| x.get_val() & 1 == 0);
            },
            BatchSize::LargeInput);
        });

        let dec = VecDeque::from_iter(TEST_DATA.iter().take(i).cloned());
        group.bench_function(BenchmarkId::new("VecDeque remove with save order", i), |b| {
            b.iter_batched(|| dec.clone(), |mut dec| {
                let mut x = 0;
                let mut end = i;
                while x < end {
                    if dec[x].get_val() & 1 == 0 {
                        let _ = dec.remove(x);
                        end -= 1;
                        continue;
                    }
                    x += 1;
                }
            },
            BatchSize::LargeInput);
        });

        group.bench_function(BenchmarkId::new("VecDeque swap_remove_back", i), |b| {
            b.iter_batched(|| dec.clone(), |mut dec| {
                let mut x = 0;
                let mut end = i;
                while x < end {
                    let val = &dec[x];
                    if val.get_val() & 1 == 0 {
                        dec.swap_remove_back(x);
                        end -= 1;
                        continue;
                    }
                    x += 1;
                }
            },
            BatchSize::LargeInput);
        });

        let ll = LinkedList::from_iter(TEST_DATA.iter().take(i).cloned());
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter_batched(|| ll.clone(), |mut ll| {
                let _ = ll.drain_filter(|x| x.get_val() & 1 == 0);
            },
            BatchSize::LargeInput);
        });
    }

    group.finish();
}

fn iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator");

    for &i in SAMPLE.iter() {
        let mut tc = TsilCev::from(&TEST_DATA[..i]);
        group.bench_function(BenchmarkId::new("TsilCev.iter_tsil_mut()", i), |b| {
            b.iter(|| {
                for x in tc.iter_tsil_mut() {
                    x.add_one();
                }
            })
        });
        group.bench_function(BenchmarkId::new("TsilCev.iter_cev_mut()", i), |b| {
            b.iter(|| {
                for x in tc.iter_cev_mut() {
                    x.add_one();
                }
            })
        });

        let mut dec = VecDeque::from_iter(TEST_DATA.iter().take(i).cloned());
        group.bench_function(BenchmarkId::new("VecDeque", i), |b| {
            b.iter(|| {
                for x in dec.iter_mut() {
                    x.add_one();
                }
            })
        });

        let mut ll = LinkedList::new();
        for x in TEST_DATA.iter().take(i) {
            ll.push_back(x.clone());
        }
        group.bench_function(BenchmarkId::new("LinkedList.iter_mut()", i), |b| {
            b.iter(|| {
                for x in ll.iter_mut() {
                    x.add_one();
                }
            })
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    pop_front,
    push_back,
    from_iter,
    bench,
    remove,
    iter,
);
criterion_main!(benches);
