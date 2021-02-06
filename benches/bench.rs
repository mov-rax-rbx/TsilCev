#![feature(drain_filter)]
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::collections::LinkedList;
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
}

const SIZE: usize = 570;
lazy_static! {
    static ref TEST_DATA: Vec<Test<'static>> =
        (0..SIZE).into_iter().map(|x| Test::new(x)).collect();
}

// static SAMPLE: [usize; 4] = [
//     TEST_DATA.len() / 4,
//     TEST_DATA.len() / 2,
//     3 * TEST_DATA.len() / 4,
//     TEST_DATA.len(),
// ];

const SAMPLE: [usize; 1] = [SIZE];

fn pop_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_front");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(&TEST_DATA[..i]);
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter(|| {
                let mut tc = tc.clone();
                for _ in 0..i {
                    tc.pop_front();
                }
            })
        });

        let mut ll = LinkedList::new();
        for x in TEST_DATA.iter().take(i) {
            ll.push_back(x.clone());
        }
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter(|| {
                let mut ll = ll.clone();
                for _ in 0..i {
                    ll.pop_front();
                }
            })
        });
    }

    group.finish();
}

fn push_back(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::new();
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter(|| {
                let mut tc = tc.clone();
                for x in TEST_DATA.iter() {
                    tc.push_back(x);
                }
            })
        });

        let ll = LinkedList::new();
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter(|| {
                let mut ll = ll.clone();
                for x in TEST_DATA.iter() {
                    ll.push_back(x);
                }
            })
        });
    }

    group.finish();
}

fn from_iter(c: &mut Criterion) {
    use std::iter::FromIterator;
    let mut group = c.benchmark_group("from_iter");

    for &i in SAMPLE.iter() {
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter(|| {
                let _ = TsilCev::from_iter(TEST_DATA.iter());
            })
        });

        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter(|| {
                let _ = LinkedList::from_iter(TEST_DATA.iter());
            })
        });
    }

    group.finish();
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back() -> pop_back() -> push_front() -> pop_front()");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::with_capacity(TEST_DATA.len());
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| {
            b.iter(|| {
                let mut tc = tc.clone();
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
            })
        });

        let ll = LinkedList::new();
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter(|| {
                let mut ll = ll.clone();
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
            })
        });
    }

    group.finish();
}

fn remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("drain_filter");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(&TEST_DATA[..i]);
        group.bench_function(BenchmarkId::new("TsilCev LinkedList order", i), |b| {
            b.iter(|| {
                let mut tc = tc.clone();
                let mut cnt = 0;
                tc.drain_filter_tsil(|_| {
                    cnt += 1;
                    cnt & 1 == 0
                });
            })
        });

        group.bench_function(BenchmarkId::new("TsilCev Vec order", i), |b| {
            b.iter(|| {
                let mut tc = tc.clone();
                let mut cnt = 0;
                tc.drain_filter_cev(|_| {
                    cnt += 1;
                    cnt & 1 == 0
                });
            })
        });

        let mut ll = LinkedList::new();
        for x in TEST_DATA.iter().take(i) {
            ll.push_back(x.clone());
        }
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| {
            b.iter(|| {
                let mut ll = ll.clone();
                let mut cnt = 0;
                ll.drain_filter(|_| {
                    cnt += 1;
                    cnt & 1 == 0
                });
            })
        });
    }

    group.finish();
}

fn into_to_vec(c: &mut Criterion) {
    let mut group = c.benchmark_group("into_to_vec");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(TEST_DATA.as_slice());
        group.bench_function(BenchmarkId::new("TsilCev into_vec", i), |b| {
            b.iter(|| {
                let _ = tc.clone().into_vec();
            })
        });

        group.bench_function(BenchmarkId::new("TsilCev to_vec", i), |b| {
            b.iter(|| {
                let _ = tc.to_vec();
            })
        });
    }

    group.finish();
}

fn make_linked_list_order(c: &mut Criterion) {
    let mut group = c.benchmark_group("make_linked_list_order");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(TEST_DATA.as_slice());
        group.bench_function(
            BenchmarkId::new("make_linked_list_order for sequence", i),
            |b| {
                b.iter(|| {
                    tc.clone().make_linked_list_order();
                })
            },
        );

        let mut tc = TsilCev::with_capacity(i);
        for x in 0..i {
            if x & 1 == 0 {
                tc.push_back(TEST_DATA[x].clone());
            } else {
                tc.push_front(TEST_DATA[x].clone());
            }
        }
        group.bench_function(
            BenchmarkId::new("TsilCev push back, front, back, etc", i),
            |b| {
                b.iter(|| {
                    tc.clone().make_linked_list_order();
                })
            },
        );
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
    benches, pop_front,
    // push_back,
    // from_iter,
    // bench,
    remove,
    // into_to_vec,
    // make_linked_list_order,
    // iter,
);
criterion_main!(benches);
