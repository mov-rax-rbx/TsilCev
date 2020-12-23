#![feature(linked_list_cursors)]
use std::collections::LinkedList;
use tsil_cev::TsilCev;
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};

#[derive(Clone, PartialEq)]
struct Test<'a> {
    f: f64,
    u: usize,
    line: &'a str,
}

const LINE: &'static str = "n.to_string()";

impl<'a> Test<'a> {
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

const NUMS: &'static [Test] = &[
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5), Test::new(9),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
    Test::new(9), Test::new(1), Test::new(5), Test::new(8), Test::new(9), Test::new(5),
];

const SAMPLE: [usize; 4] = [NUMS.len() / 4, NUMS.len() / 2, 3 * NUMS.len() / 4, NUMS.len()];

fn pop_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_front");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(NUMS);
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| b.iter(|| {
            let mut tc = tc.clone();
            for _ in 0..i {
                tc.pop_front();
            }
        }));

        let mut ll = LinkedList::new();
        for x in NUMS.iter().take(i) {
            ll.push_back(x.clone());
        }
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| b.iter(|| {
            let mut ll = ll.clone();
            for _ in 0..i {
                ll.pop_front();
            }
        }));
    }

    group.finish();
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back() -> pop_back() -> push_front() -> pop_front()");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::with_capacity(NUMS.len());
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| b.iter(|| {
            let mut tc = tc.clone();
            for x in NUMS.iter().take(i / 2) {
                tc.push_back(x.clone());
            }
            for _ in NUMS.iter().take(i / 4) {
                tc.pop_front();
            }
            for x in NUMS.iter().take(i / 2) {
                tc.push_front(x.clone());
            }
            for _ in NUMS.iter().take(i / 2) {
                tc.pop_back();
            }
        }));

        let ll = LinkedList::new();
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| b.iter(|| {
            let mut ll = ll.clone();
            for x in NUMS.iter().take(i / 2) {
                ll.push_back(x.clone());
            }
            for _ in NUMS.iter().take(i / 4) {
                ll.pop_front();
            }
            for x in NUMS.iter().take(i / 2) {
                ll.push_front(x.clone());
            }
            for _ in NUMS.iter().take(i / 2) {
                ll.pop_back();
            }
        }));
    }

    group.finish();
}

fn remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("remove()");

    for &i in SAMPLE.iter() {
        let tc = TsilCev::from(NUMS);
        let sp = i / 2;
        let rem_size = i / 4;
        group.bench_function(BenchmarkId::new("TsilCev", i), |b| b.iter(|| {
            let mut tc = tc.clone();
            let mut cursor = tc.cursor_idx_tsil_mut(sp);
            let mut cnt = 0;
            while let Some(_) = cursor.inner() {
                cursor.remove();
                cnt += 1;
                if cnt == rem_size {
                    break;
                }
            }
        }));

        let mut ll = LinkedList::new();
        for x in NUMS.iter().take(i) {
            ll.push_back(x.clone());
        }
        let sp = i / 2;
        let rem_size = i / 4;
        group.bench_function(BenchmarkId::new("LinkedList", i), |b| b.iter(|| {
            let mut ll = ll.clone();
            let mut cursor = ll.cursor_front_mut();
            for _ in 0..sp { cursor.move_next(); }
            for _ in 0..rem_size {
                cursor.remove_current();
            }
        }));
    }

    group.finish();
}

/*fn realoc_trigger_tsil_cev(c: &mut Criterion) {
    let mut tc = TsilCev::with_capacity(NUMS.len());
    for x in NUMS.iter() {
        tc.push_back(x.clone());
    }
    let delete_size = 3 * NUMS.len() / 4 - 1;
    c.bench_function("realoc trigger TsilCev", |b| b.iter(|| {
        let mut tc = tc.clone();
        let mut cursor = tc.cursor_front_mut();
        for _ in 0..delete_size {
            cursor.remove();
        }
    }));
}*/

fn iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator");

    for &i in SAMPLE.iter() {
        let mut tc = TsilCev::from(NUMS);
        group.bench_function(BenchmarkId::new("TsilCev.iter_tsil_mut()", i), |b| b.iter(|| {
            for x in tc.iter_tsil_mut() {
                x.add_one();
            }
        }));
        group.bench_function(BenchmarkId::new("TsilCev.iter_cev_mut()", i), |b| b.iter(|| {
            for x in tc.iter_cev_mut() {
                x.add_one();
            }
        }));

        let mut ll = LinkedList::new();
        for x in NUMS.iter().take(i) {
            ll.push_back(x.clone());
        }
        group.bench_function(BenchmarkId::new("LinkedList.iter_mut()", i), |b| b.iter(|| {
            for x in ll.iter_mut() {
                x.add_one();
            }
        }));
    }

    group.finish();
}

fn from(c: &mut Criterion) {
    c.bench_function("TsilCev::from(NUMS.clone())", |b| b.iter(|| {
        let _ = TsilCev::from(NUMS.clone());
    }));
}

criterion_group!(benches,
    // pop_front,
    // bench,
    // remove,
    // realoc_trigger_tsil_cev,
    from,
    // iter,
);
criterion_main!(benches);