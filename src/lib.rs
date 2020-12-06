#![feature(untagged_unions)]

use core::mem;
use core::fmt;
use core::hash::{Hash, Hasher};
use crate::index::Index;

pub(crate) mod index {
    #[derive(Debug, Copy, Clone)]
    #[repr(transparent)]
    pub(crate) struct Index(pub(crate) usize);

    impl Index {
        #[allow(non_upper_case_globals)]
        pub(crate) const None: Index = Index(usize::MAX);
        #[inline]
        pub(crate) fn is_none(self) -> bool {
            self.0 == Index::None.0
        }
        #[inline]
        pub(crate) fn to_option(self) -> Option<usize> {
            match self.0 {
                usize::MAX => None,
                idx => Some(idx),
            }
        }
    }
}

#[derive(Debug)]
struct Val<T> {
    el: mem::ManuallyDrop<T>,
    next: Index,
    prev: Index,
}

union TsilUnion<T> {
    val: Val<T>,
    next_empty: Index,
}

struct Tsil<T> {
    union: TsilUnion<T>,
    is_empty: bool,
}

impl<T: fmt::Debug> fmt::Debug for Tsil<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty {
            // safe because check self is empty
            f.debug_tuple("Empty")
                .field(unsafe { &self.union.next_empty })
                .finish()
        } else {
            // safe because check self is not empty
            f.debug_tuple("")
                .field(unsafe { &self.union.val })
                .finish()
        }
    }
}

impl<T> Default for Tsil<T> {
    #[inline]
    fn default() -> Self {
        Tsil {
            union: TsilUnion {
                next_empty: Index::None,
            },
            is_empty: true,
        }
    }
}

#[derive(Debug)]
pub struct TsilCev<T> {
    cev: Vec<Tsil<T>>,
    empty_idx: Index,
    start: usize,
    end: usize,
    density: usize,
}

impl<T> TsilCev<T> {
    // Must be > 1 because cev must have 1 element
    const MIN_REALOC_LEN: usize = 8;

    pub fn with_capacity(cap: usize) -> Self {
        let cap = if cap == 0 { 1 } else { cap };
        let mut cev = Vec::with_capacity(cap);
        cev.push(Tsil::default());
        Self {
            cev: cev,
            empty_idx: Index(0),
            start: 0,
            end: 0,
            density: 0,
        }
    }

    pub fn new() -> Self {
        Self {
            cev: vec![Tsil::default()],
            empty_idx: Index(0),
            start: 0,
            end: 0,
            density: 0,
        }
    }

    pub fn clear(&mut self) {
        self.cev.truncate(1);
        debug_assert!(self.cev.len() > 0);
        // safe because save first element
        unsafe {
            *self.cev.get_unchecked_mut(0) = Tsil {
                union: TsilUnion {
                    next_empty: Index::None,
                },
                is_empty: true,
           };
        }
        self.start = 0;
        self.end = 0;
        self.density = 0;
        self.empty_idx = Index(0);
    }

    #[inline]
    unsafe fn is_empty(&self, idx: usize) -> bool {
        debug_assert!(idx < self.cev.len());
        self.cev.get_unchecked(idx).is_empty
    }
    #[inline]
    fn start(&self) -> Index {
        debug_assert!(self.start < self.cev.len());
        // safe because always have 1 element
        if unsafe { self.is_empty(self.start) } { Index::None } else { Index(self.start) }
    }
    #[inline]
    fn end(&self) -> Index {
        debug_assert!(self.end < self.cev.len());
        // safe because always have 1 element
        if unsafe { self.is_empty(self.end) } { Index::None } else { Index(self.end) }
    }

    #[inline]
    pub fn iter_tsil(&self) -> TsilIter<T> {
        TsilIter {
            tsil_cev: self,
            cursor: self.start().to_option(),
        }
    }
    #[inline]
    pub fn iter_tsil_mut(&mut self) -> TsilIterMut<T> {
        let start = self.start().to_option();
        TsilIterMut {
            tsil_cev: self,
            cursor: start,
        }
    }

    #[inline]
    pub fn iter_cev(&self) -> CevIter<T> {
        CevIter {
            tsil_cev: self,
            cursor: Some(0),
        }
    }
    #[inline]
    pub fn iter_cev_mut(&mut self) -> CevIterMut<T> {
        CevIterMut {
            tsil_cev: self,
            cursor: Some(0),
        }
    }

    #[inline]
    pub fn front(&self) -> Option<&T> {
        // safe because check back not empty
        Some(unsafe { &*self.cev.get_unchecked(self.start().to_option()?).union.val.el })
    }
    #[inline]
    pub fn back(&self) -> Option<&T> {
        // safe because check back not empty
        Some(unsafe { &*self.cev.get_unchecked(self.end().to_option()?).union.val.el })
    }
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        let start = self.start().to_option()?;
        // safe because check back not empty
        Some(unsafe { &mut *self.cev.get_unchecked_mut(start).union.val.el })
    }
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let end = self.end().to_option()?;
        // safe because check back not empty
        Some(unsafe { &mut *self.cev.get_unchecked_mut(end).union.val.el })
    }

    #[inline]
    pub fn cursor_front(&self) -> Cursor<'_, T> {
        // safe because always have first element
        Cursor {
            tsil_cev: self,
            // safe because check back not empty
            idx: self.start(),
        }
    }
    #[inline]
    pub fn cursor_back(&self) -> Cursor<'_, T> {
        // safe because always have first element
        Cursor {
            tsil_cev: self,
            // safe because check back not empty
            idx: self.end(),
        }
    }
    #[inline]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        // safe because check back not empty
        let start = self.start();
        // safe because always have first element
        CursorMut {
            tsil_cev: self,
            idx: start
        }
    }
    #[inline]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        // safe because check back not empty
        let end = self.end();
        // safe because always have first element
        CursorMut {
            tsil_cev: self,
            idx: end
        }
    }

    pub fn cursor_idx(&self, idx: usize) -> Cursor<'_, T> {
        if idx >= self.density() {
            Cursor {
                tsil_cev: self,
                idx: Index::None
            }
        }
        else if idx <= self.density() >> 1 {
            let mut cursor = self.cursor_front();
            cursor.move_next_length(idx);
            cursor
        } else {
            let new_len = self.density() - idx - 1;
            let mut cursor = self.cursor_back();
            cursor.move_prev_length(new_len);
            cursor
        }
    }
    pub fn cursor_idx_mut(&mut self, idx: usize) -> CursorMut<'_, T> {
        if idx >= self.density() {
            CursorMut {
                tsil_cev: self,
                idx: Index::None
            }
        }
        else if idx <= self.density() >> 1 {
            let mut cursor = self.cursor_front_mut();
            cursor.move_next_length(idx);
            cursor
        } else {
            let new_len = self.density() - idx - 1;
            let mut cursor = self.cursor_back_mut();
            cursor.move_prev_length(new_len);
            cursor
        }
    }

    pub fn to_vec(mut self) -> Vec<T> {
        // like
        // self.into_iter().map(move |x| x).collect::<Vec<_>>()

        let mut ret = Vec::with_capacity(self.density);
        // safe because always have 1 element
        let mut cursor = self.start().to_option();
        while let Some(x) = cursor {
            // safe because cursor traversal in tsil_cev
            cursor = unsafe { self.cev.get_unchecked(x).union.val.next }.to_option();
            // safe because self move and drop and after mem::ManuallyDrop::take data in self never read
            ret.push(unsafe { mem::ManuallyDrop::take(&mut self.cev.get_unchecked_mut(x).union.val.el) });
        }
        ret
    }

    #[inline]
    pub fn density(&self) -> usize {
        self.density
    }
    #[inline]
    pub fn capacity(&self) -> usize {
        self.cev.capacity()
    }
    #[inline]
    pub fn cev_len(&self) -> usize {
        self.cev.len()
    }

    pub fn remove_if(&mut self, pred: impl Fn(&T) -> bool) {
        let mut cursor = self.cursor_front_mut();
        while let Some(x) = cursor.inner() {
            if pred(x) {
                cursor.remove();
            } else {
                cursor.move_next();
            }
        }
    }

    #[inline]
    fn create_empty_index(&mut self) -> usize {
        match self.empty_idx.to_option() {
            Some(idx) => {
                // safe because 0 <= empty_idx < cev.len and next_empty is Option<usize>
                self.empty_idx = unsafe { self.cev.get_unchecked(idx).union.next_empty };
                idx
            },
            None => {
                let idx = self.cev.len();
                self.cev.push(Tsil::default());
                idx
            }
        }
    }

    pub fn push_back(&mut self, val: T) {
        let idx = self.create_empty_index();
        unsafe { self.insert_back(idx, val) };
    }

    pub fn pop_back(&mut self) -> Option<T> {
        // safe because self.end index in cev and cev.size > 0
        let end_is_empty = self.end().is_none();
        if end_is_empty {
            None
        } else {
            // safe because value is never read until a new value is added
            Some(unsafe { self.make_empty(self.end) }.0)
        }
    }

    pub fn push_front(&mut self, val: T) {
        let idx = self.create_empty_index();
        unsafe { self.insert_front(idx, val) };
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let start = self.start().to_option()?;
        // safe because value is never read until a new value is added
        Some(unsafe { self.make_empty(start) }.0)
    }

    #[inline]
    unsafe fn insert_back(&mut self, idx: usize, val: T) {
        debug_assert!(idx < self.cev.len());

        // safe because self.end index in cev and cev.size > 0
        let end_is_empty = self.end().is_none();
        *self.cev.get_unchecked_mut(idx) = Tsil {
            union: TsilUnion {
                val: Val {
                    el: mem::ManuallyDrop::new(val),
                    next: Index::None,
                    prev: if !end_is_empty { Index(self.end) } else { Index::None },
                }
            },
            is_empty: false
        };
        // safe because self.end index in cev and cev.size > 0
        if !end_is_empty {
            self.cev.get_unchecked_mut(self.end).union.val.next = Index(idx);
        }
        self.end = idx;
        self.density += 1;
    }

    #[inline]
    unsafe fn insert_front(&mut self, idx: usize, val: T) {
        debug_assert!(idx < self.cev.len());

        // safe because self.start index in cev and cev.size > 0
        let start_is_empty = self.start().is_none();
        *self.cev.get_unchecked_mut(idx) = Tsil {
            union: TsilUnion {
                val: Val {
                    el: mem::ManuallyDrop::new(val),
                    next: if !start_is_empty { Index(self.start) } else { Index::None },
                    prev: Index::None,
                }
            },
            is_empty: false
        };
        // safe because self.start index in cev and cev.size > 0
        if !start_is_empty {
            self.cev.get_unchecked_mut(self.start).union.val.prev = Index(idx);
        }
        self.start = idx;
        self.density += 1;
    }

    #[inline]
    unsafe fn insert(&mut self, prev: Index, next: Index, current: Index, val: T) {
        debug_assert!(
            if !prev.is_none() { !self.is_empty(prev.0) } else { true }
            && if !next.is_none() { !self.is_empty(next.0) } else { true }
            && !current.is_none() && self.is_empty(current.0)
        );

        // safe because 0 <= currend < cev.len
        *self.cev.get_unchecked_mut(current.0) = Tsil {
            union: TsilUnion {
                val: Val {
                    el: mem::ManuallyDrop::new(val),
                    next: next,
                    prev: prev,
                }
            },
            is_empty: false
        };
        self.reconnect(prev, next, current);
        self.density += 1;
    }

    #[inline]
    unsafe fn connect(&mut self, prev: Index, next: Index) {
        debug_assert!(
            if !prev.is_none() { !self.is_empty(prev.0) } else { true }
            && if !next.is_none() { !self.is_empty(next.0) } else { true }
        );

        // safe because 0 <= x and y < cev.len
        match (prev.to_option(), next.to_option()) {
            (None, None) => {},
            (None, Some(y)) => {
                self.cev.get_unchecked_mut(y).union.val.prev = Index::None;
                self.start = y;
            },
            (Some(x), None) => {
                self.cev.get_unchecked_mut(x).union.val.next = Index::None;
                self.end = x;
            },
            (Some(x), Some(y)) => {
                self.cev.get_unchecked_mut(x).union.val.next = Index(y);
                self.cev.get_unchecked_mut(y).union.val.prev = Index(x);
            },
        };
    }

    #[inline]
    unsafe fn reconnect(&mut self, prev: Index, next: Index, current: Index) {
        debug_assert!(
            if !prev.is_none() { !self.is_empty(prev.0) } else { true }
            && if !next.is_none() { !self.is_empty(next.0) } else { true }
            && !current.is_none()
        );
        
        // safe because 0 <= x and y and z < cev.len
        match (prev.to_option(), current.to_option(), next.to_option()) {
            (None, Some(_), None) => {},
            (None, Some(z), Some(y)) => {
                self.cev.get_unchecked_mut(y).union.val.prev = Index(z);
                self.start = z;
            },
            (Some(x), Some(z), None) => {
                self.cev.get_unchecked_mut(x).union.val.next = Index(z);
                self.end = z;
            },
            (Some(x), Some(z), Some(y)) => {
                self.cev.get_unchecked_mut(x).union.val.next = Index(z);
                self.cev.get_unchecked_mut(y).union.val.prev = Index(z);
            },
            _ => unreachable!()
        };
    }

    #[inline]
    unsafe fn make_empty(&mut self, idx: usize) -> (T, Index) {
        debug_assert!(idx < self.cev.len() && !self.is_empty(idx) && self.density() > 0);

        // safe if !self.is_empty(idx) and after safe because value is mark is_empty
        // and never read until a new value is added
        let ret = mem::ManuallyDrop::take(
            &mut self.cev.get_unchecked_mut(idx).union.val.el
        );

        let prev = self.cev.get_unchecked(idx).union.val.prev;
        let next = self.cev.get_unchecked(idx).union.val.next;
        self.connect(prev, next);
        *self.cev.get_unchecked_mut(idx) = Tsil {
            union: TsilUnion {
                next_empty: self.empty_idx,
            },
            is_empty: true,
        };
        self.empty_idx = Index(idx);
        self.density -= 1;

        // safe because we know that index reorder and save index (save_idx)
        (ret, self.try_realoc(next))
    }

    // unsafe because reorder index and this method don't use in EntryMut
    #[inline]
    unsafe fn try_realoc(&mut self, save_idx: Index) -> Index {
        let realoc_len = self.cev.capacity() >> 1;
        // density balance if dencity < cev.len() / 4 then realocate for less capacity
        if realoc_len > Self::MIN_REALOC_LEN
            && self.cev.len() >= realoc_len
            && self.density <= realoc_len >> 1
        {
            // safe because self.density < realoc_len and 0 < realoc_len < cev.len
            self.realoc(realoc_len, save_idx)
        } else {
            save_idx
        }
    }

    #[inline]
    unsafe fn realoc(&mut self, realoc_len: usize, save_idx: Index) -> Index {
        debug_assert!(self.density < realoc_len);

        let save_idx = self.relax(save_idx);
        self.reconnect_empty_chain(self.density, realoc_len);

        // safe because previous we do relax and all element
        // where index >= density is empty and in this empty
        // no reference
        self.cev.set_len(realoc_len);
        self.cev.shrink_to_fit(); //.shrink_to(realoc_len);
        save_idx
    }

    #[inline]
    fn relax(&mut self, mut save_idx: Index) -> Index {
        let mut left = 0;
        // self.cev.len > 0 always
        debug_assert!(self.cev.len() > 0);
        let mut right = self.cev.len() - 1;

        loop {
            while left < right && unsafe { !self.is_empty(left) } {
                left += 1;
            }
            while left < right && unsafe { self.is_empty(right) } {
                right -= 1;
            }
            if left < right && unsafe { self.is_empty(left) && !self.is_empty(right) } {
                // safe because left is empty index and 0 <= left and right < cev.len
                unsafe { self.swap_empty_mem(left, right) };
                // valid because Index(right) != Index::None
                if right == save_idx.0 { save_idx = Index(left) }
                left += 1;
                right -= 1;
            } else {
                return save_idx;
            }
        }
    }

    #[inline]
    unsafe fn swap_empty_mem(&mut self, empty_idx: usize, idx: usize) {
        debug_assert!(
            idx < self.cev.len()
            && empty_idx < self.cev.len()
            && self.is_empty(empty_idx)
            && !self.is_empty(idx)
        );

        let idx_val = mem::take(self.cev.get_unchecked_mut(idx));
        let empty_val = mem::take(self.cev.get_unchecked_mut(empty_idx));
        *self.cev.get_unchecked_mut(empty_idx) = idx_val;
        *self.cev.get_unchecked_mut(idx) = empty_val;

        let prev = self.cev.get_unchecked(empty_idx).union.val.prev;
        let next = self.cev.get_unchecked(empty_idx).union.val.next;
        self.reconnect(prev, next, Index(empty_idx));
    }

    #[inline]
    unsafe fn reconnect_empty_chain(&mut self, start_idx: usize, end: usize) {
        debug_assert!(
            start_idx < end
            && start_idx < self.cev.len()
            && end <= self.cev.len()
        );

        for (this, next) in (start_idx..end).zip((start_idx + 1..end).into_iter()) {
            debug_assert!(self.is_empty(this));
            self.cev.get_unchecked_mut(this).union.next_empty = Index(next);
        }
        self.empty_idx = Index(start_idx);
        self.cev.get_unchecked_mut(end - 1).union.next_empty = Index::None;
    }
}

impl<T: Clone> TsilCev<T> {
    pub fn from_slice(slice: &[T]) -> Self {
        if slice.len() == 0 {
            Self::new()
        } else if slice.len() == 1 {
            Self {
                cev: vec![
                    Tsil {
                        union: TsilUnion {
                            val: Val {
                                el: mem::ManuallyDrop::new(unsafe { slice.get_unchecked(0).clone() }),
                                next: Index::None,
                                prev: Index::None,
                            }
                        },
                        is_empty: false,
                    },
                ],
                empty_idx: Index::None,
                start: 0,
                end: 0,
                density: 1,
            }
        } else {
            let mut cev = Vec::with_capacity(slice.len());
            // safe because after init
            unsafe { cev.set_len(slice.len()) };
            let mut tsil_cev = Self {
                cev: cev,
                empty_idx: Index::None,
                start: 0,
                end: slice.len() - 1,
                density: slice.len(),
            };
            unsafe {
                // safe because slice.len() > 1
                *tsil_cev.cev.get_unchecked_mut(0) = Tsil {
                    union: TsilUnion {
                        val: Val {
                            el: mem::ManuallyDrop::new(slice.get_unchecked(0).clone()),
                            next: Index(1),
                            prev: Index::None,
                        },
                    },
                    is_empty: false,
                };

                // safe because slice.len() > 1 and tsil_cev.end >= 1
                *tsil_cev.cev.get_unchecked_mut(tsil_cev.end) = Tsil {
                    union: TsilUnion {
                        val: Val {
                            el: mem::ManuallyDrop::new(slice.get_unchecked(tsil_cev.end).clone()),
                            next: Index::None,
                            prev: Index(tsil_cev.end - 1),
                        },
                    },
                    is_empty: false,
                };

                // safe because slice.len() > 1 and tsil_cev.end >= 1
                tsil_cev.cev.get_unchecked_mut(1..tsil_cev.end).iter_mut()
                    .zip(slice.get_unchecked(1..).iter().zip((1..).into_iter()))
                    .for_each(|(x, (val, current_idx))|
                        *x = Tsil {
                            union: TsilUnion {
                                val: Val {
                                    el: mem::ManuallyDrop::new(val.clone()),
                                    next: Index(current_idx + 1),
                                    prev: Index(current_idx - 1),
                                },
                            },
                            is_empty: false,
                        }
                    );
            }
            tsil_cev
        }
    }
}

pub struct Cursor<'t, T: 't> {
    tsil_cev: &'t TsilCev<T>,
    idx: Index,
}

impl<'t, T: 't> Cursor<'t, T> {
    #[inline]
    pub fn inner(&self) -> Option<&T> {
        debug_assert!(
            if !self.idx.is_none() {
                self.idx.0 < self.tsil_cev.cev.len() && unsafe { !self.tsil_cev.is_empty(self.idx.0) }
            } else { true }
        );

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &*self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).union.val.el })
    }

    #[inline]
    pub fn to_start(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.start();
        self
    }
    #[inline]
    pub fn to_end(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.end();
        self
    }

    #[inline]
    pub fn move_next(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.next }
        }
        self
    }
    #[inline]
    pub fn move_prev(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.prev }
        }
        self
    }

    #[inline]
    pub fn move_next_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.next };
            len -= 1;
        }
        self
    }
    #[inline]
    pub fn move_prev_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.prev };
            len -= 1;
        }
        self
    }

    #[inline]
    pub fn peek_next(&self) -> Option<&T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).union.val.next };
        // safe because next_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &*self.tsil_cev.cev.get_unchecked(next_idx.to_option()?).union.val.el })
    }
    #[inline]
    pub fn peek_prev(&self) -> Option<&T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).union.val.prev };
        // safe because prev_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &*self.tsil_cev.cev.get_unchecked(prev_idx.to_option()?).union.val.el })
    }

    #[inline]
    pub fn finish(&mut self) -> Self {
        Self {
            tsil_cev: &self.tsil_cev,
            idx: self.idx,
        }
    }

    #[inline]
    pub fn iter_tsil(&self) -> TsilIter<T> {
        TsilIter {
            tsil_cev: self.tsil_cev,
            cursor: self.idx.to_option(),
        }
    }
    #[inline]
    pub fn iter_cev(&self) -> CevIter<T> {
        CevIter {
            tsil_cev: self.tsil_cev,
            cursor: self.idx.to_option(),
        }
    }
}

pub struct CursorMut<'t, T: 't> {
    tsil_cev: &'t mut TsilCev<T>,
    idx: Index,
}

impl<'t, T: 't> CursorMut<'t, T> {
    #[inline]
    pub fn inner(&self) -> Option<&T> {
        debug_assert!(
            if !self.idx.is_none() {
                self.idx.0 < self.tsil_cev.cev.len() && unsafe { !self.tsil_cev.is_empty(self.idx.0) }
            } else { true }
        );

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &*self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).union.val.el })
    }
    #[inline]
    pub fn inner_mut(&mut self) -> Option<&mut T> {
        debug_assert!(
            if !self.idx.is_none() {
                self.idx.0 < self.tsil_cev.cev.len() && unsafe { !self.tsil_cev.is_empty(self.idx.0) }
            } else { true }
        );

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &mut *self.tsil_cev.cev.get_unchecked_mut(self.idx.to_option()?).union.val.el })
    }

    #[inline]
    pub fn to_start(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.start();
        self
    }
    #[inline]
    pub fn to_end(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.end();
        self
    }

    #[inline]
    pub fn move_next(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.next }
        }
        self
    }
    #[inline]
    pub fn move_prev(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.prev }
        }
        self
    }

    #[inline]
    pub fn move_next_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.next };
            len -= 1;
        }
        self
    }
    #[inline]
    pub fn move_prev_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.prev };
            len -= 1;
        }
        self
    }

    #[inline]
    pub fn peek_next(&mut self) -> Option<&mut T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).union.val.next };
        // safe because next_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &mut *self.tsil_cev.cev.get_unchecked_mut(next_idx.to_option()?).union.val.el })
    }
    #[inline]
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).union.val.prev };
        // safe because prev_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &mut *self.tsil_cev.cev.get_unchecked_mut(prev_idx.to_option()?).union.val.el })
    }

    #[inline]
    pub fn finish(&mut self) -> Self {
        Self {
            // safe because Rust can't deduce that we won't return multiple references to the same value
            tsil_cev: unsafe { &mut *(self.tsil_cev as *mut _) },
            idx: self.idx,
        }
    }

    #[inline]
    pub fn to_cursor(self) -> Cursor<'t, T> {
        Cursor {
            tsil_cev: self.tsil_cev,
            idx: self.idx,
        }
    }

    #[inline]
    pub fn iter_tsil(&self) -> TsilIter<T> {
        TsilIter {
            tsil_cev: self.tsil_cev,
            cursor: self.idx.to_option(),
        }
    }
    #[inline]
    pub fn iter_tsil_mut(&mut self) -> TsilIterMut<T> {
        TsilIterMut {
            tsil_cev: self.tsil_cev,
            cursor: self.idx.to_option(),
        }
    }

    #[inline]
    pub fn iter_cev(&self) -> CevIter<T> {
        CevIter {
            tsil_cev: self.tsil_cev,
            cursor: self.idx.to_option(),
        }
    }
    #[inline]
    pub fn iter_cev_mut(&mut self) -> CevIterMut<T> {
        CevIterMut {
            tsil_cev: self.tsil_cev,
            cursor: self.idx.to_option(),
        }
    }

    pub fn insert_before(&mut self, val: T) -> &mut Self {
        if !self.idx.is_none() {
            let idx = self.tsil_cev.create_empty_index();
            let prev = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.prev };
            unsafe { self.tsil_cev.insert(prev, self.idx, Index(idx), val) };
        } else {
            self.tsil_cev.push_back(val);
        }
        self
    }
    pub fn insert_after(&mut self, val: T) -> &mut Self {
        if !self.idx.is_none() {
            let idx = self.tsil_cev.create_empty_index();
            let next = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).union.val.next };
            unsafe { self.tsil_cev.insert(self.idx, next, Index(idx), val) };
        } else {
            self.tsil_cev.push_front(val);
        }
        self
    }

    pub fn owned(&mut self) -> Option<T> {
        if !self.idx.is_none() {
            // safe because after we do self.make_empty() and
            // value is never read until a new value is added
            let (ret, next_idx) = unsafe { self.tsil_cev.make_empty(self.idx.0) };
            self.idx = next_idx;
            Some(ret)
        } else {
            None
        }
    }

    #[inline]
    pub fn remove(&mut self) {
        let _ = self.owned();
    }
}

pub struct TsilIterMut<'t, T: 't> {
    tsil_cev: &'t mut TsilCev<T>,
    cursor: Option<usize>,
}

#[derive(Clone)]
pub struct TsilIter<'t, T: 't> {
    tsil_cev: &'t TsilCev<T>,
    cursor: Option<usize>,
}

#[derive(Clone)]
pub struct TsilIntoIter<T> {
    tsil_cev: TsilCev<T>
}

impl<'t, T: 't> Iterator for TsilIter<'t, T> {
    type Item = &'t T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let x = self.cursor?;
        // safe because cursor traversal in tsil_cev
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).union.val.next }.to_option();
        // safe 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &*self.tsil_cev.cev.get_unchecked(x).union.val.el })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.density(), Some(self.tsil_cev.density()))
    }

    #[inline]
    fn last(self) -> Option<&'t T> {
        self.tsil_cev.back()
    }
}

impl<'t, T: 't> Iterator for TsilIterMut<'t, T> {
    type Item = &'t mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let x = self.cursor?;
        // safe because cursor traversal in tsil_cev
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).union.val.next }.to_option();
        // safe because Rust can't deduce that we won't return multiple references to the same value
        // and 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &mut *(&mut *self.tsil_cev.cev.get_unchecked_mut(x).union.val.el as *mut _) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.density(), Some(self.tsil_cev.density()))
    }

    #[inline]
    fn last(self) -> Option<&'t mut T> {
        self.tsil_cev.back_mut()
    }
}

impl<T> Iterator for TsilIntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.tsil_cev.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.density(), Some(self.tsil_cev.density()))
    }
}

impl<'t, T: 't> DoubleEndedIterator for TsilIter<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t T> {
        let x = self.cursor?;
        // safe because cursor traversal in tsil_cev
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).union.val.prev }.to_option();
        // safe because Rust can't deduce that we won't return multiple references to the same value
        // and 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &*self.tsil_cev.cev.get_unchecked(x).union.val.el })
    }
}

impl<'t, T: 't> DoubleEndedIterator for TsilIterMut<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t mut T> {
        let x = self.cursor?;
        // safe because cursor traversal in tsil_cev
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).union.val.prev }.to_option();
        // safe because Rust can't deduce that we won't return multiple references to the same value
        // and 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &mut *(&mut *self.tsil_cev.cev.get_unchecked_mut(x).union.val.el as *mut _) })
    }
}

impl<T> DoubleEndedIterator for TsilIntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.tsil_cev.pop_back()
    }
}

impl<'t, T: 't> ExactSizeIterator for TsilIter<'t, T> {}
impl<'t, T: 't> ExactSizeIterator for TsilIterMut<'t, T> {}
impl<T> ExactSizeIterator for TsilIntoIter<T> {}

impl<'t, T: 't> ExactSizeIterator for CevIter<'t, T> {}
impl<'t, T: 't> ExactSizeIterator for CevIterMut<'t, T> {}

impl<'t, T: 't> std::iter::FusedIterator for TsilIter<'t, T> {}
impl<'t, T: 't> std::iter::FusedIterator for TsilIterMut<'t, T> {}
impl<T> std::iter::FusedIterator for TsilIntoIter<T> {}

impl<'t, T: 't> std::iter::FusedIterator for CevIter<'t, T> {}
impl<'t, T: 't> std::iter::FusedIterator for CevIterMut<'t, T> {}

pub struct CevIterMut<'t, T: 't> {
    tsil_cev: &'t mut TsilCev<T>,
    cursor: Option<usize>,
}

#[derive(Clone)]
pub struct CevIter<'t, T: 't> {
    tsil_cev: &'t TsilCev<T>,
    cursor: Option<usize>,
}

impl<'t, T: 't> Iterator for CevIter<'t, T> {
    type Item = &'t T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let x = self.cursor?;
            // safe because 0 <= cursor < tsil_cev.cev.len()
            self.cursor = if x + 1 == self.tsil_cev.cev.len() { None } else { Some(x + 1) };
            // safe by previous check
            if unsafe { !self.tsil_cev.is_empty(x) } {
                return Some(unsafe { &*self.tsil_cev.cev.get_unchecked(x).union.val.el });
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.density(), Some(self.tsil_cev.density()))
    }

    #[inline]
    fn last(self) -> Option<&'t T> {
        self.tsil_cev.back()
    }
}

impl<'t, T: 't> Iterator for CevIterMut<'t, T> {
    type Item = &'t mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let x = self.cursor?;
            // safe because 0 <= cursor < tsil_cev.cev.len()
            self.cursor = if x + 1 == self.tsil_cev.cev.len() { None } else { Some(x + 1) };
            // safe because Rust can't deduce that we won't return multiple references to the same value
            // safe by previous check
            if unsafe { !self.tsil_cev.is_empty(x) } {
                return Some(unsafe { &mut *(&mut *self.tsil_cev.cev.get_unchecked_mut(x).union.val.el as *mut _) });
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.density(), Some(self.tsil_cev.density()))
    }

    #[inline]
    fn last(self) -> Option<&'t mut T> {
        self.tsil_cev.back_mut()
    }
}

impl<T> IntoIterator for TsilCev<T> {
    type Item = T;
    type IntoIter = TsilIntoIter<T>;

    #[inline]
    fn into_iter(self) -> TsilIntoIter<T> {
        TsilIntoIter { tsil_cev: self }
    }
}

impl<'t, T> IntoIterator for &'t TsilCev<T> {
    type Item = &'t T;
    type IntoIter = TsilIter<'t, T>;

    #[inline]
    fn into_iter(self) -> TsilIter<'t, T> {
        self.iter_tsil()
    }
}

impl<'t, T> IntoIterator for &'t mut TsilCev<T> {
    type Item = &'t mut T;
    type IntoIter = TsilIterMut<'t, T>;

    #[inline]
    fn into_iter(self) -> TsilIterMut<'t, T> {
        self.iter_tsil_mut()
    }
}

impl<T> Extend<T> for TsilCev<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |x| self.push_back(x));
    }
}

impl<'t, T: 't + Copy> Extend<&'t T> for TsilCev<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'t T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

impl<T> Drop for Tsil<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() && !self.is_empty {
            // safe because check self not empty
            unsafe {
                mem::ManuallyDrop::drop(&mut self.union.val.el);
            }
        }
    }
}

impl<T: Clone> Clone for Val<T> {
    fn clone(&self) -> Self {
        Self {
            el: self.el.clone(),
            next: self.next,
            prev: self.prev,
        }
    }
}

impl<T: Clone> Clone for Tsil<T> {
    fn clone(&self) -> Self {
        // safe because check is empty or not
        if self.is_empty {
            Self {
                union: TsilUnion {
                    next_empty: unsafe { self.union.next_empty }
                },
                is_empty: true,
            }
        } else {
            Self {
                union: TsilUnion {
                    val: unsafe { self.union.val.clone() }
                },
                is_empty: false,
            }
        }
    }
}

impl<T: Clone> Clone for TsilCev<T> {
    fn clone(&self) -> Self {
        Self {
            cev: self.cev.clone(),
            empty_idx: self.empty_idx,
            start: self.start,
            end: self.end,
            density: self.density,
        }
    }
    fn clone_from(&mut self, source: &Self) {
        self.cev.clone_from(&source.cev);
        self.empty_idx = source.empty_idx;
        self.start = source.start;
        self.end = source.end;
        self.density = source.density;
    }
}

impl<T: Hash> Hash for TsilCev<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.density().hash(state);
        for elt in self {
            elt.hash(state);
        }
    }
}