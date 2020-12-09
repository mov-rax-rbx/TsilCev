#![no_std]

#[macro_use]
extern crate alloc;

use alloc::vec::Vec;
use core::hash::{Hash, Hasher};
use core::cmp::Ordering;
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
    impl Default for Index {
        #[inline]
        fn default() -> Self {
            Index::None
        }
    }
}

#[derive(Debug, Default, Clone)]
struct Val<T> {
    el: T,
    next: Index,
    prev: Index,
}

#[derive(Debug, Default, Clone)]
pub struct TsilCev<T> {
    cev: Vec<Val<T>>,
    start: Index,
    end: Index,
}

impl<T> TsilCev<T> {
    // Must be > 1 because cev must have 1 element
    const MIN_REALOC_LEN: usize = 8;

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            cev: Vec::with_capacity(cap),
            start: Index::None,
            end: Index::None,
        }
    }

    pub fn new() -> Self {
        Self {
            cev: Vec::new(),
            start: Index::None,
            end: Index::None,
        }
    }

    pub fn clear(&mut self) {
        self.cev.clear();
        self.start = Index::None;
        self.end = Index::None;
    }

    #[inline]
    fn start(&self) -> Index {
        debug_assert!(self.start.to_option().map_or(true, |x| x < self.cev.len()));
        self.start
    }
    #[inline]
    fn end(&self) -> Index {
        debug_assert!(self.end.to_option().map_or(true, |x| x < self.cev.len()));
        self.end
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
            pos: 0,
        }
    }
    #[inline]
    pub fn iter_cev_mut(&mut self) -> CevIterMut<T> {
        CevIterMut {
            tsil_cev: self,
            pos: 0,
        }
    }

    #[inline]
    pub fn drain_filter_tsil<F>(&mut self, pred: F) -> DrainFilterTsil<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.cev.len();
        DrainFilterTsil {
            cursor: self.cursor_front_mut(),
            pred: pred,
            old_len: len,
        }
    }

    #[inline]
    pub fn drain_filter_cev<F>(&mut self, pred: F) -> DrainFilterCev<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.cev.len();
        DrainFilterCev {
            tsil_cev: self,
            pos: 0,
            pred: pred,
            old_len: len,
        }
    }

    #[inline]
    pub fn front(&self) -> Option<&T> {
        // safe because check back not empty
        Some(unsafe { &self.cev.get_unchecked(self.start().to_option()?).el })
    }
    #[inline]
    pub fn back(&self) -> Option<&T> {
        // safe because check back not empty
        Some(unsafe { &self.cev.get_unchecked(self.end().to_option()?).el })
    }
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        let start = self.start().to_option()?;
        // safe because check back not empty
        Some(unsafe { &mut self.cev.get_unchecked_mut(start).el })
    }
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let end = self.end().to_option()?;
        // safe because check back not empty
        Some(unsafe { &mut self.cev.get_unchecked_mut(end).el })
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

    pub fn cursor_idx_tsil(&self, idx: usize) -> Cursor<'_, T> {
        if idx >= self.len() {
            Cursor {
                tsil_cev: self,
                idx: Index::None
            }
        }
        else if idx <= self.len() >> 1 {
            let mut cursor = self.cursor_front();
            cursor.move_next_length(idx);
            cursor
        } else {
            let new_len = self.len() - idx - 1;
            let mut cursor = self.cursor_back();
            cursor.move_prev_length(new_len);
            cursor
        }
    }
    pub fn cursor_idx_tsil_mut(&mut self, idx: usize) -> CursorMut<'_, T> {
        if idx >= self.len() {
            CursorMut {
                tsil_cev: self,
                idx: Index::None
            }
        }
        else if idx <= self.len() >> 1 {
            let mut cursor = self.cursor_front_mut();
            cursor.move_next_length(idx);
            cursor
        } else {
            let new_len = self.len() - idx - 1;
            let mut cursor = self.cursor_back_mut();
            cursor.move_prev_length(new_len);
            cursor
        }
    }

    pub fn to_vec(self) -> Vec<T> {
        // like
        // self.into_iter().map(move |x| x).collect::<Vec<_>>()

        // Faster then previous?
        let mut ret = Vec::with_capacity(self.cev.len());
        let mut cursor = self.start().to_option();
        while let Some(x) = cursor {
            // safe because cursor traversal in tsil_cev
            cursor = unsafe { self.cev.get_unchecked(x).next }.to_option();
            // safe because self move and drop in end
            let val = unsafe { core::ptr::read(self.cev.as_ptr().add(x)).el };
            ret.push(val);
        }
        ret
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.cev.capacity()
    }
    #[inline]
    pub fn len(&self) -> usize {
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

    pub fn push_back(&mut self, val: T) {
        unsafe { self.insert(self.end, Index::None, val) };
        /*let idx = self.cev.len();
        self.cev.push(Val {
            el: val,
            next: Index::None,
            prev: self.end,
        });
        if !self.end().is_none() {
            unsafe { self.cev.get_unchecked_mut(self.end.0).next = Index(idx) };
        }
        self.end = Index(idx);
        if self.start().is_none() {
            self.start = Index(idx);
        };*/
    }

    pub fn pop_back(&mut self) -> Option<T> {
        let end = self.end().to_option()?;
        // safe because value is never read until a new value is added
        Some(unsafe { self.make_empty(end) }.0)
    }

    pub fn push_front(&mut self, val: T) {
        unsafe { self.insert(Index::None, self.start, val) };
        /*let idx = self.cev.len();
        self.cev.push(Val {
            el: val,
            next: self.start,
            prev: Index::None,
        });
        if !self.start().is_none() {
            unsafe { self.cev.get_unchecked_mut(self.start.0).prev = Index(idx) };
        }
        self.start = Index(idx);
        if self.end().is_none() {
            self.end = Index(idx);
        }*/
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let start = self.start().to_option()?;
        // safe because value is never read until a new value is added
        Some(unsafe { self.make_empty(start) }.0)
    }

    #[inline]
    unsafe fn insert(&mut self, prev: Index, next: Index, val: T) {
        debug_assert!(
            prev.to_option().map_or(true, |x| x < self.cev.len())
            && next.to_option().map_or(true, |x| x < self.cev.len())
        );
        let current = self.cev.len();
        self.cev.push(Val {
            el: val,
            next: next,
            prev: prev,
        });
        self.reconnect(prev, next, Index(current));
    }

    #[inline]
    unsafe fn connect(&mut self, prev: Index, next: Index) {
        debug_assert!(
            prev.to_option().map_or(true, |x| x < self.cev.len())
            && next.to_option().map_or(true, |x| x < self.cev.len())
        );
        // safe because 0 <= x and y < cev.len
        match (prev.to_option(), next.to_option()) {
            (None, None) => {
                self.start = Index::None;
                self.end = Index::None;
            },
            (None, Some(y)) => {
                self.cev.get_unchecked_mut(y).prev = Index::None;
                self.start = Index(y);
            },
            (Some(x), None) => {
                self.cev.get_unchecked_mut(x).next = Index::None;
                self.end = Index(x);
            },
            (Some(x), Some(y)) => {
                self.cev.get_unchecked_mut(x).next = Index(y);
                self.cev.get_unchecked_mut(y).prev = Index(x);
            },
        };
    }

    #[inline]
    unsafe fn reconnect(&mut self, prev: Index, next: Index, current: Index) {
        debug_assert!(
            prev.to_option().map_or(true, |x| x < self.cev.len())
            && next.to_option().map_or(true, |x| x < self.cev.len())
            && current.to_option().map_or(false, |x| x < self.cev.len())
        );
        // safe because 0 <= x and y and z < cev.len
        match (prev.to_option(), current.to_option(), next.to_option()) {
            (None, Some(z), None) => {
                self.start = Index(z);
                self.end = Index(z);
            },
            (None, Some(z), Some(y)) => {
                self.cev.get_unchecked_mut(y).prev = Index(z);
                self.start = Index(z);
            },
            (Some(x), Some(z), None) => {
                self.cev.get_unchecked_mut(x).next = Index(z);
                self.end = Index(z);
            },
            (Some(x), Some(z), Some(y)) => {
                self.cev.get_unchecked_mut(x).next = Index(z);
                self.cev.get_unchecked_mut(y).prev = Index(z);
            },
            _ => unreachable!()
        };
    }

    #[inline]
    unsafe fn make_empty(&mut self, idx: usize) -> (T, Index) {
        debug_assert!(idx < self.cev.len() && self.len() > 0);

        let prev = self.cev.get_unchecked(idx).prev;
        let next = self.cev.get_unchecked(idx).next;
        self.connect(prev, next);
        if idx + 1 != self.cev.len() {
            self.swap_mem(idx, self.cev.len() - 1);
            let prev = self.cev.get_unchecked(idx).prev;
            let next = self.cev.get_unchecked(idx).next;
            self.reconnect(prev, next, Index(idx));
        }
        let ret = self.remove_last_mem().el;

        // safe because we know that index reorder and save index (save_idx)
        self.try_realoc();
        (ret, if next.0 == self.cev.len() { Index(idx) } else { next })
    }

    // unsafe because reorder index and this method don't use in EntryMut
    #[inline]
    unsafe fn try_realoc(&mut self) {
        let realoc_len = self.cev.capacity() >> 1;
        // density balance if density < cev.len() / 4 then realocate for less capacity
        if realoc_len > Self::MIN_REALOC_LEN
            && self.cev.len() <= realoc_len >> 1
        {
            // safe because self.density < realoc_len and 0 < realoc_len < cev.len
            self.realoc(realoc_len)
        }
    }

    #[inline]
    unsafe fn realoc(&mut self, realoc_len: usize) {
        debug_assert!(self.len() <= realoc_len);

        // safe because previous we do relax and all element
        // where index >= density is empty and in this empty
        // no reference
        let old_len = self.cev.len();
        self.cev.set_len(realoc_len);
        self.cev.shrink_to_fit(); //.shrink_to(realoc_len);
        self.cev.set_len(old_len);
    }

    #[inline]
    unsafe fn swap_mem(&mut self, x: usize, y: usize) {
        debug_assert!(x < self.cev.len() && y < self.cev.len());

        let x_val = self.cev.as_mut_ptr().add(x);
        let y_val = self.cev.as_mut_ptr().add(y);
        core::ptr::swap(x_val, y_val);
    }

    #[inline]
    unsafe fn remove_last_mem(&mut self) -> Val<T> {
        debug_assert!(self.cev.len() > 0);

        let last = self.cev.len() - 1;
        let last_val = self.cev.as_ptr().add(last);
        self.cev.set_len(last);
        core::ptr::read(last_val)
    }
}

impl<T: Clone> TsilCev<T> {
    pub fn from_slice(slice: &[T]) -> Self {
        if slice.len() == 0 {
            Self::new()
        } else if slice.len() == 1 {
            Self {
                cev: vec![Val {
                    el: unsafe { slice.get_unchecked(0).clone() },
                    next: Index::None,
                    prev: Index::None,
                }],
                start: Index(0),
                end: Index(0),
            }
        } else {
            let mut cev = Vec::with_capacity(slice.len());
            // safe because after init
            unsafe { cev.set_len(slice.len()) };
            let mut tsil_cev = Self {
                cev: cev,
                start: Index(0),
                end: Index(slice.len() - 1),
            };
            unsafe {
                // safe because slice.len() > 1
                *tsil_cev.cev.get_unchecked_mut(0) = Val {
                    el: slice.get_unchecked(0).clone(),
                    next: Index(1),
                    prev: Index::None,
                };

                // safe because slice.len() > 1 and tsil_cev.end >= 1
                *tsil_cev.cev.get_unchecked_mut(tsil_cev.end.0) = Val {
                    el: slice.get_unchecked(tsil_cev.end.0).clone(),
                    next: Index::None,
                    prev: Index(tsil_cev.end.0 - 1),
                };

                // safe because slice.len() > 1 and tsil_cev.end >= 1
                tsil_cev.cev.get_unchecked_mut(1..tsil_cev.end.0).iter_mut()
                    .zip(slice.get_unchecked(1..).iter().zip((1..).into_iter()))
                    .for_each(|(x, (val, current_idx))|
                        *x = Val {
                            el: val.clone(),
                            next: Index(current_idx + 1),
                            prev: Index(current_idx - 1),
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
        debug_assert!(self.idx.to_option().map_or(true, |x| x < self.tsil_cev.cev.len()));

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).el })
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
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next }
        }
        self
    }
    #[inline]
    pub fn move_prev(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev }
        }
        self
    }

    #[inline]
    pub fn move_next_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            len -= 1;
        }
        self
    }
    #[inline]
    pub fn move_prev_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            len -= 1;
        }
        self
    }

    #[inline]
    pub fn peek_next(&self) -> Option<&T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).next };
        // safe because next_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(next_idx.to_option()?).el })
    }
    #[inline]
    pub fn peek_prev(&self) -> Option<&T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).prev };
        // safe because prev_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(prev_idx.to_option()?).el })
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
            // safe because self.tsil_len < usize::MAX
            pos: self.idx.0,
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
        debug_assert!(self.idx.to_option().map_or(true, |x| x < self.tsil_cev.cev.len()));

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).el })
    }
    #[inline]
    pub fn inner_mut(&mut self) -> Option<&mut T> {
        debug_assert!(self.idx.to_option().map_or(true, |x| x < self.tsil_cev.cev.len()));

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &mut self.tsil_cev.cev.get_unchecked_mut(self.idx.to_option()?).el })
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
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next }
        }
        self
    }
    #[inline]
    pub fn move_prev(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev }
        }
        self
    }

    #[inline]
    pub fn move_next_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            len -= 1;
        }
        self
    }
    #[inline]
    pub fn move_prev_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len > 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            len -= 1;
        }
        self
    }

    #[inline]
    pub fn peek_next(&mut self) -> Option<&mut T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).next };
        // safe because next_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &mut self.tsil_cev.cev.get_unchecked_mut(next_idx.to_option()?).el })
    }
    #[inline]
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).prev };
        // safe because prev_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &mut self.tsil_cev.cev.get_unchecked_mut(prev_idx.to_option()?).el })
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
            // safe because self.tsil_len < usize::MAX
            pos: self.idx.0,
        }
    }
    #[inline]
    pub fn iter_cev_mut(&mut self) -> CevIterMut<T> {
        CevIterMut {
            tsil_cev: self.tsil_cev,
            // safe because self.tsil_len < usize::MAX
            pos: self.idx.0,
        }
    }

    pub fn insert_before(&mut self, val: T) -> &mut Self {
        if !self.idx.is_none() {
            let prev = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            unsafe { self.tsil_cev.insert(prev, self.idx, val) };
        } else {
            self.tsil_cev.push_back(val);
        }
        self
    }
    pub fn insert_after(&mut self, val: T) -> &mut Self {
        if !self.idx.is_none() {
            let next = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            unsafe { self.tsil_cev.insert(self.idx, next, val) };
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
    pub fn remove(&mut self) -> &mut Self {
        let _ = self.owned();
        self
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
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).next }.to_option();
        // safe 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(x).el })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.len(), Some(self.tsil_cev.len()))
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
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).next }.to_option();
        // safe because Rust can't deduce that we won't return multiple references to the same value
        // and 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &mut *(&mut self.tsil_cev.cev.get_unchecked_mut(x).el as *mut _) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.len(), Some(self.tsil_cev.len()))
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
        (self.tsil_cev.len(), Some(self.tsil_cev.len()))
    }
}

impl<'t, T: 't> DoubleEndedIterator for TsilIter<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t T> {
        let x = self.cursor?;
        // safe because cursor traversal in tsil_cev
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).prev }.to_option();
        // safe because Rust can't deduce that we won't return multiple references to the same value
        // and 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(x).el })
    }
}

impl<'t, T: 't> DoubleEndedIterator for TsilIterMut<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t mut T> {
        let x = self.cursor?;
        // safe because cursor traversal in tsil_cev
        self.cursor = unsafe { self.tsil_cev.cev.get_unchecked(x).prev }.to_option();
        // safe because Rust can't deduce that we won't return multiple references to the same value
        // and 0 <= x < self.tsil_cev.cev.len because we traversal on tsil_cev
        Some(unsafe { &mut *(&mut self.tsil_cev.cev.get_unchecked_mut(x).el as *mut _) })
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
impl<'t, T: 't> ExactSizeIterator for CevIter<'t, T> {}
impl<'t, T: 't> ExactSizeIterator for CevIterMut<'t, T> {}
impl<T> ExactSizeIterator for TsilIntoIter<T> {}

impl<'t, T: 't> core::iter::FusedIterator for TsilIter<'t, T> {}
impl<'t, T: 't> core::iter::FusedIterator for TsilIterMut<'t, T> {}
impl<'t, T: 't> core::iter::FusedIterator for CevIter<'t, T> {}
impl<'t, T: 't> core::iter::FusedIterator for CevIterMut<'t, T> {}
impl<T> core::iter::FusedIterator for TsilIntoIter<T> {}

pub struct CevIterMut<'t, T: 't> {
    tsil_cev: &'t mut TsilCev<T>,
    pos: usize,
}

#[derive(Clone)]
pub struct CevIter<'t, T: 't> {
    tsil_cev: &'t TsilCev<T>,
    pos: usize,
}

impl<'t, T: 't> Iterator for CevIter<'t, T> {
    type Item = &'t T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.tsil_cev.len() {
            let x = self.pos;
            self.pos += 1;
            // safe by previous check
            return Some(unsafe { &self.tsil_cev.cev.get_unchecked(x).el });
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.len(), Some(self.tsil_cev.len()))
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
        if self.pos < self.tsil_cev.len() {
            let x = self.pos;
            self.pos += 1;
            // safe because Rust can't deduce that we won't return multiple references to the same value
            // safe by previous check
            return Some(unsafe { &mut *(&mut self.tsil_cev.cev.get_unchecked_mut(x).el as *mut _) });
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.tsil_cev.len(), Some(self.tsil_cev.len()))
    }

    #[inline]
    fn last(self) -> Option<&'t mut T> {
        self.tsil_cev.back_mut()
    }
}

pub struct DrainFilterTsil<'t, T: 't, F: 't>
where
    F: FnMut(&mut T) -> bool,
{
    cursor: CursorMut<'t, T>,
    pred: F,
    old_len: usize,
}

impl<T, F> Iterator for DrainFilterTsil<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while let Some(x) = self.cursor.inner_mut() {
            if (self.pred)(x) {
                return self.cursor.owned();
            }
            self.cursor.move_next();
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.cursor.tsil_cev.len()))
    }
}

pub struct DrainFilterCev<'t, T: 't, F: 't>
where
    F: FnMut(&mut T) -> bool,
{
    tsil_cev: &'t mut TsilCev<T>,
    pos: usize,
    pred: F,
    old_len: usize,
}

impl<T, F> Iterator for DrainFilterCev<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while self.pos < self.tsil_cev.len() {
            let x = unsafe { &mut self.tsil_cev.cev.get_unchecked_mut(self.pos).el };
            if (self.pred)(x) {
                return Some(unsafe { self.tsil_cev.make_empty(self.pos) }.0);
            }
            self.pos += 1;
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.tsil_cev.len()))
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

impl<T: PartialEq> PartialEq for TsilCev<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter_tsil().eq(other)
    }
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl<T: Eq> Eq for TsilCev<T> {}

impl<T: PartialOrd> PartialOrd for TsilCev<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter_tsil().partial_cmp(other)
    }
}

impl<T: Ord> Ord for TsilCev<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter_tsil().cmp(other)
    }
}

// impl<T: Clone> Clone for TsilCev<T> {
//     fn clone(&self) -> Self {
//         Self {
//             cev: self.cev.clone(),
//             start: self.start,
//             end: self.end,
//         }
//     }
//     fn clone_from(&mut self, source: &Self) {
//         self.cev.clone_from(&source.cev);
//         self.start = source.start;
//         self.end = source.end;
//     }
// }

impl<T: Hash> Hash for TsilCev<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for elt in self {
            elt.hash(state);
        }
    }
}