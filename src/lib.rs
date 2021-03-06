//! Implementation of the linked list on `Vec`. Has an
//! `O(1)` amortized insertion and removal time due to
//! linear placement in memory. It is added in the
//! same way as in `Vec`, but at deletion the element
//! moves to the end and something like pop is called.

//! # `tsil` and `cev`
//! `TsilCev` has 2 types of iterators `Tsil` and `Cev`.
//! `Tsil` - iterating as in `LinkedList`. `Cev` - iterating
//! as in `Vec` (a bit faster because memory access is sequential).

//! # Examples
//! ```
//! use tsil_cev::TsilCev;
//!
//! let mut tc = TsilCev::from(vec![5, 6, 7, 8, 9, 10]);
//! tc.push_front(4);
//!
//! let mut cursor = tc.cursor_front_mut();
//! assert_eq!(cursor.current(), Some(&4));
//!
//! cursor.move_next();
//! assert_eq!(cursor.current(), Some(&5));
//!
//! cursor.remove();
//! assert_eq!(cursor.current(), Some(&6));
//!
//! cursor.remove().remove().move_next_length(2);
//! assert_eq!(cursor.current(), Some(&10));
//!
//! cursor.move_prev();
//! assert_eq!(cursor.current(), Some(&9));
//!
//! tc.drain_filter_tsil(|x| *x % 2 == 0);
//! assert_eq!(tc.into_vec(), &[9]);
//! ```

//! # Current Implementation
//! The allocator for the elements is `Vec` and each
//! element has two indexes (next and previous element).
//! When delete an item, it moves to the end, and something
//! like pop is called.

//! ## Optional features
//!
//! ### `serde`
//!
//! When this optional dependency is enabled, `TsilCev` implements the
//! `serde::Serialize` and `serde::Deserialize` traits.

#![no_std]

extern crate alloc;

#[cfg(feature = "serde")]
mod serde;

use crate::index::Index;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::{FromIterator, FusedIterator};
use core::ptr::{read, swap};
use core::slice::{Iter, IterMut};

// It should be Option<usize>, but in order to save
// memory and avoid the NULL problem, a separate
// Index type has been created which should make
// indexes more reliable
pub(crate) mod index {
    #[derive(Debug, Copy, Clone)]
    #[repr(transparent)]
    // Like NonZeroUsize but NonMaxUsize
    pub(crate) struct Index(pub(crate) usize);

    impl Index {
        #[allow(non_upper_case_globals)]
        // Safe None value if the size of array inside the
        // TsilCev will never be larger than usize::MAX.
        // But theoretical array inside TsilCev equal
        // usize::MAX if 0 <= size_of::<T>() <= 1, but T
        // inside is 2 * size_of::<usize>() + size_of::<InnerType>()
        //           (next_idx) + (prev_idx) + (InnerType) > 1
        // So Index for TsilCev safe.
        pub(crate) const None: Index = Index(usize::MAX);
        #[inline]
        pub(crate) const fn is_none(self) -> bool {
            self.to_option().is_none()
        }
        #[inline]
        pub(crate) const fn to_option(self) -> Option<usize> {
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
    /// Constructs a new, empty `TsilCev` with the specified capacity
    /// like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::<()>::with_capacity(4);
    /// assert_eq!(tc.len(), 0);
    /// assert_eq!(tc.capacity(), 4);
    /// ```
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            cev: Vec::with_capacity(cap),
            start: Index::None,
            end: Index::None,
        }
    }

    /// Constructs a new, empty `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// assert_eq!(tc.len(), 0);
    /// assert_eq!(tc.capacity(), 0);
    ///
    /// tc.push_back(5);
    /// assert_eq!(tc.len(), 1);
    /// assert!(tc.capacity() >= 1);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            cev: Vec::new(),
            start: Index::None,
            end: Index::None,
        }
    }

    /// Deletes all values from `TsilCev` like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3]);
    /// assert_eq!(tc.len(), 4);
    /// assert!(tc.capacity() >= 4);
    ///
    /// tc.clear();
    /// assert_eq!(tc.len(), 0);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.cev.clear();
        self.start = Index::None;
        self.end = Index::None;
    }

    #[inline]
    fn start(&self) -> Index {
        debug_assert!(self.start.to_option().map_or(true, |x| x < self.len()));
        self.start
    }
    #[inline]
    fn end(&self) -> Index {
        debug_assert!(self.end.to_option().map_or(true, |x| x < self.len()));
        self.end
    }

    /// Returns `Tsil` iterator. Iterating as in `LinkedList`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(10);
    /// tc.push_front(0);
    /// let mut cev_iter = tc.iter_tsil();
    ///
    /// assert_eq!(cev_iter.next(), Some(&0));
    /// assert_eq!(cev_iter.next(), Some(&10));
    /// assert_eq!(cev_iter.next(), None);
    /// ```
    #[inline]
    pub fn iter_tsil(&self) -> TsilIter<T> {
        TsilIter {
            start_cursor: self.cursor_front(),
            end_cursor: self.cursor_back(),
            feature_len: self.len(),
        }
    }

    /// Returns `Tsil` iterator. Iterating as in `LinkedList` that allows
    /// modifying each value.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(10);
    /// tc.push_front(0);
    /// for x in tc.iter_tsil_mut() {
    ///     *x *= 20;
    /// }
    ///
    /// assert_eq!(tc.into_vec(), &[0, 200]);
    /// ```
    #[inline]
    pub fn iter_tsil_mut(&mut self) -> TsilIterMut<T> {
        let len = self.len();
        TsilIterMut {
            // safe because start_cursor and end_cursor no overlap
            // and contains array index (if array realocate)
            // and rust borrow checker will not allow the iterator
            // to be used if an element (for example, the last element)
            // has been deleted
            start_cursor: unsafe { (&mut *(self as *mut TsilCev<T>)).cursor_front_mut() },
            end_cursor: self.cursor_back_mut(),
            feature_len: len,
        }
    }

    /// Returns `Cev` iterator. Iterating as in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(10);
    /// tc.push_front(0);
    /// let mut cev_iter = tc.iter_cev();
    ///
    /// assert_eq!(cev_iter.next(), Some(&10));
    /// assert_eq!(cev_iter.next(), Some(&0));
    /// assert_eq!(cev_iter.next(), None);
    /// ```
    #[inline]
    pub fn iter_cev(&self) -> CevIter<T> {
        CevIter {
            iter: self.cev.iter(),
        }
    }

    /// Returns `Cev` iterator. Iterating as in Vec that allows modifying
    /// each value.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(10);
    /// tc.push_front(0);
    /// for x in tc.iter_cev_mut() {
    ///     *x *= 20;
    /// }
    ///
    /// assert_eq!(tc.into_vec(), &[0, 200]);
    /// ```
    #[inline]
    pub fn iter_cev_mut(&mut self) -> CevIterMut<T> {
        CevIterMut {
            iter: self.cev.iter_mut(),
        }
    }

    /// Creates an `Tsil` iterator which uses a mutate closure to determine
    /// if an element should be removed like in `LinkedList`.
    ///
    /// If the closure returns true, then the element is removed and yielded.
    /// If the closure returns false, the element will remain in the `TsilCev`
    /// and will not be yielded
    /// by the iterator.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(4);
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// tc.push_back(5);
    /// tc.push_back(6);
    /// tc.push_back(7);
    /// tc.push_back(8);
    /// tc.push_back(9);
    ///
    /// let less_eq_four = tc.drain_filter_tsil(|x| *x <= 4).collect::<Vec<_>>();
    ///
    /// assert_eq!(less_eq_four, &[0, 1, 2, 3, 4]); // note the order of the sequence (Tsil iterator)
    /// assert_eq!(tc.into_vec(), &[5, 6, 7, 8, 9]);
    /// ```
    #[inline]
    pub fn drain_filter_tsil<F>(&mut self, pred: F) -> DrainFilterTsil<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len();
        DrainFilterTsil {
            cursor: self.cursor_front_mut(),
            pred: pred,
            max_feature_len: len,
        }
    }

    /// More efficient then drain_filter_tsil because use `Cev` iterator.
    /// But the iteration order is not the same as in `LinkedList`.
    /// Creates an `Cev` iterator which uses a mutate closure to determine
    /// if an element should be removed like in `Vec`.
    ///
    /// If the closure returns true, then the element is removed and yielded.
    /// If the closure returns false, the element will remain in the `TsilCev`
    /// and will not be yielded
    /// by the iterator.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(4);
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// tc.push_back(5);
    /// tc.push_back(6);
    /// tc.push_back(7);
    /// tc.push_back(8);
    /// tc.push_back(9);
    ///
    /// let less_eq_four = tc.drain_filter_cev(|x| *x <= 4).collect::<Vec<_>>();
    ///
    /// assert_eq!(less_eq_four, &[4, 3, 2, 1, 0]); // note the order of the sequence (Cev iterator)
    /// assert_eq!(tc.into_vec(), &[5, 6, 7, 8, 9]);
    /// ```
    #[inline]
    pub fn drain_filter_cev<F>(&mut self, pred: F) -> DrainFilterCev<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len();
        let current_ptr = self.cev.as_mut_ptr();
        DrainFilterCev {
            tsil_cev: self,
            current_ptr: current_ptr,
            pred: pred,
            max_feature_len: len,
        }
    }

    /// Returns reference to the front (start) element or `None` if `TsilCev`
    /// is empty like in `LinkedList`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// assert_eq!(tc.front(), Some(&0));
    /// assert_eq!(TsilCev::<()>::new().front(), None);
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        // safe because check back not empty
        Some(unsafe { &self.cev.get_unchecked(self.start().to_option()?).el })
    }

    /// Returns reference to the back (end) element or `None` if `TsilCev` is
    /// empty like in `LinkedList`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// assert_eq!(tc.back(), Some(&4));
    /// assert_eq!(TsilCev::<()>::new().back(), None);
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        // safe because check back not empty
        Some(unsafe { &self.cev.get_unchecked(self.end().to_option()?).el })
    }

    /// Returns mutable reference to the front (start) element or `None` if
    /// `TsilCev` is empty like in `LinkedList`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// match tc.front_mut() {
    ///     Some(x) => *x = 10,
    ///     None => {},
    /// }
    ///
    /// assert_eq!(tc.front(), Some(&10));
    /// assert_eq!(TsilCev::<()>::new().front(), None);
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        let start = self.start().to_option()?;
        // safe because check back not empty
        Some(unsafe { &mut self.cev.get_unchecked_mut(start).el })
    }

    /// Returns mutable reference to the back (end) element or `None` if
    /// `TsilCev` is empty like in `LinkedList`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// match tc.back_mut() {
    ///     Some(x) => *x = 14,
    ///     None => {},
    /// }
    ///
    /// assert_eq!(tc.back(), Some(&14));
    /// assert_eq!(TsilCev::<()>::new().back(), None);
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let end = self.end().to_option()?;
        // safe because check back not empty
        Some(unsafe { &mut self.cev.get_unchecked_mut(end).el })
    }

    /// Returns cursor to the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.current(), tc.front());
    /// ```
    #[inline]
    pub fn cursor_front(&self) -> Cursor<'_, T> {
        Cursor {
            tsil_cev: self,
            idx: self.start(),
        }
    }

    /// Returns cursor to the end (back) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor = tc.cursor_back();
    ///
    /// assert_eq!(cursor.current(), tc.back());
    /// ```
    #[inline]
    pub fn cursor_back(&self) -> Cursor<'_, T> {
        Cursor {
            tsil_cev: self,
            idx: self.end(),
        }
    }

    /// Returns mutable cursor to the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front_mut();
    /// if let Some(x) = cursor.current_mut() {
    ///     *x = 14;
    /// }
    ///
    /// assert_eq!(cursor.current(), Some(&14));
    /// assert_eq!(tc.into_vec(), &[14, 1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        let start = self.start();
        CursorMut {
            tsil_cev: self,
            idx: start,
        }
    }

    /// Returns mutable cursor to the back (end) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_back_mut();
    /// if let Some(x) = cursor.current_mut() {
    ///     *x = 14;
    /// }
    ///
    /// assert_eq!(cursor.current(), Some(&14));
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 14]);
    /// ```
    #[inline]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        let end = self.end();
        CursorMut {
            tsil_cev: self,
            idx: end,
        }
    }

    /// Returns cursor to the element with `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_back(4);
    ///
    /// assert_eq!(tc.cursor_idx_tsil(0).current(), Some(&1));
    /// assert_eq!(tc.cursor_idx_tsil(1).current(), Some(&2));
    /// assert_eq!(tc.cursor_idx_tsil(2).current(), Some(&3));
    /// assert_eq!(tc.cursor_idx_tsil(3).current(), Some(&4));
    /// ```
    pub fn cursor_idx_tsil(&self, idx: usize) -> Cursor<'_, T> {
        if idx >= self.len() {
            Cursor {
                tsil_cev: self,
                idx: Index::None,
            }
        } else if idx <= self.len() >> 1 {
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

    /// Returns mutable cursor to the element with `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_back(4);
    ///
    /// *tc.cursor_idx_tsil_mut(0).current_mut().unwrap() = 0;
    /// *tc.cursor_idx_tsil_mut(1).current_mut().unwrap() = 0;
    /// *tc.cursor_idx_tsil_mut(2).current_mut().unwrap() = 0;
    /// *tc.cursor_idx_tsil_mut(3).current_mut().unwrap() = 1;
    /// assert_eq!(tc.cursor_idx_tsil_mut(0).current(), Some(&0));
    /// assert_eq!(tc.cursor_idx_tsil_mut(1).current(), Some(&0));
    /// assert_eq!(tc.cursor_idx_tsil_mut(2).current(), Some(&0));
    /// assert_eq!(tc.cursor_idx_tsil_mut(3).current(), Some(&1));
    /// ```
    pub fn cursor_idx_tsil_mut(&mut self, idx: usize) -> CursorMut<'_, T> {
        if idx >= self.len() {
            CursorMut {
                tsil_cev: self,
                idx: Index::None,
            }
        } else if idx <= self.len() >> 1 {
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

    /// Transform `TsilCev` to `Vec` with `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_back(4);
    ///
    /// assert_eq!(tc.into_vec(), vec![1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        let mut res = Vec::with_capacity(self.len());
        unsafe {
            res.set_len(self.len());
        }
        res.iter_mut()
            .zip(self.iter_tsil())
            // safe because self move and droped
            .for_each(|(dest, src)| *dest = unsafe { read(src as *const _) });
        res
    }

    /// Places elements inside `TsilCev` in the order
    /// of `LinkedList` without using additional memory.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_back(4);
    ///
    /// tc.make_linked_list_order();
    /// assert_eq!(tc.iter_cev().copied().collect::<Vec<_>>(), vec![1, 2, 3, 4]);
    /// ```
    pub fn make_linked_list_order(&mut self) {
        debug_assert!(Index(0usize.wrapping_sub(1)).is_none());

        if !self.is_empty() {
            let start = self.cev.as_ptr();
            let mut cev_ptr = self.cev.as_mut_ptr();

            let end = unsafe { self.cev.as_mut_ptr().add(self.len() - 1) };
            let mut tsil_ptr = unsafe { start.add(self.start().0) as *mut _ };

            while cev_ptr != end {
                unsafe {
                    let cev_idx = cev_ptr.offset_from(start) as usize;
                    if tsil_ptr != cev_ptr {
                        let tsil_idx = Index(tsil_ptr.offset_from(start) as usize);
                        if (*tsil_ptr).next.0 == cev_idx {
                            (*tsil_ptr).next = tsil_idx;
                        } else {
                            if let Some(val_prev_idx) = (*cev_ptr).prev.to_option() {
                                self.cev.get_unchecked_mut(val_prev_idx).next = tsil_idx;
                            }
                            if let Some(val_next_idx) = (*cev_ptr).next.to_option() {
                                self.cev.get_unchecked_mut(val_next_idx).prev = tsil_idx;
                            }
                        }
                        swap(cev_ptr, tsil_ptr);
                    }

                    tsil_ptr = start.add((*cev_ptr).next.0) as *mut _;

                    (*cev_ptr).prev = Index(cev_idx.wrapping_sub(1));
                    (*cev_ptr).next = Index(cev_idx + 1);
                    cev_ptr = cev_ptr.offset(1);
                }
            }

            unsafe {
                (*end).next = Index::None;
                self.start = Index(0);
                self.end = Index(end.offset_from(start) as usize);
            }
        }
    }

    /// Sorts the slice with a comparator function like in `Vec`.
    /// This sort is stable (i.e., does not reorder equal elements) and `O(n * log(n))` worst-case.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![5, 4, 1, 3, 2]);
    /// tc.sort_by(|a, b| a.cmp(b));
    /// assert_eq!(tc.to_vec(), &[1, 2, 3, 4, 5]);
    ///
    /// // reverse sorting
    /// tc.sort_by(|a, b| b.cmp(a));
    /// assert_eq!(tc.to_vec(), &[5, 4, 3, 2, 1]);
    /// ```
    pub fn sort_by(&mut self, mut cmp: impl FnMut(&T, &T) -> Ordering) {
        self.cev.sort_by(|x, y| cmp(&x.el, &y.el));
        self.make_chain_cev();
    }

    /// Sorts the slice with a key extraction function like in `Vec`.
    /// This sort is stable (i.e., does not reorder equal elements) and `O(m * n * log(n))`
    /// worst-case, where the key function is `O(m)`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![-5i32, 4, 1, -3, 2]);
    ///
    /// tc.sort_by_key(|k| k.abs());
    /// assert_eq!(tc.to_vec(), &[1, 2, -3, 4, -5]);
    /// ```
    pub fn sort_by_key<K: Ord>(&mut self, mut f: impl FnMut(&T) -> K) {
        self.cev.sort_by_key(|x| f(&x.el));
        self.make_chain_cev();
    }

    /// Sorts the slice with a key extraction function like in `Vec`.
    /// During sorting, the key function is called only once per element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![-5i32, 4, 32, -3, 2]);
    ///
    /// tc.sort_by_cached_key(|k| k.to_string());
    /// assert_eq!(tc.to_vec(), &[-3, -5, 2, 32, 4]);
    /// ```
    pub fn sort_by_cached_key<K: Ord>(&mut self, mut f: impl FnMut(&T) -> K) {
        self.cev.sort_by_cached_key(|x| f(&x.el));
        self.make_chain_cev();
    }

    /// Sorts the slice with a comparator function, but may not preserve the order of equal
    /// elements like in `Vec`.
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(*n* \* log(*n*)) worst-case.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![5, 4, 1, 3, 2]);
    /// tc.sort_unstable_by(|a, b| a.cmp(b));
    /// assert_eq!(tc.to_vec(), &[1, 2, 3, 4, 5]);
    ///
    /// // reverse sorting
    /// tc.sort_unstable_by(|a, b| b.cmp(a));
    /// assert_eq!(tc.to_vec(), &[5, 4, 3, 2, 1]);
    /// ```
    pub fn sort_unstable_by(&mut self, mut cmp: impl FnMut(&T, &T) -> Ordering) {
        self.cev.sort_unstable_by(|x, y| cmp(&x.el, &y.el));
        self.make_chain_cev();
    }

    /// Sorts the slice with a key extraction function, but may not preserve the order of equal
    /// elements like in `Vec`.
    /// This sort is unstable (i.e., may reorder equal elements), in-place
    /// (i.e., does not allocate), and *O*(m \* *n* \* log(*n*)) worst-case, where the key function is
    /// *O*(*m*).
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![-5i32, 4, 1, -3, 2]);
    ///
    /// tc.sort_unstable_by_key(|k| k.abs());
    /// assert_eq!(tc.to_vec(), &[1, 2, -3, 4, -5]);
    /// ```
    pub fn sort_unstable_by_key<K: Ord>(&mut self, mut f: impl FnMut(&T) -> K) {
        self.cev.sort_unstable_by_key(|x| f(&x.el));
        self.make_chain_cev();
    }

    /// Reserves capacity for at least `additional` more elements to be
    /// inserted like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.len(), 5);
    /// assert!(tc.capacity() >= 5);
    ///
    /// tc.reserve(10);
    /// assert_eq!(tc.len(), 5);
    /// assert!(tc.capacity() >= 15);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.cev.reserve(additional);
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `TsilCev` like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.len(), 5);
    /// assert!(tc.capacity() >= 5);
    ///
    /// tc.reserve_exact(10);
    /// assert_eq!(tc.len(), 5);
    /// assert!(tc.capacity() >= 15);
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.cev.reserve_exact(additional);
    }

    /// Shrinks the capacity of the `TsilCev` as much as possible like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert!(tc.capacity() >= 5);
    ///
    /// tc.shrink_to_fit();
    /// assert_eq!(tc.capacity(), 5);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.cev.shrink_to_fit();
    }

    /// Returns the number of elements the `TsilCev` can hold without
    /// reallocating like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert!(tc.capacity() >= 5);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.cev.capacity()
    }

    /// Returns the number of elements in the `TsilCev` like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// assert_eq!(tc.capacity(), 5);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.cev.len()
    }

    /// Returns `true` if the `TsilCev` contains no elements like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// assert_eq!(tc.is_empty(), false);
    ///
    /// tc.clear();
    /// assert_eq!(tc.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.cev.is_empty()
    }

    /// Appends an element to the back (end) of a `TsilCev`
    /// like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// tc.push_back(5);
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 4, 5]);
    /// ```
    pub fn push_back(&mut self, val: T) {
        // safe because end is None or end < self.len
        unsafe { self.insert(self.end(), Index::None, val) };
    }

    /// Removes the last element from a `TsilCev` and returns it, or `None` if it
    /// is empty like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// tc.pop_back();
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3]);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        unsafe {
            let end_idx = self.end().to_option()?;
            let last_idx = self.len() - 1;

            let end = self.cev.as_mut_ptr().add(end_idx);
            let last = self.cev.as_mut_ptr().add(last_idx);

            self.connect((*end).prev, Index::None);
            if end != last {
                swap(end, last);
                self.reconnect((*end).prev, (*end).next, Index(end_idx));
            }
            self.cev.set_len(last_idx);
            Some(read(last).el)
        }
    }

    /// Appends an element to the front (start) of a `TsilCev`
    /// like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// tc.push_front(5);
    /// assert_eq!(tc.into_vec(), &[5, 0, 1, 2, 3, 4]);
    /// ```
    pub fn push_front(&mut self, val: T) {
        // safe because start is None or start < self.len
        unsafe { self.insert(Index::None, self.start(), val) };
    }

    /// Removes the first element from a `TsilCev` and returns it, or `None` if it
    /// is empty like in `Vec`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// tc.pop_front();
    /// assert_eq!(tc.into_vec(), &[1, 2, 3, 4]);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        unsafe {
            let start_idx = self.start().to_option()?;
            let last_idx = self.len() - 1;

            let start = self.cev.as_mut_ptr().add(start_idx);
            let last = self.cev.as_mut_ptr().add(last_idx);

            self.connect(Index::None, (*start).next);
            if start != last {
                swap(start, last);
                self.reconnect((*start).prev, (*start).next, Index(start_idx));
            }
            self.cev.set_len(last_idx);
            Some(read(last).el)
        }
    }

    #[inline]
    unsafe fn insert(&mut self, prev: Index, next: Index, val: T) {
        debug_assert!(
            prev.to_option().map_or(true, |x| x < self.len())
                && next.to_option().map_or(true, |x| x < self.len())
        );
        let current = self.len();
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
            prev.to_option().map_or(true, |x| x < self.len())
                && next.to_option().map_or(true, |x| x < self.len())
        );
        // safe if 0 <= x and y < cev.len
        match (prev.to_option(), next.to_option()) {
            (None, None) => {
                self.start = Index::None;
                self.end = Index::None;
            }
            (None, Some(y)) => {
                (*self.cev.as_mut_ptr().add(y)).prev = Index::None;
                self.start = Index(y);
            }
            (Some(x), None) => {
                (*self.cev.as_mut_ptr().add(x)).next = Index::None;
                self.end = Index(x);
            }
            (Some(x), Some(y)) => {
                (*self.cev.as_mut_ptr().add(x)).next = Index(y);
                (*self.cev.as_mut_ptr().add(y)).prev = Index(x);
            }
        };
    }

    #[inline]
    unsafe fn reconnect(&mut self, prev: Index, next: Index, current: Index) {
        debug_assert!(
            prev.to_option().map_or(true, |x| x < self.len())
                && next.to_option().map_or(true, |x| x < self.len())
                && current.to_option().map_or(false, |x| x < self.len())
        );
        // safe if 0 <= x and y and z < cev.len
        match (prev.to_option(), current.to_option(), next.to_option()) {
            (None, Some(z), None) => {
                self.start = Index(z);
                self.end = Index(z);
            }
            (None, Some(z), Some(y)) => {
                (*self.cev.as_mut_ptr().add(y)).prev = Index(z);
                self.start = Index(z);
            }
            (Some(x), Some(z), None) => {
                (*self.cev.as_mut_ptr().add(x)).next = Index(z);
                self.end = Index(z);
            }
            (Some(x), Some(z), Some(y)) => {
                (*self.cev.as_mut_ptr().add(x)).next = Index(z);
                (*self.cev.as_mut_ptr().add(y)).prev = Index(z);
            }
            _ => unreachable!(),
        };
    }

    #[inline]
    unsafe fn make_empty(&mut self, idx: usize) -> (T, Index) {
        debug_assert!(idx < self.len() && !self.is_empty());

        let last_idx = self.len() - 1;
        let last = self.cev.as_mut_ptr().add(last_idx);
        let val = self.cev.as_mut_ptr().add(idx);

        let next = (*val).next;
        self.connect((*val).prev, (*val).next);
        if idx != last_idx {
            swap(val, last);
            self.reconnect((*val).prev, (*val).next, Index(idx));
        }
        self.cev.set_len(last_idx);
        let ret = read(last).el;

        (ret, if next.0 == last_idx { Index(idx) } else { next })
    }

    #[inline]
    unsafe fn make_empty_ptr(&mut self, val: *mut Val<T>) -> (T, Index) {
        debug_assert!(!val.is_null() && val < self.cev.as_mut_ptr().add(self.len()));

        let last_idx = self.len() - 1;
        let last = self.cev.as_mut_ptr().add(last_idx);

        let next = (*val).next;
        let index = Index(val.offset_from(self.cev.as_ptr()) as usize);
        self.connect((*val).prev, (*val).next);
        if val != last {
            swap(val, last);
            self.reconnect((*val).prev, (*val).next, index);
        }
        self.cev.set_len(last_idx);
        let ret = read(last).el;

        (ret, if next.0 == last_idx { index } else { next })
    }

    #[inline]
    fn make_chain_cev(&mut self) {
        debug_assert!(Index(0usize.wrapping_sub(1)).is_none());

        if self.len() == 1 {
            self.start = Index(0);
            self.end = Index(0);
            // safe because self.len == 1
            unsafe {
                self.cev.get_unchecked_mut(0).prev = Index::None;
                self.cev.get_unchecked_mut(0).next = Index::None;
            };
        } else if self.len() > 1 {
            let last_idx = self.len() - 1;
            self.cev
                .iter_mut()
                .zip((0..).into_iter())
                .for_each(|(x, current_idx)| {
                    x.next = Index(current_idx + 1);
                    x.prev = Index(current_idx.wrapping_sub(1));
                });

            // safe because self.len > 1
            unsafe { self.cev.get_unchecked_mut(last_idx).next = Index::None };
            self.start = Index(0);
            self.end = Index(self.len() - 1);
        }
    }
}

impl<T: Clone> TsilCev<T> {
    /// Copies `TsilCev` into a new `Vec` with `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_front(3);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_back(4);
    ///
    /// assert_eq!(tc.to_vec(), vec![1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn to_vec(&self) -> Vec<T> {
        let mut res = Vec::<T>::with_capacity(self.len());
        unsafe {
            res.set_len(self.len());
        }
        res.iter_mut()
            .zip(self.iter_tsil())
            .for_each(|(dest, src)| dest.clone_from(src));
        res
    }
}

impl<T: Clone> From<&[T]> for TsilCev<T> {
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4].as_slice());
    ///
    /// assert_eq!(tc.front(), Some(&0));
    /// assert_eq!(tc.back(), Some(&4));
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 4]);
    /// ```
    fn from(slice: &[T]) -> Self {
        debug_assert!(Index(0usize.wrapping_sub(1)).is_none());

        if slice.is_empty() {
            Self::new()
        } else {
            let mut tsil_cev = TsilCev::with_capacity(slice.len());
            unsafe { tsil_cev.cev.set_len(slice.len()) };
            let last_idx = slice.len() - 1;
            tsil_cev
                .cev
                .iter_mut()
                .zip(slice.iter().zip((0..).into_iter()))
                .for_each(|(x, (val, current_idx))| {
                    *x = Val {
                        el: val.clone(),
                        next: Index(current_idx + 1),
                        prev: Index(current_idx.wrapping_sub(1)),
                    }
                });
            unsafe { tsil_cev.cev.get_unchecked_mut(last_idx).next = Index::None };
            tsil_cev.start = Index(0);
            tsil_cev.end = Index(last_idx);
            tsil_cev
        }
    }
}

impl<T> From<Vec<T>> for TsilCev<T> {
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.front(), Some(&0));
    /// assert_eq!(tc.back(), Some(&4));
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 4]);
    /// ```
    fn from(vec: Vec<T>) -> Self {
        debug_assert!(Index(0usize.wrapping_sub(1)).is_none());

        if vec.is_empty() {
            Self::new()
        } else {
            let mut tsil_cev = TsilCev::with_capacity(vec.len());
            unsafe { tsil_cev.cev.set_len(vec.len()) };
            let last_idx = vec.len() - 1;
            tsil_cev
                .cev
                .iter_mut()
                .zip(vec.into_iter().zip((0..).into_iter()))
                .for_each(move |(x, (val, current_idx))| {
                    *x = Val {
                        el: val,
                        next: Index(current_idx + 1),
                        prev: Index(current_idx.wrapping_sub(1)),
                    }
                });
            unsafe { tsil_cev.cev.get_unchecked_mut(last_idx).next = Index::None };
            tsil_cev.start = Index(0);
            tsil_cev.end = Index(last_idx);
            tsil_cev
        }
    }
}

impl<T: Clone> From<&Vec<T>> for TsilCev<T> {
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(&vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.front(), Some(&0));
    /// assert_eq!(tc.back(), Some(&4));
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 4]);
    /// ```
    fn from(vec: &Vec<T>) -> Self {
        Self::from(vec.as_slice())
    }
}

impl<T> From<TsilCev<T>> for Vec<T> {
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let vec = Vec::from(tc);
    /// assert_eq!(vec, &[0, 1, 2, 3, 4]);
    /// ```
    fn from(tsil_cev: TsilCev<T>) -> Self {
        tsil_cev.into_vec()
    }
}

impl<T: Clone> From<&TsilCev<T>> for Vec<T> {
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let vec = Vec::from(&tc);
    /// assert_eq!(vec, &[0, 1, 2, 3, 4]);
    /// ```
    fn from(tsil_cev: &TsilCev<T>) -> Self {
        tsil_cev.iter_tsil().cloned().collect()
    }
}

#[derive(Clone)]
pub struct Cursor<'t, T: 't> {
    tsil_cev: &'t TsilCev<T>,
    idx: Index,
}

impl<'t, T: 't> Cursor<'t, T> {
    /// Returns `true` if cursor pointing on some element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.is_none(), false);
    ///
    /// cursor.move_prev();
    /// assert_eq!(cursor.is_none(), true);
    /// ```
    #[inline]
    pub fn is_none(&self) -> bool {
        self.idx.is_none()
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing or `None` if cursor empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// ```
    #[inline]
    pub fn current(&self) -> Option<&T> {
        debug_assert!(self
            .idx
            .to_option()
            .map_or(true, |x| x < self.tsil_cev.cev.len()));

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).el })
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing and not check if cursor empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor = tc.cursor_front();
    ///
    /// assert_eq!(unsafe { cursor.current_unchecked() }, &0);
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn current_unchecked(&self) -> &T {
        debug_assert!(self
            .idx
            .to_option()
            .map_or(false, |x| x < self.tsil_cev.cev.len()));

        &self.tsil_cev.cev.get_unchecked(self.idx.0).el
    }

    /// Move cursor to front (start) `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_idx_tsil(3);
    ///
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_to_start();
    /// assert_eq!(cursor.current(), Some(&0));
    /// ```
    #[inline]
    pub fn move_to_start(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.start();
        self
    }

    /// Move cursor to back (end) `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_idx_tsil(3);
    ///
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_to_end();
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub fn move_to_end(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.end();
        self
    }

    /// Move cursor to next `TsilCev` element in `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    #[inline]
    pub fn move_next(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next }
        }
        self
    }

    /// Move cursor to prev `TsilCev` element in `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_back();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    #[inline]
    pub fn move_prev(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev }
        }
        self
    }

    /// Move cursor to next `TsilCev` element in `LinkedList` order.
    /// If the cursor is empty or back (end) element in `TsilCev`
    /// then this will move to the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_back();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_next_cycle();
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_next_cycle();
    /// assert_eq!(cursor.current(), Some(&1));
    /// ```
    #[inline]
    pub fn move_next_cycle(&mut self) -> &mut Self {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.end.0
        {
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
        } else {
            self.move_to_start();
        }
        self
    }

    /// Move cursor to prev `TsilCev` element in `LinkedList` order.
    /// If the cursor is empty or front (start) element in `TsilCev`
    /// then this will move to the back (end) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_prev_cycle();
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_prev_cycle();
    /// assert_eq!(cursor.current(), Some(&3));
    /// ```
    #[inline]
    pub fn move_prev_cycle(&mut self) -> &mut Self {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.start.0
        {
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
        } else {
            self.move_to_end();
        }
        self
    }

    /// Move cursor to next `TsilCev` element in `LinkedList` order
    /// not check if cursor is empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// unsafe { cursor.move_next_unchecked() };
    /// assert_eq!(cursor.current(), Some(&1));
    /// unsafe { cursor.move_next_unchecked() };
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn move_next_unchecked(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.cev.get_unchecked(self.idx.0).next;
        self
    }

    /// Move cursor to prev `TsilCev` element in `LinkedList` order
    /// not check if cursor is empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_back();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// unsafe { cursor.move_prev_unchecked() };
    /// assert_eq!(cursor.current(), Some(&3));
    /// unsafe { cursor.move_prev_unchecked() };
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn move_prev_unchecked(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.cev.get_unchecked(self.idx.0).prev;
        self
    }

    /// Move cursor to next `TsilCev` elements with lengths in
    /// `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_front();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_next_length(1);
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_next_length(3);
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub fn move_next_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len != 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            len -= 1;
        }
        self
    }

    /// Move cursor to prev `TsilCev` element with lenght in
    /// `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_back();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_prev_length(1);
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_prev_length(3);
    /// assert_eq!(cursor.current(), Some(&0));
    /// ```
    #[inline]
    pub fn move_prev_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len != 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            len -= 1;
        }
        self
    }

    /// Returns a reference to the next element or `None` if cursor empty
    /// or next element not exist.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.cursor_front().peek_next(), Some(&1));
    /// assert_eq!(tc.cursor_back().peek_next(), None);
    /// ```
    #[inline]
    pub fn peek_next(&self) -> Option<&T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).next };
        // safe because next_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(next_idx.to_option()?).el })
    }

    /// Returns a reference to the prev element or `None` if cursor empty
    /// or prev element not exist.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.cursor_front().peek_prev(), None);
    /// assert_eq!(tc.cursor_back().peek_prev(), Some(&3));
    /// ```
    #[inline]
    pub fn peek_prev(&self) -> Option<&T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).prev };
        // safe because prev_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(prev_idx.to_option()?).el })
    }

    /// Returns a reference to the next element or `None` if `TsilCev` empty.
    /// If the cursor is empty or back (end) element in `TsilCev`
    /// then this will return the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.cursor_back().peek_next_cycle(), Some(&0));
    /// assert_eq!(tc.cursor_back().peek_next(), None);
    /// ```
    #[inline]
    pub fn peek_next_cycle(&self) -> Option<&T> {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.end.0
        {
            let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            Some(unsafe { &self.tsil_cev.cev.get_unchecked(next_idx.0).el })
        } else {
            Some(unsafe {
                &self
                    .tsil_cev
                    .cev
                    .get_unchecked(self.tsil_cev.start.to_option()?)
                    .el
            })
        }
    }

    /// Returns a reference to the prev element or `None` if `TsilCev` empty.
    /// If the cursor is empty or back (end) element in `TsilCev`
    /// then this will return the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.cursor_front().peek_prev_cycle(), Some(&4));
    /// assert_eq!(tc.cursor_front().peek_prev(), None);
    /// ```
    #[inline]
    pub fn peek_prev_cycle(&self) -> Option<&T> {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.start.0
        {
            let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            Some(unsafe { &self.tsil_cev.cev.get_unchecked(prev_idx.0).el })
        } else {
            Some(unsafe {
                &self
                    .tsil_cev
                    .cev
                    .get_unchecked(self.tsil_cev.end.to_option()?)
                    .el
            })
        }
    }

    /// Finish combination chain with cursor.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// let mut cursor = tc.cursor_front().move_next_length(3).finish();
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub fn finish(&mut self) -> Self {
        Self {
            tsil_cev: &self.tsil_cev,
            idx: self.idx,
        }
    }
}

pub struct CursorMut<'t, T: 't> {
    tsil_cev: &'t mut TsilCev<T>,
    idx: Index,
}

impl<'t, T: 't> CursorMut<'t, T> {
    /// Returns `true` if cursor pointing on some element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front_mut();
    ///
    /// assert_eq!(cursor.is_none(), false);
    ///
    /// cursor.move_prev();
    /// assert_eq!(cursor.is_none(), true);
    /// ```
    #[inline]
    pub fn is_none(&self) -> bool {
        self.idx.is_none()
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing or `None` if cursor empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor = tc.cursor_front_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// ```
    #[inline]
    pub fn current(&self) -> Option<&T> {
        debug_assert!(self
            .idx
            .to_option()
            .map_or(true, |x| x < self.tsil_cev.cev.len()));

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe { &self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).el })
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing and not check if cursor empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor = tc.cursor_front();
    ///
    /// assert_eq!(unsafe { cursor.current_unchecked() }, &0);
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn current_unchecked(&self) -> &T {
        debug_assert!(self
            .idx
            .to_option()
            .map_or(false, |x| x < self.tsil_cev.cev.len()));

        &self.tsil_cev.cev.get_unchecked(self.idx.0).el
    }

    /// Returns a mutable reference to the element that the cursor is currently
    /// pointing or `None` if cursor empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front_mut();
    /// match cursor.current_mut() {
    ///     Some(x) => *x = 10,
    ///     None => {},
    /// };
    ///
    /// assert_eq!(cursor.current(), Some(&10));
    /// ```
    #[inline]
    pub fn current_mut(&mut self) -> Option<&mut T> {
        debug_assert!(self
            .idx
            .to_option()
            .map_or(true, |x| x < self.tsil_cev.cev.len()));

        // safe because 0 <= Some(self.idx) < cev.len because self.idx traversal on tsil_cev
        Some(unsafe {
            &mut self
                .tsil_cev
                .cev
                .get_unchecked_mut(self.idx.to_option()?)
                .el
        })
    }

    /// Returns a mutable reference to the element that the cursor is currently
    /// pointing and not check if cursor empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front_mut();
    /// unsafe { *cursor.current_unchecked_mut() = 10 };
    ///
    /// assert_eq!(cursor.current(), Some(&10));
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn current_unchecked_mut(&mut self) -> &mut T {
        debug_assert!(self
            .idx
            .to_option()
            .map_or(false, |x| x < self.tsil_cev.cev.len()));

        &mut self.tsil_cev.cev.get_unchecked_mut(self.idx.0).el
    }

    /// Move cursor to front (start) `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_idx_tsil_mut(3);
    ///
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_to_start();
    /// assert_eq!(cursor.current(), Some(&0));
    /// ```
    #[inline]
    pub fn move_to_start(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.start();
        self
    }

    /// Move cursor to back (end) `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_idx_tsil_mut(3);
    ///
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_to_end();
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub fn move_to_end(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.end();
        self
    }

    /// Move cursor to next `TsilCev` element in `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_front_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    #[inline]
    pub fn move_next(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next }
        }
        self
    }

    /// Move cursor to prev `TsilCev` element in `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_back_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    #[inline]
    pub fn move_prev(&mut self) -> &mut Self {
        if !self.idx.is_none() {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev }
        }
        self
    }

    /// Move cursor to next `TsilCev` element in `LinkedList` order.
    /// If the cursor is empty or back (end) element in `TsilCev`
    /// then this will move to the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_back_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_next_cycle();
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_next_cycle();
    /// assert_eq!(cursor.current(), Some(&1));
    /// ```
    #[inline]
    pub fn move_next_cycle(&mut self) -> &mut Self {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.end.0
        {
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
        } else {
            self.move_to_start();
        }
        self
    }

    /// Move cursor to prev `TsilCev` element in `LinkedList` order.
    /// If the cursor is empty or front (start) element in `TsilCev`
    /// then this will move to the back (end) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let mut cursor = tc.cursor_front_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_prev_cycle();
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_prev_cycle();
    /// assert_eq!(cursor.current(), Some(&3));
    /// ```
    #[inline]
    pub fn move_prev_cycle(&mut self) -> &mut Self {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.start.0
        {
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
        } else {
            self.move_to_end();
        }
        self
    }

    /// Move cursor to next `TsilCev` element in `LinkedList` order
    /// not check if cursor is empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_front_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// unsafe { cursor.move_next_unchecked() };
    /// assert_eq!(cursor.current(), Some(&1));
    /// unsafe { cursor.move_next_unchecked() };
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn move_next_unchecked(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.cev.get_unchecked(self.idx.0).next;
        self
    }

    /// Move cursor to prev `TsilCev` element in `LinkedList` order
    /// not check if cursor is empty.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_back_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// unsafe { cursor.move_prev_unchecked() };
    /// assert_eq!(cursor.current(), Some(&3));
    /// unsafe { cursor.move_prev_unchecked() };
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    /// # Safety
    ///
    /// This function safe if current not None.
    #[inline]
    pub unsafe fn move_prev_unchecked(&mut self) -> &mut Self {
        self.idx = self.tsil_cev.cev.get_unchecked(self.idx.0).prev;
        self
    }

    /// Move cursor to next `TsilCev` elements with lengths in
    /// `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_front_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&0));
    /// cursor.move_next_length(1);
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_next_length(3);
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub fn move_next_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len != 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            len -= 1;
        }
        self
    }

    /// Move cursor to prev `TsilCev` element with lenght in
    /// `LinkedList` order.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::new();
    /// tc.push_back(3);
    /// tc.push_back(4);
    /// tc.push_front(2);
    /// tc.push_front(1);
    /// tc.push_front(0);
    /// let mut cursor = tc.cursor_back_mut();
    ///
    /// assert_eq!(cursor.current(), Some(&4));
    /// cursor.move_prev_length(1);
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_prev_length(3);
    /// assert_eq!(cursor.current(), Some(&0));
    /// ```
    #[inline]
    pub fn move_prev_length(&mut self, mut len: usize) -> &mut Self {
        while !self.idx.is_none() && len != 0 {
            // safe because by previous check and self.idx traversal on tsil_cev
            self.idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            len -= 1;
        }
        self
    }

    /// Returns a mutable reference to the next element or `None` if cursor empty
    /// or next element not exist.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// *tc.cursor_front_mut().peek_next().unwrap() = 10;
    ///
    /// assert_eq!(tc.cursor_front_mut().peek_next(), Some(&mut 10));
    /// assert_eq!(tc.cursor_back_mut().peek_next(), None);
    /// ```
    #[inline]
    pub fn peek_next(&mut self) -> Option<&mut T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).next };
        // safe because next_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe {
            &mut self
                .tsil_cev
                .cev
                .get_unchecked_mut(next_idx.to_option()?)
                .el
        })
    }

    /// Returns a mutable reference to the prev element or `None` if cursor empty
    /// or prev element not exist.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// *tc.cursor_back_mut().peek_prev().unwrap() = 30;
    ///
    /// assert_eq!(tc.cursor_front_mut().peek_prev(), None);
    /// assert_eq!(tc.cursor_back_mut().peek_prev(), Some(&mut 30));
    /// ```
    #[inline]
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        // safe because self.idx.to_option()? and self.idx traversal on tsil_cev
        let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.to_option()?).prev };
        // safe because prev_idx.to_option()? and self.idx traversal on tsil_cev
        Some(unsafe {
            &mut self
                .tsil_cev
                .cev
                .get_unchecked_mut(prev_idx.to_option()?)
                .el
        })
    }

    /// Returns a mutable reference to the next element or `None` if `TsilCev` empty.
    /// If the cursor is empty or back (end) element in `TsilCev`
    /// then this will return the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.cursor_back_mut().peek_next_cycle(), Some(&mut 0));
    /// assert_eq!(tc.cursor_back_mut().peek_next(), None);
    /// ```
    #[inline]
    pub fn peek_next_cycle(&mut self) -> Option<&mut T> {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.end.0
        {
            let next_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            Some(unsafe { &mut self.tsil_cev.cev.get_unchecked_mut(next_idx.0).el })
        } else {
            Some(unsafe {
                &mut self
                    .tsil_cev
                    .cev
                    .get_unchecked_mut(self.tsil_cev.start.to_option()?)
                    .el
            })
        }
    }

    /// Returns a mutable reference to the prev element or `None` if `TsilCev` empty.
    /// If the cursor is empty or back (end) element in `TsilCev`
    /// then this will return the front (start) element.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// assert_eq!(tc.cursor_front_mut().peek_prev_cycle(), Some(&mut 4));
    /// assert_eq!(tc.cursor_front_mut().peek_prev(), None);
    /// ```
    #[inline]
    pub fn peek_prev_cycle(&mut self) -> Option<&mut T> {
        if !self.idx.is_none() &&
            // valid because self.idx not Index::None
            self.idx.0 != self.tsil_cev.start.0
        {
            let prev_idx = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            Some(unsafe { &mut self.tsil_cev.cev.get_unchecked_mut(prev_idx.0).el })
        } else {
            Some(unsafe {
                &mut self
                    .tsil_cev
                    .cev
                    .get_unchecked_mut(self.tsil_cev.end.to_option()?)
                    .el
            })
        }
    }

    /// Finish combination chain with cursor.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// let mut cursor = tc.cursor_front_mut().move_next_length(3).finish();
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub fn finish(&mut self) -> Self {
        Self {
            // safe because Rust can't deduce that we won't return multiple references to the same value
            tsil_cev: unsafe { &mut *(self.tsil_cev as *mut _) },
            idx: self.idx,
        }
    }

    /// Convert CursorMut to Cursor.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// let cursor_mut = tc.cursor_front_mut().move_next_length(3).finish();
    /// let mut cursor = cursor_mut.into_cursor();
    ///
    /// assert_eq!(cursor.current(), Some(&3));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&4));
    /// ```
    #[inline]
    pub const fn into_cursor(self) -> Cursor<'t, T> {
        Cursor {
            tsil_cev: self.tsil_cev,
            idx: self.idx,
        }
    }

    /// Insert elements before current cursor position in `LinkedList` order.
    /// Current cursor position don't move. If the cursor is empty then the
    /// new element is inserted at the back (end) of the `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().insert_before(-1).finish();
    /// assert_eq!(cursor.current(), Some(&0));
    /// assert_eq!(tc.to_vec(), &[-1, 0, 1, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().move_next_length(3).insert_before(20).finish();
    /// assert_eq!(cursor.current(), Some(&2));
    /// assert_eq!(tc.to_vec(), &[-1, 0, 1, 20, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().move_prev().insert_before(100).finish();
    /// assert_eq!(cursor.current(), None);
    /// assert_eq!(tc.to_vec(), &[-1, 0, 1, 20, 2, 3, 4, 100]);
    /// ```
    pub fn insert_before(&mut self, val: T) -> &mut Self {
        if !self.idx.is_none() {
            let prev = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).prev };
            unsafe { self.tsil_cev.insert(prev, self.idx, val) };
        } else {
            self.tsil_cev.push_back(val);
        }
        self
    }

    /// Insert elements after current cursor position in `LinkedList` order.
    /// Current cursor position don't move. If the cursor is empty then the
    /// new element is inserted at the front (start) of the `TsilCev`.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().insert_after(10).finish();
    /// assert_eq!(cursor.current(), Some(&0));
    /// assert_eq!(tc.to_vec(), &[0, 10, 1, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().move_next_length(3).insert_after(20).finish();
    /// assert_eq!(cursor.current(), Some(&2));
    /// assert_eq!(tc.to_vec(), &[0, 10, 1, 2, 20, 3, 4]);
    ///
    /// let cursor = tc.cursor_back_mut().move_next().insert_after(-1).finish();
    /// assert_eq!(cursor.current(), None);
    /// assert_eq!(tc.to_vec(), &[-1, 0, 10, 1, 2, 20, 3, 4]);
    /// ```
    pub fn insert_after(&mut self, val: T) -> &mut Self {
        if !self.idx.is_none() {
            let next = unsafe { self.tsil_cev.cev.get_unchecked(self.idx.0).next };
            unsafe { self.tsil_cev.insert(self.idx, next, val) };
        } else {
            self.tsil_cev.push_front(val);
        }
        self
    }

    /// Removes and return the current element from the `TsilCev` and move current
    /// cursor to the next position in `LinkedList` order. If the cursor is empty
    /// then no remove and `None` is returned.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// let mut cursor = tc.cursor_front_mut();
    /// assert_eq!(cursor.owned(), Some(0));
    /// assert_eq!(cursor.current(), Some(&1));
    /// assert_eq!(tc.to_vec(), &[1, 2, 3, 4]);
    ///
    /// let mut cursor = tc.cursor_front_mut().move_next_length(2).finish();
    /// assert_eq!(cursor.owned(), Some(3));
    /// assert_eq!(cursor.current(), Some(&4));
    /// assert_eq!(tc.to_vec(), &[1, 2, 4]);
    ///
    /// let mut cursor = tc.cursor_back_mut();
    /// assert_eq!(cursor.owned(), Some(4));
    /// assert_eq!(cursor.current(), None);
    /// assert_eq!(tc.to_vec(), &[1, 2]);
    /// ```
    pub fn owned(&mut self) -> Option<T> {
        let idx = self.idx.to_option()?;
        let (ret, next_idx) = unsafe { self.tsil_cev.make_empty(idx) };
        self.idx = next_idx;
        Some(ret)
    }

    /// Like `owned`, but don't return value.
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().remove().finish();
    /// assert_eq!(cursor.current(), Some(&1));
    /// assert_eq!(tc.to_vec(), &[1, 2, 3, 4]);
    ///
    /// let cursor = tc.cursor_front_mut().move_next_length(2).remove().finish();
    /// assert_eq!(cursor.current(), Some(&4));
    /// assert_eq!(tc.to_vec(), &[1, 2, 4]);
    ///
    /// let cursor = tc.cursor_back_mut().remove().finish();
    /// assert_eq!(cursor.current(), None);
    /// assert_eq!(tc.to_vec(), &[1, 2]);
    /// ```
    #[inline]
    pub fn remove(&mut self) -> &mut Self {
        let _ = self.owned();
        self
    }
}

#[derive(Clone)]
pub struct TsilIter<'t, T: 't> {
    start_cursor: Cursor<'t, T>,
    end_cursor: Cursor<'t, T>,
    feature_len: usize,
}

impl<'t, T: 't> Iterator for TsilIter<'t, T> {
    type Item = &'t T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.feature_len != 0 {
            self.feature_len -= 1;
            // safe because Rust can't deduce that we won't return multiple references to the same value
            let x = Some(unsafe { &*(self.start_cursor.current_unchecked() as *const _) });
            // self.feature_len != 0
            unsafe { self.start_cursor.move_next_unchecked() };
            x
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.feature_len, Some(self.feature_len))
    }

    #[inline]
    fn last(mut self) -> Option<&'t T> {
        self.next_back()
    }
}

impl<'t, T: 't> DoubleEndedIterator for TsilIter<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t T> {
        if self.feature_len != 0 {
            self.feature_len -= 1;
            // safe because Rust can't deduce that we won't return multiple references to the same value
            let x = Some(unsafe { &*(self.end_cursor.current_unchecked() as *const _) });
            // self.feature_len != 0
            unsafe { self.end_cursor.move_prev_unchecked() };
            x
        } else {
            None
        }
    }
}

pub struct TsilIterMut<'t, T: 't> {
    start_cursor: CursorMut<'t, T>,
    end_cursor: CursorMut<'t, T>,
    feature_len: usize,
}

impl<'t, T: 't> Iterator for TsilIterMut<'t, T> {
    type Item = &'t mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.feature_len != 0 {
            self.feature_len -= 1;
            // safe because Rust can't deduce that we won't return multiple references to the same value
            let x = Some(unsafe { &mut *(self.start_cursor.current_unchecked_mut() as *mut _) });
            // self.feature_len != 0
            unsafe { self.start_cursor.move_next_unchecked() };
            x
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.feature_len, Some(self.feature_len))
    }

    #[inline]
    fn last(mut self) -> Option<&'t mut T> {
        self.next_back()
    }
}

impl<'t, T: 't> DoubleEndedIterator for TsilIterMut<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t mut T> {
        if self.feature_len != 0 {
            self.feature_len -= 1;
            // safe because Rust can't deduce that we won't return multiple references to the same value
            let x = Some(unsafe { &mut *(self.end_cursor.current_unchecked_mut() as *mut _) });
            // self.feature_len != 0
            unsafe { self.end_cursor.move_prev_unchecked() };
            x
        } else {
            None
        }
    }
}

#[derive(Clone)]
pub struct TsilIntoIter<T> {
    tsil_cev: TsilCev<T>,
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

impl<'t, T: 't> FusedIterator for TsilIter<'t, T> {}
impl<'t, T: 't> FusedIterator for TsilIterMut<'t, T> {}
impl<'t, T: 't> FusedIterator for CevIter<'t, T> {}
impl<'t, T: 't> FusedIterator for CevIterMut<'t, T> {}
impl<T> FusedIterator for TsilIntoIter<T> {}

#[derive(Clone)]
#[repr(transparent)]
pub struct CevIter<'t, T: 't> {
    iter: Iter<'t, Val<T>>,
}

impl<'t, T: 't> Iterator for CevIter<'t, T> {
    type Item = &'t T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(&self.iter.next()?.el)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<&'t T> {
        Some(&self.iter.next_back()?.el)
    }
}

impl<'t, T: 't> DoubleEndedIterator for CevIter<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t T> {
        Some(&self.iter.next_back()?.el)
    }
}

#[repr(transparent)]
pub struct CevIterMut<'t, T: 't> {
    iter: IterMut<'t, Val<T>>,
}

impl<'t, T: 't> Iterator for CevIterMut<'t, T> {
    type Item = &'t mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(&mut self.iter.next()?.el)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<&'t mut T> {
        Some(&mut self.iter.next_back()?.el)
    }
}

impl<'t, T: 't> DoubleEndedIterator for CevIterMut<'t, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'t mut T> {
        Some(&mut self.iter.next_back()?.el)
    }
}

pub struct DrainFilterTsil<'t, T: 't, F: 't>
where
    F: FnMut(&mut T) -> bool,
{
    cursor: CursorMut<'t, T>,
    pred: F,
    max_feature_len: usize,
}

impl<T, F> Iterator for DrainFilterTsil<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        while self.max_feature_len != 0 {
            self.max_feature_len -= 1;
            let x = unsafe { self.cursor.current_unchecked_mut() };
            if (self.pred)(x) {
                return self.cursor.owned();
            }
            unsafe { self.cursor.move_next_unchecked() };
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.max_feature_len))
    }
}

impl<T, F> Drop for DrainFilterTsil<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    fn drop(&mut self) {
        self.for_each(drop)
    }
}

pub struct DrainFilterCev<'t, T: 't, F: 't>
where
    F: FnMut(&mut T) -> bool,
{
    tsil_cev: &'t mut TsilCev<T>,
    current_ptr: *mut Val<T>,
    pred: F,
    max_feature_len: usize,
}

impl<T, F> Iterator for DrainFilterCev<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        while self.max_feature_len != 0 {
            self.max_feature_len -= 1;
            let x = unsafe { &mut (*self.current_ptr).el };
            if (self.pred)(x) {
                return Some(unsafe { self.tsil_cev.make_empty_ptr(self.current_ptr) }.0);
            }
            self.current_ptr = unsafe { self.current_ptr.offset(1) };
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.max_feature_len))
    }
}

impl<T, F> Drop for DrainFilterCev<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    fn drop(&mut self) {
        self.for_each(drop)
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
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let mut tc = TsilCev::from(vec![0, 1, 2, 3, 4]);
    /// tc.extend((5..=10).into_iter());
    ///
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    ///
    /// let mut tc = TsilCev::new();
    /// tc.extend((0..=4).into_iter());
    ///
    /// assert_eq!(tc.into_vec(), TsilCev::from(vec![0, 1, 2, 3, 4]).into_vec());
    /// ```
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        debug_assert!(Index(0usize.wrapping_sub(1)).is_none());
        // like
        // iter.into_iter().for_each(move |x| self.push_back(x));

        let old_len = self.len();
        self.cev
            .extend(
                iter.into_iter()
                    .zip((old_len..).into_iter())
                    .map(move |(x, current_idx)| Val {
                        el: x,
                        next: Index(current_idx + 1),
                        prev: Index(current_idx.wrapping_sub(1)),
                    }),
            );
        let new_len = self.len();
        if new_len != old_len {
            // not underflow because new_len > 0
            let last = new_len - 1;
            // safe because 0 <= last and old_len < self.cev.len
            unsafe {
                self.cev.get_unchecked_mut(last).next = Index::None;
                self.cev.get_unchecked_mut(old_len).prev = self.end;
                if old_len > 0 {
                    self.cev.get_unchecked_mut(self.end.0).next = Index(old_len);
                }
            }
            if old_len == 0 {
                self.start = Index(0);
            }
            self.end = Index(last);
        }
    }
}

impl<'t, T: 't + Copy> Extend<&'t T> for TsilCev<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'t T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

impl<T> FromIterator<T> for TsilCev<T> {
    /// ```
    /// use tsil_cev::TsilCev;
    ///
    /// let tc = (0..=4).into_iter().map(|x| x).collect::<TsilCev<_>>();
    ///
    /// assert_eq!(tc.into_vec(), &[0, 1, 2, 3, 4]);
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut tsil_cev = Self::new();
        tsil_cev.extend(iter.into_iter());
        tsil_cev
    }
}

impl<T: PartialEq> PartialEq for TsilCev<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter_tsil().eq(other)
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

impl<T: Hash> Hash for TsilCev<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for elt in self {
            elt.hash(state);
        }
    }
}
