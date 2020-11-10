//! Reusable slice of references.
//!
//! # Motivation
//!
//! The [`Slice`] data structure from this crate can be used to solve a very specific problem:
//!
//! ---
//!
//! * We want to create a slice of references (a.k.a. `&[&T]` or `&mut [&mut T]`)
//!   with a length not known at compile time.
//!
//! *AND*
//!
//! * Multiple invocations should be able to use incompatible lifetimes
//!   (all references within each single invocation must of course have a common lifetime).
//!
//! *AND*
//!
//! * The allocated memory should be reusable for multiple invocations.
//!
//! ---
//!
//! The hard part is fulfilling all three requirements at the same time.
//! If we allow either one of them to be broken,
//! this problem can be solved easily with built-in tools:
//!
//! * If the number of references is known at compile time, the built-in array type
//!   (a.k.a. `[&T; N]` or `[&mut T; N]`) can (and should!) be used.
//!   No dynamic memory at all has to be allocated.
//!
//! * If all used lifetimes are compatible, a single [`Vec<&T>`](Vec) can be used and reused.
//!
//! * If the lifetimes are not compatible, but we don't care about allocating
//!   at each invocation, a fresh [`Vec<&T>`](Vec) can be used each time,
//!   allowing for different (and incompatible) lifetimes.
//!
//! The following example shows the problem with incompatible lifetimes.
//! The number of references in this example is known at compile time,
//! but let's just pretend it's not.
//!
//! ```compile_fail
//! fn print_slice(slice: &[&str]) { for s in slice { print!("<{}>", s); } println!(); }
//!
//! let mut vec = Vec::<&str>::with_capacity(2);
//!
//! {
//!     let one = String::from("one");
//!     let two = String::from("two");
//!     vec.push(&one);
//!     vec.push(&two);
//!     print_slice(&vec);
//!     vec.clear();
//! }
//!
//! let three = String::from("three");
//! vec.push(&three);
//! print_slice(&vec);
//! ```
//!
//! This example cannot be compiled, the compiler complains:
//!
//! ```text
//! error[E0597]: `one` does not live long enough
//!    |
//! 8  |     vec.push(&one);
//!    |              ^^^^ borrowed value does not live long enough
//! ...
//! 12 | }
//!    | - `one` dropped here while still borrowed
//! ...
//! 15 | vec.push(&three);
//!    | --- borrow later used here
//!
//! For more information about this error, try `rustc --explain E0597`.
//! ```
//!
//! Even though the `Vec<&str>` is emptied at the end of the inner scope,
//! it still "remembers" the lifetime of its previous inhabitants
//! and doesn't allow future references to have incompatible lifetimes.
//!
//! The problem can be solved with the [`Slice`] type from this crate:
//!
//! ```
//! use rsor::Slice;
//! # fn print_slice(slice: &[&str]) { for s in slice { print!("<{}>", s); } println!(); }
//!
//! let mut myslice = Slice::<str>::with_capacity(2);
//!
//! {
//!     let one = String::from("one");
//!     let two = String::from("two");
//!
//!     let strings = myslice.fill(|mut v| {
//!         v.push(&one);
//!         v.push(&two);
//!         v
//!     });
//!     print_slice(strings);
//! }
//!
//! let three = String::from("three");
//!
//! let strings = myslice.fill(|mut v| {
//!     v.push(&three);
//!     v
//! });
//! print_slice(strings);
//! assert_eq!(myslice.capacity(), 2);
//! ```
//!
//! This example compiles successfully and produces the expected output:
//!
//! ```text
//! <one><two>
//! <three>
//! ```
//!
//! Note that the capacity has not changed from the initial value,
//! i.e. no additional memory has been allocated.
//!
//! # Common Use Cases
//!
//! The previous example was quite artificial, in order
//! to illustrate the problem with incompatible lifetimes.
//!
//! The following, a bit more realistic example is using a [`Slice<[T]>`](Slice)
//! to create a (mutable) *slice of slices* (a.k.a. `&mut [&mut [T]]`)
//! from a (mutable) flat slice (a.k.a. `&mut [T]`):
//!
//! ```
//! use rsor::Slice;
//!
//! fn sos_from_flat_slice<'a, 'b>(
//!     reusable_slice: &'a mut Slice<[f32]>,
//!     flat_slice: &'b mut [f32],
//!     subslice_length: usize,
//! ) -> &'a mut [&'b mut [f32]] {
//!     reusable_slice.from_iter_mut(flat_slice.chunks_mut(subslice_length))
//! }
//! ```
//!
//! In some cases, two separate named lifetimes are not necessary;
//! just try combining them into a single one and see if it still works.
//!
//! The same thing can of course also be done for immutable slices
//! by removing all instances of `mut` except on the first argument
//! (but including changing
//! [`.from_iter_mut()`](Slice::from_iter_mut) to
//! [`.from_iter()`](Slice::from_iter) and
//! `.chunks_mut()` to `.chunks()`).
//!
//! If a pointer/length pair is given, it can be turned into a slice with
//! [`std::slice::from_raw_parts_mut()`] or [`std::slice::from_raw_parts()`].
//!
//! In C APIs it is common to have a "pointer to pointers",
//! where one pointer points to a contiguous piece of memory
//! containing further pointers, each pointing to yet another piece of memory.
//!
//! To turn these nested pointers into nested slices, we can use something like this:
//!
//! ```
//! # use rsor::Slice;
//! unsafe fn sos_from_nested_pointers<'a, 'b>(
//!     reusable_slice: &'a mut Slice<[f32]>,
//!     ptr: *const *mut f32,
//!     subslices: usize,
//!     subslice_length: usize,
//! ) -> &'a mut [&'b mut [f32]] {
//!     let slice_of_ptrs = std::slice::from_raw_parts(ptr, subslices);
//!     reusable_slice.from_iter_mut(
//!         slice_of_ptrs
//!             .iter()
//!             .map(|&ptr| std::slice::from_raw_parts_mut(ptr, subslice_length)),
//!     )
//! }
//! ```
//!
//! Note that `ptr` is supposed to be valid for the lifetime `'a` and
//! all other pointers are supposed to be valid for the lifetime `'b`.
//! The caller has to make sure that this is actually the case.
//! This is one of the many reasons why this function is marked as `unsafe`!

#![warn(rust_2018_idioms)]
#![warn(single_use_lifetimes)]
#![deny(missing_docs)]

use std::mem;

/// Reusable slice of references.
///
/// Any method that adds references (`&T` or `&mut T`) to a `Slice`
/// borrows it mutably (using `&mut self`) and
/// returns a slice of references (`&[&T]` or `&mut [&mut T]`, respectively).
/// The references are only available while the returned slice is alive.
/// After that, the `Slice` is logically empty again and can be reused
/// (using references with a possibly different lifetime).
///
/// *See also the [crate-level documentation](crate).*
pub struct Slice<T: 'static + ?Sized> {
    /// Pointer and capacity of a `Vec`.
    ///
    /// The `'static` lifetime is just a placeholder,
    /// more appropriate lifetimes are applied later.
    ///
    /// NB: `length` is ignored, see `Drop` implementation.
    vec_data: Option<(*mut &'static T, usize)>,
}

impl<T: 'static + ?Sized> Slice<T> {
    /// Creates a new reusable slice with capacity `0`.
    pub fn new() -> Slice<T> {
        Slice::with_capacity(0)
    }

    /// Creates a new reusable slice with the given capacity.
    pub fn with_capacity(capacity: usize) -> Slice<T> {
        let mut v = mem::ManuallyDrop::new(Vec::<&T>::with_capacity(capacity));
        let ptr: *mut &T = v.as_mut_ptr();
        Slice {
            vec_data: Some((ptr, v.capacity())),
        }
    }

    /// Returns a slice of references that has been filled by the given function.
    ///
    /// The function `f()` receives an *empty* [`Vec`] and is supposed to fill it
    /// with the desired number of references and return the modified `Vec`
    /// (or an entirely different one if desired!).
    /// The references in the returned `Vec` are then returned in a slice of references.
    ///
    /// The capacity of the argument passed to `f()` can be obtained with
    /// [`Slice::capacity()`] beforehand, or with [`Vec::capacity()`]
    /// within the function.
    ///
    /// # Examples
    ///
    /// Note that the lifetime `'b` used to fill the `Vec` in `f()`
    /// is the same as the lifetime of the returned references.
    /// This means that even though the lifetimes between invocations
    /// are allowed to be incompatible, the lifetimes used within one invocation
    /// are still checked by the compiler with all of its dreaded rigor.
    ///
    /// For example, the following code does not compile because the lifetime of one of the
    /// references used in `f()` is too short:
    ///
    /// ```compile_fail
    /// use rsor::Slice;
    ///
    /// let mut myslice = Slice::<str>::new();
    /// let strings = {
    ///     let inner_scope = String::from("inner scope is too short-lived");
    ///     let static_str = "static &str is OK";
    ///     myslice.fill(|mut v| {
    ///         v.push(&inner_scope);
    ///         v.push(static_str);
    ///         v
    ///     })
    /// };
    /// ```
    ///
    /// This is how the compiler phrases it:
    ///
    /// ```text
    /// error[E0597]: `inner_scope` does not live long enough
    ///    |
    /// 4  | let strings = {
    ///    |     ------- borrow later stored here
    /// ...
    /// 7  |     myslice.fill(|mut v| {
    ///    |                  ------- value captured here
    /// 8  |         v.push(&inner_scope);
    ///    |                 ^^^^^^^^^^^ borrowed value does not live long enough
    /// ...
    /// 12 | };
    ///    | - `inner_scope` dropped here while still borrowed
    ///
    /// For more information about this error, try `rustc --explain E0597`.
    /// ```
    ///
    /// To avoid this error, we have to use a longer lifetime, for example like this:
    ///
    /// ```
    /// # use rsor::Slice;
    /// let mut myslice = Slice::<str>::new();
    /// let same_scope = String::from("same scope is OK");
    /// let strings = {
    ///     let static_str = "static &str is OK";
    ///     myslice.fill(|mut v| {
    ///         v.push(&same_scope);
    ///         v.push(static_str);
    ///         v
    ///     })
    /// };
    /// assert_eq!(strings, ["same scope is OK", "static &str is OK"]);
    /// ```
    pub fn fill<'a, 'b, F>(&'a mut self, f: F) -> &'a [&'b T]
    where
        F: FnOnce(Vec<&'b T>) -> Vec<&'b T>,
    {
        let (ptr, capacity) = self.vec_data.take().unwrap();
        let mut v = unsafe { Vec::from_raw_parts(ptr as *mut &T, 0, capacity) };
        v = f(v); // NB: Re-allocation is possible, this might even return a different Vec!
        let v = mem::ManuallyDrop::new(v);
        let (ptr, length, capacity) = (v.as_ptr(), v.len(), v.capacity());
        let result = unsafe { std::slice::from_raw_parts(ptr, length) };
        self.vec_data = Some((ptr as *mut &T, capacity));
        result
    }

    /// Returns a slice of mutable references that has been filled by the given function.
    ///
    /// Same as [`fill()`](Slice::fill), but for mutable references.
    pub fn fill_mut<'a, 'b, F>(&'a mut self, f: F) -> &'a mut [&'b mut T]
    where
        F: FnOnce(Vec<&'b mut T>) -> Vec<&'b mut T>,
    {
        let (ptr, capacity) = self.vec_data.take().unwrap();
        let mut v = unsafe { Vec::from_raw_parts(ptr as *mut &mut T, 0, capacity) };
        v = f(v); // NB: Re-allocation is possible, this might even return a different Vec!
        let mut v = mem::ManuallyDrop::new(v);
        let (ptr, length, capacity) = (v.as_mut_ptr(), v.len(), v.capacity());
        let result = unsafe { std::slice::from_raw_parts_mut(ptr, length) };
        self.vec_data = Some((ptr as *mut &T, capacity));
        result
    }

    /// Returns a slice of references that has been filled by draining an iterator.
    pub fn from_iter<'a, 'b, I>(&'a mut self, iter: I) -> &'a [&'b T]
    where
        I: IntoIterator<Item = &'b T>,
    {
        self.fill(|mut v| {
            v.extend(iter.into_iter());
            v
        })
    }

    /// Returns a slice of mutable references that has been filled by draining an iterator.
    pub fn from_iter_mut<'a, 'b, I>(&'a mut self, iter: I) -> &'a mut [&'b mut T]
    where
        I: IntoIterator<Item = &'b mut T>,
    {
        self.fill_mut(|mut v| {
            v.extend(iter.into_iter());
            v
        })
    }

    /// Returns the number of references that can be used without reallocating.
    pub fn capacity(&self) -> usize {
        // NB: vec_data can only be None during `fill[_mut]()`, which has exclusive access.
        self.vec_data.unwrap().1
    }
}

impl<T: 'static + ?Sized> Default for Slice<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static + ?Sized> Drop for Slice<T> {
    fn drop(&mut self) {
        if let Some((ptr, capacity)) = self.vec_data {
            unsafe {
                // Length is assumed to be zero, there are no destructors to be run for references.
                Vec::from_raw_parts(ptr, 0, capacity);
            }
        }
    }
}

/// A `Slice` can be moved between threads.
///
/// However, it cannot be moved while it's in use (because it's borrowed).
/// When it's not in use, it doesn't contain any elements.
/// Therefore, we don't have to care about whether `T` implements `Send` and/or `Sync`.
///
/// # Examples
///
/// Despite [`std::rc::Rc`] decidedly not implementing [`Send`],
/// a `Slice<Rc<T>>` can be sent between threads:
///
/// ```
/// let myslice = rsor::Slice::<std::rc::Rc<i32>>::new();
///
/// std::thread::spawn(move || {
///     assert_eq!(myslice.capacity(), 0);
/// }).join().unwrap();
/// ```
unsafe impl<T: 'static + ?Sized> Send for Slice<T> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn local_variable() {
        let mut myslice = Slice::new();
        let mut number = 24;
        let slice = myslice.fill_mut(|mut v| {
            v.push(&mut number);
            v
        });
        *slice[0] = 42;
        assert_eq!(number, 42);
    }

    #[test]
    fn different_lifetimes() {
        let mut myslice = Slice::new();

        {
            let mut number = 7;
            let slice = myslice.fill_mut(|mut v| {
                v.push(&mut number);
                v
            });
            *slice[0] = 9;
            assert_eq!(number, 9);
        }

        {
            let mut number = Box::new(5);
            let slice = myslice.fill_mut(|mut v| {
                v.push(&mut *number);
                v
            });
            *slice[0] = 6;
            assert_eq!(*number, 6);
        }

        {
            let number = 4;
            let slice = myslice.fill(|mut v| {
                v.push(&number);
                v
            });
            assert_eq!(*slice[0], 4);
        }
    }

    #[test]
    fn fill() {
        let mut myslice = Slice::new();
        let data = vec![1, 2, 3, 4, 5, 6];
        let sos = myslice.fill(|mut v| {
            v.push(&data[0..2]);
            v.push(&data[2..4]);
            v.push(&data[4..6]);
            v
        });
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
    }

    #[test]
    fn fill_mut() {
        let mut myslice = Slice::new();
        let mut data = vec![1, 2, 3, 4, 5, 6];
        let sos = myslice.fill_mut(|mut v| {
            let (first, second) = data.split_at_mut(2);
            v.push(first);
            let (first, second) = second.split_at_mut(2);
            v.push(first);
            v.push(second);
            v
        });
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
    }

    #[test]
    fn from_nested_ptr() {
        let mut myslice = Slice::with_capacity(3);
        let v = vec![1, 2, 3, 4, 5, 6];

        // Assuming we have a slice of pointers with a known length:
        let ptrs = [v[0..2].as_ptr(), v[2..4].as_ptr(), v[4..6].as_ptr()];
        let length = 2;

        let sos = myslice.from_iter(
            ptrs.iter()
                .map(|&ptr| unsafe { std::slice::from_raw_parts(ptr, length) }),
        );
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
    }

    #[test]
    fn from_nested_ptr_mut() {
        let mut myslice = Slice::new();
        let mut v = vec![1, 2, 3, 4, 5, 6];

        // Assuming we have a slice of pointers with a known length:
        let ptrs = [
            v[0..2].as_mut_ptr(),
            v[2..4].as_mut_ptr(),
            v[4..6].as_mut_ptr(),
        ];
        let length = 2;

        let sos = myslice.from_iter_mut(
            ptrs.iter()
                .map(|&ptr| unsafe { std::slice::from_raw_parts_mut(ptr, length) }),
        );
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
        sos[1][0] = 30;
        sos[1][1] = 40;
        assert_eq!(sos, [[1, 2], [30, 40], [5, 6]]);
        assert_eq!(v[2..4], [30, 40]);
    }
}
