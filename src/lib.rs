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
//! * If we don't care about allocating memory at each invocation,
//!   a fresh [`Vec<&T>`](Vec) can be used each time,
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
//! let mut reusable_slice = Slice::<str>::with_capacity(2);
//!
//! {
//!     let one = String::from("one");
//!     let two = String::from("two");
//!
//!     let strings = reusable_slice.fill(|mut v| {
//!         v.push(&one);
//!         v.push(&two);
//!         v
//!     });
//!     print_slice(strings);
//! }
//!
//! let three = String::from("three");
//!
//! let strings = reusable_slice.fill(|mut v| {
//!     v.push(&three);
//!     v
//! });
//! print_slice(strings);
//! assert_eq!(reusable_slice.capacity(), 2);
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
//! If a "list of lists" (e.g. something like a `Vec<Vec<T>>`) is given,
//! it can be turned into a slice of slices with
//! [`Slice::from_refs()`] (returning `&[&[T]]`) or
//! [`Slice::from_muts()`] (returning `&mut [&mut [T]]`).
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
//!
//! # Deeper Nesting
//!
//! The motivation for creating this crate was to enable *slices of slices*,
//! as shown in the examples above.
//! However, it turns out that it is possible to have deeper nesting, for example
//! *slices of slices of slices*:
//!
//! ```
//! use rsor::Slice;
//!
//! let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
//! let mut level0 = Slice::with_capacity(6);
//! let mut level1 = Slice::with_capacity(2);
//! let sosos = level1.from_iter(level0.from_iter(data.chunks(2)).chunks(3));
//! assert_eq!(
//!     sosos,
//!     [[[1, 2], [3, 4], [5, 6]], [[7, 8], [9, 10], [11, 12]]]
//! );
//! assert_eq!(level0.capacity(), 6);
//! assert_eq!(level1.capacity(), 2);
//! ```
//!
//! For each level of nesting, a separate [`Slice`] is needed.
//! The above example uses a `Slice<[T]>` for the innermost level and
//! a `Slice<[&[T]]>` for the outer level.
//! The resulting slice has the type `&[&[&[T]]]`.

#![warn(rust_2018_idioms)]
#![warn(single_use_lifetimes)]
#![deny(missing_docs)]

use std::mem::ManuallyDrop;
use std::ptr::NonNull;

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
pub struct Slice<T: ?Sized> {
    /// Pointer and capacity of a `Vec`.
    ///
    /// We want to store `&T` and/or `&mut T` elements with different lifetimes,
    /// but dynamically changing lifetimes are not supported by Rust
    /// (because they cannot be verified at compile time).
    /// To avoid exposing any lifetime at all, we hide the actual reference type
    /// from the compiler by storing a pointer to a pointer instead of a pointer to a reference.
    ///
    /// We use `NonNull` to enable null pointer optimization.
    ///
    /// NB: `length` is ignored, see `Drop` implementation.
    vec_data: Option<(NonNull<*const T>, usize)>,
}

impl<T: ?Sized> Drop for Slice<T> {
    fn drop(&mut self) {
        if let Some((ptr, capacity)) = self.vec_data {
            unsafe {
                // Length is assumed to be zero, there are no destructors to be run for references.
                Vec::from_raw_parts(ptr.as_ptr(), 0, capacity);
            }
        }
    }
}

impl<T: ?Sized> Slice<T> {
    /// Creates a new reusable slice with capacity `0`.
    pub fn new() -> Slice<T> {
        Slice::with_capacity(0)
    }

    /// Creates a new reusable slice with the given capacity.
    pub fn with_capacity(capacity: usize) -> Slice<T> {
        let mut v = ManuallyDrop::new(Vec::with_capacity(capacity));
        // Safety: Pointer in `Vec` is guaranteed to be non-null.
        let ptr = unsafe { NonNull::new_unchecked(v.as_mut_ptr()) };
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
    /// let mut reusable_slice = Slice::<str>::new();
    /// let strings = {
    ///     let inner_scope = String::from("inner scope is too short-lived");
    ///     let static_str = "static &str is OK";
    ///     reusable_slice.fill(|mut v| {
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
    /// 7  |     reusable_slice.fill(|mut v| {
    ///    |                         ------- value captured here
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
    /// let mut reusable_slice = Slice::<str>::new();
    /// let same_scope = String::from("same scope is OK");
    /// let strings = {
    ///     let static_str = "static &str is OK";
    ///     reusable_slice.fill(|mut v| {
    ///         v.push(&same_scope);
    ///         v.push(static_str);
    ///         v
    ///     })
    /// };
    /// assert_eq!(strings, ["same scope is OK", "static &str is OK"]);
    /// ```
    ///
    /// Yet another contrived example, this time to show that
    /// the lifetimes `'a` and `'b` can be different:
    ///
    /// ```
    /// use rsor::Slice;
    ///
    /// let data = 'a';
    /// let outer_reference = {
    ///     let mut reusable_slice = Slice::new();
    ///     let chars = reusable_slice.fill(|mut v| {
    ///         v.push(&data);
    ///         v
    ///     });
    ///     chars[0]
    /// };
    /// assert_eq!(*outer_reference, 'a');
    /// ```
    ///
    /// Note that the returned value `chars` has the type `&'a [&'b char]`,
    /// where `'a` is the lifetime of the inner scope, while the lifetime `'b`
    /// is valid until the end of the example.
    /// This is why `outer_reference` (with lifetime `'b`) can still be accessed
    /// when `reusable_slice` and `chars` (with lifetime `'a`) have already gone out of scope.
    pub fn fill<'a, 'b, F>(&'a mut self, f: F) -> &'a [&'b T]
    where
        F: FnOnce(Vec<&'b T>) -> Vec<&'b T>,
    {
        let (ptr, capacity) = self.vec_data.take().unwrap();
        let ptr = ptr.cast::<&T>().as_ptr();
        let v = unsafe { Vec::from_raw_parts(ptr, 0, capacity) };
        let v = f(v); // NB: Re-allocation is possible, this might even return a different Vec!
        let mut v = ManuallyDrop::new(v);
        // Safety: Pointer in `Vec` is guaranteed to be non-null.
        let ptr = unsafe { NonNull::new_unchecked(v.as_mut_ptr()) };
        self.vec_data = Some((ptr.cast(), v.capacity()));
        unsafe { std::slice::from_raw_parts(v.as_ptr(), v.len()) }
    }

    /// Returns a slice of mutable references that has been filled by the given function.
    ///
    /// Same as [`fill()`](Slice::fill), but for mutable references.
    pub fn fill_mut<'a, 'b, F>(&'a mut self, f: F) -> &'a mut [&'b mut T]
    where
        F: FnOnce(Vec<&'b mut T>) -> Vec<&'b mut T>,
    {
        let (ptr, capacity) = self.vec_data.take().unwrap();
        let ptr = ptr.cast::<&mut T>().as_ptr();
        let v = unsafe { Vec::from_raw_parts(ptr, 0, capacity) };
        let v = f(v); // NB: Re-allocation is possible, this might even return a different Vec!
        let mut v = ManuallyDrop::new(v);
        // Safety: Pointer in `Vec` is guaranteed to be non-null.
        let ptr = unsafe { NonNull::new_unchecked(v.as_mut_ptr()) };
        self.vec_data = Some((ptr.cast(), v.capacity()));
        unsafe { std::slice::from_raw_parts_mut(v.as_mut_ptr(), v.len()) }
    }

    /// Returns a slice of references that has been filled by draining an iterator.
    ///
    /// *See the [crate-level documentation](crate#common-use-cases) for examples.*
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
    ///
    /// *See the [crate-level documentation](crate#common-use-cases) for examples.*
    pub fn from_iter_mut<'a, 'b, I>(&'a mut self, iter: I) -> &'a mut [&'b mut T]
    where
        I: IntoIterator<Item = &'b mut T>,
    {
        self.fill_mut(|mut v| {
            v.extend(iter.into_iter());
            v
        })
    }

    /// Returns a slice of references given a list of things that implement [`AsRef<T>`].
    ///
    /// # Examples
    ///
    /// Many things implement [`AsRef<T>`], for example [`Box<T>`]:
    ///
    /// ```
    /// use rsor::Slice;
    ///
    /// let boxes = vec![Box::new(10), Box::new(20)];
    /// let mut reusable_slice = Slice::new();
    /// assert_eq!(reusable_slice.from_refs(&boxes), [&10, &20]);
    /// ```
    ///
    /// [`String`]s have multiple [`AsRef`] implementations:
    /// `AsRef<str>` and `AsRef<[u8]>` (and even more!):
    ///
    /// ```
    /// # use rsor::Slice;
    /// let strings = vec![String::from("one"), String::from("two")];
    /// let mut reusable_slice1 = Slice::<str>::new();
    /// let mut reusable_slice2 = Slice::<[u8]>::new();
    /// assert_eq!(reusable_slice1.from_refs(&strings), strings);
    /// assert_eq!(reusable_slice2.from_refs(&strings), [b"one", b"two"]);
    /// ```
    ///
    /// A list of [`Vec`]s (or boxed slices etc.) can be turned into
    /// a *slice of slices* (`&[&[T]]`) by using a `Slice<[T]>`:
    ///
    /// ```
    /// # use rsor::Slice;
    /// let vecs = vec![vec![1.0, 2.0, 3.0], vec![4.0, 5.0, 6.0]];
    /// let mut reusable_slice = Slice::new();
    /// assert_eq!(reusable_slice.from_refs(&vecs), vecs);
    /// ```
    pub fn from_refs<'a, 'b, R>(&'a mut self, refs: &'b [R]) -> &'a [&'b T]
    where
        R: AsRef<T> + 'b,
    {
        self.fill(move |mut v| {
            v.extend(refs.iter().map(AsRef::as_ref));
            v
        })
    }

    /// Returns a mutable slice of references given a list of things that implement [`AsMut<T>`].
    ///
    /// This can be used like [`from_refs()`](Slice::from_refs),
    /// but this time with mutable references:
    ///
    /// ```
    /// use rsor::Slice;
    ///
    /// let mut boxes = vec![Box::new(10), Box::new(20)];
    /// let mut reusable_slice = Slice::new();
    /// let mut_slice = reusable_slice.from_muts(&mut boxes);
    /// *mut_slice[1] = 30;
    /// assert_eq!(boxes, [Box::new(10), Box::new(30)]);
    /// ```
    ///
    /// ```
    /// # use rsor::Slice;
    /// let mut strings = vec![String::from("one"), String::from("two")];
    /// let mut reusable_slice = Slice::<str>::new();
    /// let mut_slice = reusable_slice.from_muts(&mut strings);
    /// mut_slice[1].make_ascii_uppercase();
    /// assert_eq!(strings, ["one", "TWO"]);
    /// ```
    ///
    /// ```
    /// # use rsor::Slice;
    /// let mut vecs = vec![vec![1.0, 2.0, 3.0], vec![4.0, 5.0, 6.0]];
    /// let mut reusable_slice = Slice::<[f32]>::new();
    /// let mut_slice = reusable_slice.from_muts(&mut vecs);
    /// mut_slice[1][2] += 4.0;
    /// assert_eq!(vecs, [[1.0, 2.0, 3.0], [4.0, 5.0, 10.0]]);
    /// ```
    pub fn from_muts<'a, 'b, M>(&'a mut self, muts: &'b mut [M]) -> &'a mut [&'b mut T]
    where
        M: AsMut<T> + 'b,
    {
        self.fill_mut(move |mut v| {
            v.extend(muts.iter_mut().map(AsMut::as_mut));
            v
        })
    }

    /// Returns the number of references that can be used without reallocating.
    pub fn capacity(&self) -> usize {
        // NB: vec_data can only be None during `fill[_mut]()`, which has exclusive access.
        self.vec_data.unwrap().1
    }
}

impl<T: ?Sized> Default for Slice<T> {
    fn default() -> Self {
        Self::new()
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
/// let reusable_slice = rsor::Slice::<std::rc::Rc<i32>>::new();
///
/// std::thread::spawn(move || {
///     assert_eq!(reusable_slice.capacity(), 0);
/// }).join().unwrap();
/// ```
unsafe impl<T: ?Sized> Send for Slice<T> {}

/// A `&Slice` can be shared between threads.
///
/// However, a reference can only be taken when the `Slice` is not in use.
unsafe impl<T: ?Sized> Sync for Slice<T> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn local_variable() {
        let mut reusable_slice = Slice::new();
        let mut number = 24;
        let slice = reusable_slice.fill_mut(|mut v| {
            v.push(&mut number);
            v
        });
        *slice[0] = 42;
        assert_eq!(number, 42);
    }

    #[test]
    fn different_lifetimes() {
        let mut reusable_slice = Slice::new();

        {
            let mut number = 7;
            let slice = reusable_slice.fill_mut(|mut v| {
                v.push(&mut number);
                v
            });
            *slice[0] = 9;
            assert_eq!(number, 9);
        }

        {
            let mut number = Box::new(5);
            let slice = reusable_slice.fill_mut(|mut v| {
                v.push(&mut *number);
                v
            });
            *slice[0] = 6;
            assert_eq!(*number, 6);
        }

        {
            let number = 4;
            let slice = reusable_slice.fill(|mut v| {
                v.push(&number);
                v
            });
            assert_eq!(*slice[0], 4);
        }
    }

    #[test]
    fn fill() {
        let mut reusable_slice = Slice::new();
        let data = vec![1, 2, 3, 4, 5, 6];
        let sos = reusable_slice.fill(|mut v| {
            v.push(&data[0..2]);
            v.push(&data[2..4]);
            v.push(&data[4..6]);
            v
        });
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
    }

    #[test]
    fn fill_mut() {
        let mut reusable_slice = Slice::new();
        let mut data = vec![1, 2, 3, 4, 5, 6];
        let sos = reusable_slice.fill_mut(|mut v| {
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
        let mut reusable_slice = Slice::with_capacity(3);
        let v = vec![1, 2, 3, 4, 5, 6];

        // Assuming we have a slice of pointers with a known length:
        let ptrs = [v[0..2].as_ptr(), v[2..4].as_ptr(), v[4..6].as_ptr()];
        let length = 2;

        let sos = reusable_slice.from_iter(
            ptrs.iter()
                .map(|&ptr| unsafe { std::slice::from_raw_parts(ptr, length) }),
        );
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
    }

    #[test]
    fn from_nested_ptr_mut() {
        let mut reusable_slice = Slice::new();
        let mut v = vec![1, 2, 3, 4, 5, 6];

        // Assuming we have a slice of pointers with a known length:
        let ptrs = [
            v[0..2].as_mut_ptr(),
            v[2..4].as_mut_ptr(),
            v[4..6].as_mut_ptr(),
        ];
        let length = 2;

        let sos = reusable_slice.from_iter_mut(
            ptrs.iter()
                .map(|&ptr| unsafe { std::slice::from_raw_parts_mut(ptr, length) }),
        );
        assert_eq!(sos, [[1, 2], [3, 4], [5, 6]]);
        sos[1][0] = 30;
        sos[1][1] = 40;
        assert_eq!(sos, [[1, 2], [30, 40], [5, 6]]);
        assert_eq!(v[2..4], [30, 40]);
    }

    /// Makes sure we use null pointer optimization.
    #[test]
    fn struct_size() {
        use std::mem::size_of;
        assert_eq!(size_of::<Slice<f32>>(), size_of::<&[f32]>());
    }
}
