Reusable Slice of References
============================

* Crate: https://crates.io/crates/rsor
* Documentation: https://docs.rs/rsor

This crate can be used without the standard library (`#![no_std]`),
but the [alloc](https://doc.rust-lang.org/alloc/) crate is needed nevertheless.


Usage
-----

Add this to your `Cargo.toml`:

```toml
[dependencies]
rsor = "0.1"
```


Related Crates
--------------

* [vecstorage](https://crates.io/crates/vecstorage)
  solves the same problem as this crate.
  While it is more flexible in the types `T` it accepts,
  it also does fewer compile-time checks,
  and mismatched types can cause a runtime panic.


License
-------

MIT OR Apache-2.0
