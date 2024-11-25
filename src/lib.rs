#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(not(feature = "bounded"), forbid(unsafe_code))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(clippy::type_complexity, unused_extern_crates)]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

pub use core::ops::Bound;

/// A memtable implementation based on unbounded `SkipList`.
#[cfg(feature = "unbounded")]
#[cfg_attr(docsrs, doc(cfg(feature = "unbounded")))]
pub mod unbounded;

/// A memtable implementation based on bounded ARENA-style `SkipList`.
#[cfg(feature = "bounded")]
#[cfg_attr(docsrs, doc(cfg(feature = "bounded")))]
pub mod bounded;
