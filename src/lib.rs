//! [![github]](https://github.com/duncanlivingston/thicket)&ensp;
//! [![crates-io]](https://crates.io/duncanlivingston/thicket)&ensp;
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//!
//! ## Introduction
//!
//! This crate implements a variety of collections based on binary trees, in particular splay trees.
//! Splay trees are a type of data structure that offers logarithmic time lookup for random access
//! of data. They are self-organising, in the sense that commonly accessed items with the tree send
//! to 'bubble' to the top so that future lookups of these items will be faster in the future.
//!
//! ## Benefits
//!
//!  The crate complements the standard `std::collection` routines, but provide the following
//! benefits:
//!
//! - Keys stored in the collections do not need to be hashable.
//! - Keys are sorted into an 'ascending' order within the collection by comparing keys pairwise.
//! - Keys in the collection do not need to implement `Clone`or `Copy`. Keys the support `Ord` can
//!   use `Map` or `Set`, etc, but if not a custom function can be supplied to compare keys using
//!   `MapBy` or `StringMapBy`, etc.
//! - The crate is small and `#![no_std]`.
//! - Copying and moving of keys are values is minimised. They are stored as (key, Value) pairs in a
//!   single array. They are moved when inserted and moved when the array is expanded, but otherwise
//!   do not move as the tree reconfigures around them. Once the array is large enough the memory is
//!   managed internally and when keys are removed that memory is recycled for future use.
//! - The storage of the (key, value) pair is separate to the storage of the structure of the tree.
//!   This has subtle benefits such as removing a (key, value) pair does not immediately remove them
//!   from strage. That means, for example that the `pop_first()` returns a reference `&(K, V)` not
//!   a value `(K, V)`.
//!
//! ## Contents
//!
//! The initial release of the `thicket` crate includes the following types
//!
//! <center>
//!
//! | Type          | Stores       | Sorts By  | Iterator              |
//! |:--------------|:-------------|:----------|-----------------------|
//! | `Map`         | Key/Value    | Ord       | `MapIterator`         |
//! | `Set`         | Key          | Ord       | `SetIterator`         |
//! | `StringMap`   | String/Value | Ord       | `StringMapIterator`   |
//! | `StringSet`   | String       | Ord       | `StringSetIterator`   |
//! | `MapBy`       | Key/Value    | Function  | `MapByIterator`       |
//! | `SetBy`       | Key          | Function  | `SetByIterator`       |
//! | `StringMapBy` | String/Value | Function  | `StringMapByIterator` |
//! | `StringSetBy` | String       | Function  | `StringSetByIterator` |
//!
//! </center>
//!
//! The crate exposes an additional type `util::Tree` that provides the foundation of the other
//! types. This can be thought of as a utility that manages a set of `usize` indices into an
//! external vector of data, without storing the vector itself. It is provided to support
//! development of additional collection types.

#![no_std]
#![warn(missing_docs)]

mod map;
mod set;
pub mod util;

pub use map::*;
pub use set::*;
