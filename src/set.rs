//! Implementation of a sets, backed by a splay tree
#![warn(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;
use compact_str::CompactString;
use core::{cell::RefCell, cmp::Ordering, iter::FusedIterator};

use crate::util::Tree;

//-----------------------------------------------------------------------------------------------//

/// A simple of keys, implemented using a splay tree.
#[derive(Clone)]
pub struct Set<K>
where
    K: Ord,
{
    tree: RefCell<Tree>,
    key_slice: Vec<K>,
}

impl<K> Set<K>
where
    K: Ord,
{
    /// Constructor
    pub fn new() -> Set<K> {
        Set {
            tree: RefCell::new(Tree::new()),
            key_slice: Vec::new(),
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize) -> Set<K> {
        Set {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_slice: Vec::with_capacity(capacity),
        }
    }

    /// Get the number of key/value pairs in the `Set`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any key/value pairs in the `Set`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all key/value pairs from the `Set`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_slice.truncate(0);
    }

    /// Reserves capacity for at least `additional` more key/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();

        debug_assert_eq!(self.key_slice.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_slice.reserve(required);
        }
    }

    /// Get a value by key.
    ///
    /// If the key is not in the tree then `None` is returned.
    pub fn get(&self, key: &K) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_k(key, &self.key_slice);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_slice[leaf])
    }

    /// Set a value by key.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the key to the top of
    /// the tree.
    pub fn set(&mut self, key: K) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_k(&key, &self.key_slice);
        tree.promote(leaf);

        if leaf == self.key_slice.len() {
            self.key_slice.push(key);
        } else {
            self.key_slice[leaf] = key;
        }
    }

    /// Unset a value by key.
    ///
    /// If the key does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &K) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_k(key, &self.key_slice);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first key in the set
    pub fn first(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Get the last key in the set
    pub fn last(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the first key from the set
    pub fn pop_first(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the last key from the set
    pub fn pop_last(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Iterate over the key/value pairs in the `Set`
    pub fn iter(&self) -> SetIterator<'_, K> {
        let tree = &mut self.tree.borrow();
        SetIterator {
            set: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<K> Default for Set<K>
where
    K: Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, K> IntoIterator for &'a Set<K>
where
    K: Ord,
{
    type Item = &'a K;
    type IntoIter = SetIterator<'a, K>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K> FromIterator<K> for Set<K>
where
    K: Ord,
{
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut set = Self::with_capacity(iter.size_hint().0);
        for key in iter {
            set.set(key);
        }
        set
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `Set`
pub struct SetIterator<'a, K>
where
    K: Ord,
{
    set: &'a Set<K>,
    leaf: usize,
    count: usize,
}

impl<'a, K> Iterator for SetIterator<'a, K>
where
    K: Ord,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.set.tree.borrow().next(self.leaf);
        self.count -= 1;

        Some(&self.set.key_slice[leaf])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<K> FusedIterator for SetIterator<'_, K> where K: Ord {}

//-----------------------------------------------------------------------------------------------//

/// A simple set of strings, implemented using a splay tree.
///
/// This is specialised version of `Set` that stores keys as a string.
pub struct StringSet {
    tree: RefCell<Tree>,
    key_slice: Vec<CompactString>,
}

impl StringSet {
    /// Constructor
    pub fn new() -> StringSet {
        StringSet {
            tree: RefCell::new(Tree::new()),
            key_slice: Vec::new(),
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize) -> StringSet {
        StringSet {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_slice: Vec::with_capacity(capacity),
        }
    }

    /// Get the number of string/value pairs in the `StringSet`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any string/value pairs in the `StringSet`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all string/value pairs from the `StringSet`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_slice.truncate(0);
    }

    /// Reserves capacity for at least `additional` more string/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();
        debug_assert_eq!(self.key_slice.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_slice.reserve(required);
        }
    }

    /// Get a value by string.
    ///
    /// If the string is not in the tree then `None` is returned.
    pub fn get(&self, key: &str) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_s(key, &self.key_slice);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_slice[leaf])
    }

    /// Set a value by string.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the string to the top
    /// of the tree.
    pub fn set(&mut self, key: &str) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_s(key, &self.key_slice);
        tree.promote(leaf);

        if leaf == self.key_slice.len() {
            self.key_slice.push(CompactString::new(key));
        } else {
            self.key_slice[leaf] = CompactString::new(key);
        };
    }

    /// Unset a value by string.
    ///
    /// If the string does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &str) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_s(key, &self.key_slice);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first string in the set
    pub fn first(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Get the last string in the set
    pub fn last(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the first string from the set
    pub fn pop_first(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the last key from the set
    pub fn pop_last(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Iterate over the string/value pairs in the `StringSet`
    pub fn iter(&self) -> StringSetIterator<'_> {
        let tree = &mut self.tree.borrow();
        StringSetIterator {
            set: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl Default for StringSet {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> IntoIterator for &'a StringSet {
    type Item = &'a str;
    type IntoIter = StringSetIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> FromIterator<&'a str> for StringSet {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut set = Self::with_capacity(iter.size_hint().0);
        for key in iter {
            set.set(key);
        }
        set
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `StringSet`
pub struct StringSetIterator<'a> {
    set: &'a StringSet,
    leaf: usize,
    count: usize,
}

impl<'a> Iterator for StringSetIterator<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.set.tree.borrow().next(self.leaf);
        self.count -= 1;

        Some(&self.set.key_slice[leaf])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl FusedIterator for StringSetIterator<'_> {}

//-----------------------------------------------------------------------------------------------//

/// A simple set of keys, implemented using a splay tree.
///
/// This version allows a custom sorting function to be used.
#[derive(Clone)]
pub struct SetBy<K, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    tree: RefCell<Tree>,
    key_slice: Vec<K>,
    compare: F,
}

impl<K, F> SetBy<K, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    /// Constructor
    pub fn new(compare: F) -> SetBy<K, F> {
        SetBy {
            tree: RefCell::new(Tree::new()),
            key_slice: Vec::new(),
            compare,
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize, compare: F) -> SetBy<K, F> {
        SetBy {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_slice: Vec::with_capacity(capacity),
            compare,
        }
    }

    /// Get the number of key/value pairs in the `Set`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any key/value pairs in the `Set`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all key/value pairs from the `Set`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_slice.truncate(0);
    }

    /// Reserves capacity for at least `additional` more key/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();

        debug_assert_eq!(self.key_slice.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_slice.reserve(required);
        }
    }

    /// Get a value by key.
    ///
    /// If the key is not in the tree then `None` is returned.
    pub fn get(&self, key: &K) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_k_by(key, &self.key_slice, &self.compare);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_slice[leaf])
    }

    /// Set a value by key.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the key to the top of
    /// the tree.
    pub fn set(&mut self, key: K) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_k_by(&key, &self.key_slice, &self.compare);
        tree.promote(leaf);

        if leaf == self.key_slice.len() {
            self.key_slice.push(key);
        } else {
            self.key_slice[leaf] = key;
        }
    }

    /// Unset a value by key.
    ///
    /// If the key does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &K) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_k_by(key, &self.key_slice, &self.compare);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first key in the set
    pub fn first(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Get the last key in the set
    pub fn last(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the first key from the set
    pub fn pop_first(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the last key from the set
    pub fn pop_last(&self) -> Option<&K> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Iterate over the key/value pairs in the `Set`
    pub fn iter(&self) -> SetByIterator<'_, K, F> {
        let tree = &mut self.tree.borrow();
        SetByIterator {
            set: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<'a, K, F> IntoIterator for &'a SetBy<K, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    type Item = &'a K;
    type IntoIter = SetByIterator<'a, K, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `SetBy`
pub struct SetByIterator<'a, K, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    set: &'a SetBy<K, F>,
    leaf: usize,
    count: usize,
}

impl<'a, K, F> Iterator for SetByIterator<'a, K, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.set.tree.borrow().next(self.leaf);
        self.count -= 1;

        Some(&self.set.key_slice[leaf])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<K, F> FusedIterator for SetByIterator<'_, K, F> where F: Fn(&K, &K) -> Ordering {}

//-----------------------------------------------------------------------------------------------//

/// A simple set of strings, implemented using a splay tree.
///
/// This is specialised version of `Set` that stores keys as a string and allows a custom sorting
/// function to be used.
pub struct StringSetBy<F>
where
    F: Fn(&str, &str) -> Ordering,
{
    tree: RefCell<Tree>,
    key_slice: Vec<CompactString>,
    compare: F,
}

impl<F> StringSetBy<F>
where
    F: Fn(&str, &str) -> Ordering,
{
    /// Constructor
    pub fn new(compare: F) -> StringSetBy<F> {
        StringSetBy {
            tree: RefCell::new(Tree::new()),
            key_slice: Vec::new(),
            compare,
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize) -> StringSet {
        StringSet {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_slice: Vec::with_capacity(capacity),
        }
    }

    /// Get the number of string/value pairs in the `StringSet`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any string/value pairs in the `StringSet`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all string/value pairs from the `StringSet`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_slice.truncate(0);
    }

    /// Reserves capacity for at least `additional` more string/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();
        debug_assert_eq!(self.key_slice.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_slice.reserve(required);
        }
    }

    /// Get a value by string.
    ///
    /// If the string is not in the tree then `None` is returned.
    pub fn get(&self, key: &str) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_s_by(key, &self.key_slice, &self.compare);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_slice[leaf])
    }

    /// Set a value by string.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the string to the top
    /// of the tree.
    pub fn set(&mut self, key: &str) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_s_by(key, &self.key_slice, &self.compare);
        tree.promote(leaf);

        if leaf == self.key_slice.len() {
            self.key_slice.push(CompactString::new(key));
        } else {
            self.key_slice[leaf] = CompactString::new(key);
        };
    }

    /// Unset a value by string.
    ///
    /// If the string does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &str) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_s_by(key, &self.key_slice, &self.compare);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first string in the set
    pub fn first(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Get the last string in the set
    pub fn last(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the first string from the set
    pub fn pop_first(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Pop the last key from the set
    pub fn pop_last(&self) -> Option<&str> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            Some(&self.key_slice[leaf])
        }
    }

    /// Iterate over the string/value pairs in the `StringSet`
    pub fn iter(&self) -> StringSetByIterator<'_, F> {
        let tree = &mut self.tree.borrow();
        StringSetByIterator {
            set: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<'a, F> IntoIterator for &'a StringSetBy<F>
where
    F: Fn(&str, &str) -> Ordering,
{
    type Item = &'a str;
    type IntoIter = StringSetByIterator<'a, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `StringSet`
pub struct StringSetByIterator<'a, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    set: &'a StringSetBy<F>,
    leaf: usize,
    count: usize,
}

impl<'a, F> Iterator for StringSetByIterator<'a, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.set.tree.borrow().next(self.leaf);
        self.count -= 1;

        Some(&self.set.key_slice[leaf])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<F> FusedIterator for StringSetByIterator<'_, F> where F: Fn(&str, &str) -> Ordering {}

//-----------------------------------------------------------------------------------------------//

#[test]
// A very simple test of setting a set
fn test_set_0() {
    use alloc::vec;

    let mut set = Set::new();

    set.set(5);
    set.set(1);
    set.set(9);

    debug_assert_eq!(set.get(&5), Some(&5));
    debug_assert_eq!(set.get(&4), None);

    let v: Vec<i32> = set.iter().cloned().collect();
    debug_assert_eq!(v, vec![1, 5, 9]);
}

#[test]
// A very simple test of setting a set
fn test_set_1() {
    use alloc::{
        string::{String, ToString},
        vec,
    };

    let mut set = Set::new();

    set.set("Five".to_string());
    set.set("One".to_string());
    set.set("Nine".to_string());

    debug_assert_eq!(set.get(&"Five".to_string()), Some(&"Five".to_string()));
    debug_assert_eq!(set.get(&"Seven".to_string()), None);

    let v: Vec<String> = set.iter().cloned().collect();
    debug_assert_eq!(
        v,
        vec!["Five".to_string(), "Nine".to_string(), "One".to_string()]
    );
}

#[test]
// A stress test with setting and getting
fn test_set_2() {
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(1234567890);

    let mut set = Set::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        set.set(key);
    }

    debug_assert_eq!(set.count(), COUNT);

    let mut rng = SmallRng::seed_from_u64(1234567890);

    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        debug_assert_eq!(set.get(&key), Some(&key));
    }

    debug_assert_eq!(set.count(), COUNT);
}

#[test]
// A stress test with setting and popping from the start
fn test_set_3() {
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(9876543210);

    let mut set = Set::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        set.set(key);
    }

    debug_assert_eq!(set.count(), COUNT);

    for _ in 0..COUNT {
        let _ = set.pop_first().unwrap();
    }

    debug_assert_eq!(set.count(), 0);
}

#[test]
// A stress test with setting and popping from the end
fn test_set_4() {
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(9876543210);

    let mut set = Set::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        set.set(key);
    }

    debug_assert_eq!(set.count(), COUNT);

    for _ in 0..COUNT {
        let _ = set.pop_last().unwrap();
    }

    debug_assert_eq!(set.count(), 0);
}

#[test]
// A stress test with setting and unsetting
fn test_set_5() {
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(5678901234);

    let mut set = Set::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        set.set(key);
    }

    debug_assert_eq!(set.count(), COUNT);

    let mut rng = SmallRng::seed_from_u64(5678901234);

    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        set.unset(&key);
    }

    debug_assert_eq!(set.count(), 0);
}
