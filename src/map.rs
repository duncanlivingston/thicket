//! Implementation of a maps, backed by a splay tree
#![warn(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;
use compact_str::CompactString;
use core::{cell::RefCell, cmp::Ordering, iter::FusedIterator};

use crate::util::Tree;

//-----------------------------------------------------------------------------------------------//

/// A simple map between keys and values, implemented using a splay tree.
#[derive(Clone)]
pub struct Map<K, V>
where
    K: Ord,
{
    tree: RefCell<Tree>,
    key_value: Vec<(K, V)>,
}

impl<K, V> Map<K, V>
where
    K: Ord,
{
    /// Constructor
    pub fn new() -> Map<K, V> {
        Map {
            tree: RefCell::new(Tree::new()),
            key_value: Vec::new(),
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize) -> Map<K, V> {
        Map {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_value: Vec::with_capacity(capacity),
        }
    }

    /// Get the number of key/value pairs in the `Map`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any key/value pairs in the `Map`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all key/value pairs from the `Map`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_value.truncate(0);
    }

    /// Reserves capacity for at least `additional` more key/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();

        debug_assert_eq!(self.key_value.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_value.reserve(required);
        }
    }

    /// Get a value by key.
    ///
    /// If the key is not in the tree then `None` is returned.
    pub fn get(&self, key: &K) -> Option<&V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_kv(key, &self.key_value);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_value[leaf].1)
    }

    /// Get a mutable referernce by key.
    ///
    /// If the key is not in the tree then `None` is returned - this function will not create a key
    /// if it does not exist. In this case use `set` instead.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_kv(key, &self.key_value);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&mut self.key_value[leaf].1)
    }

    /// Set a value by key.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the key to the top of
    /// the tree.
    pub fn set(&mut self, key: K, value: V) -> &(K, V) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_kv(&key, &self.key_value);
        tree.promote(leaf);

        if leaf == self.key_value.len() {
            self.key_value.push((key, value));
        } else {
            self.key_value[leaf] = (key, value);
        }

        &self.key_value[leaf]
    }

    /// Unset a value by key.
    ///
    /// If the key does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &K) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_kv(key, &self.key_value);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first key in the map
    pub fn first(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Get the last key in the map
    pub fn last(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the first key from the map
    pub fn pop_first(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the last key from the map
    pub fn pop_last(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Iterate over the key/value pairs in the `Map`
    pub fn iter(&self) -> MapIterator<'_, K, V> {
        let tree = &mut self.tree.borrow();
        MapIterator {
            map: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<K, V> Default for Map<K, V>
where
    K: Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, K, V> IntoIterator for &'a Map<K, V>
where
    K: Ord,
{
    type Item = &'a (K, V);
    type IntoIter = MapIterator<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K, V> FromIterator<(K, V)> for Map<K, V>
where
    K: Ord,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity(iter.size_hint().0);
        for (key, value) in iter {
            map.set(key, value);
        }
        map
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `Map`
pub struct MapIterator<'a, K, V>
where
    K: Ord,
{
    map: &'a Map<K, V>,
    leaf: usize,
    count: usize,
}

impl<'a, K, V> Iterator for MapIterator<'a, K, V>
where
    K: Ord,
{
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<&'a (K, V)> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.map.tree.borrow().next(self.leaf);
        self.count -= 1;

        Some(&self.map.key_value[leaf])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<K, V> FusedIterator for MapIterator<'_, K, V> where K: Ord {}

//-----------------------------------------------------------------------------------------------//

/// A simple map between strings and values, implemented using a splay tree.
///
/// This is specialised version of `Map` that stores keys as a string.
pub struct StringMap<V> {
    tree: RefCell<Tree>,
    key_value: Vec<(CompactString, V)>,
}

impl<V> StringMap<V> {
    /// Constructor
    pub fn new() -> StringMap<V> {
        StringMap {
            tree: RefCell::new(Tree::new()),
            key_value: Vec::new(),
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize) -> StringMap<V> {
        StringMap {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_value: Vec::with_capacity(capacity),
        }
    }

    /// Get the number of string/value pairs in the `StringMap`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any string/value pairs in the `StringMap`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all string/value pairs from the `StringMap`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_value.truncate(0);
    }

    /// Reserves capacity for at least `additional` more string/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();
        debug_assert_eq!(self.key_value.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_value.reserve(required);
        }
    }

    /// Get a value by string.
    ///
    /// If the string is not in the tree then `None` is returned.
    pub fn get(&self, key: &str) -> Option<&V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_sv(key, &self.key_value);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_value[leaf].1)
    }

    /// Get a mutable referernce by string.
    ///
    /// If the string is not in the tree then `None` is returned - this function will not create a
    /// string if it does not exist. In this case use `set` instead.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_sv(key, &self.key_value);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&mut self.key_value[leaf].1)
    }

    /// Set a value by string.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the string to the top
    /// of the tree.
    pub fn set(&mut self, key: &str, value: V) -> (&str, &V) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_sv(key, &self.key_value);
        tree.promote(leaf);

        if leaf == self.key_value.len() {
            self.key_value.push((CompactString::new(key), value));
        } else {
            self.key_value[leaf] = (CompactString::new(key), value);
        };

        let key_value = &self.key_value[leaf];
        (&key_value.0, &key_value.1)
    }

    /// Unset a value by string.
    ///
    /// If the string does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &str) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_sv(key, &self.key_value);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first string in the map
    pub fn first(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Get the last string in the map
    pub fn last(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the first string from the map
    pub fn pop_first(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the last key from the map
    pub fn pop_last(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Iterate over the string/value pairs in the `StringMap`
    pub fn iter(&self) -> StringMapIterator<'_, V> {
        let tree = &mut self.tree.borrow();
        StringMapIterator {
            map: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<V> Default for StringMap<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, V> IntoIterator for &'a StringMap<V> {
    type Item = (&'a str, &'a V);
    type IntoIter = StringMapIterator<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, V> FromIterator<(&'a str, V)> for StringMap<V> {
    fn from_iter<I: IntoIterator<Item = (&'a str, V)>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity(iter.size_hint().0);
        for (key, value) in iter {
            map.set(key, value);
        }
        map
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `StringMap`
pub struct StringMapIterator<'a, V> {
    map: &'a StringMap<V>,
    leaf: usize,
    count: usize,
}

impl<'a, V> Iterator for StringMapIterator<'a, V> {
    type Item = (&'a str, &'a V);

    fn next(&mut self) -> Option<(&'a str, &'a V)> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.map.tree.borrow().next(self.leaf);
        self.count -= 1;

        let key_value = &self.map.key_value[leaf];
        Some((&key_value.0, &key_value.1))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<V> FusedIterator for StringMapIterator<'_, V> {}

//-----------------------------------------------------------------------------------------------//

/// A simple map between keys and values, implemented using a splay tree.
///
/// This version allows a custom sorting function to be used.
#[derive(Clone)]
pub struct MapBy<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    tree: RefCell<Tree>,
    key_value: Vec<(K, V)>,
    compare: F,
}

impl<K, V, F> MapBy<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    /// Constructor
    pub fn new(compare: F) -> MapBy<K, V, F> {
        MapBy {
            tree: RefCell::new(Tree::new()),
            key_value: Vec::new(),
            compare,
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize, compare: F) -> MapBy<K, V, F> {
        MapBy {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_value: Vec::with_capacity(capacity),
            compare,
        }
    }

    /// Get the number of key/value pairs in the `Map`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any key/value pairs in the `Map`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all key/value pairs from the `Map`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_value.truncate(0);
    }

    /// Reserves capacity for at least `additional` more key/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();

        debug_assert_eq!(self.key_value.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_value.reserve(required);
        }
    }

    /// Get a value by key.
    ///
    /// If the key is not in the tree then `None` is returned.
    pub fn get(&self, key: &K) -> Option<&V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_kv_by(key, &self.key_value, &self.compare);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_value[leaf].1)
    }

    /// Get a mutable referernce by key.
    ///
    /// If the key is not in the tree then `None` is returned - this function will not create a key
    /// if it does not exist. In this case use `set` instead.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_kv_by(key, &self.key_value, &self.compare);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&mut self.key_value[leaf].1)
    }

    /// Set a value by key.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the key to the top of
    /// the tree.
    pub fn set(&mut self, key: K, value: V) -> &(K, V) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_kv_by(&key, &self.key_value, &self.compare);
        tree.promote(leaf);

        if leaf == self.key_value.len() {
            self.key_value.push((key, value));
        } else {
            self.key_value[leaf] = (key, value);
        }

        &self.key_value[leaf]
    }

    /// Unset a value by key.
    ///
    /// If the key does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &K) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_kv_by(key, &self.key_value, &self.compare);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first key in the map
    pub fn first(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Get the last key in the map
    pub fn last(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the first key from the map
    pub fn pop_first(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the last key from the map
    pub fn pop_last(&self) -> Option<(&K, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Iterate over the key/value pairs in the `Map`
    pub fn iter(&self) -> MapByIterator<'_, K, V, F> {
        let tree = &mut self.tree.borrow();
        MapByIterator {
            map: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<'a, K, V, F> IntoIterator for &'a MapBy<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    type Item = &'a (K, V);
    type IntoIter = MapByIterator<'a, K, V, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `MapBy`
pub struct MapByIterator<'a, K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    map: &'a MapBy<K, V, F>,
    leaf: usize,
    count: usize,
}

impl<'a, K, V, F> Iterator for MapByIterator<'a, K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    type Item = &'a (K, V);

    fn next(&mut self) -> Option<&'a (K, V)> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.map.tree.borrow().next(self.leaf);
        self.count -= 1;

        Some(&self.map.key_value[leaf])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<K, V, F> FusedIterator for MapByIterator<'_, K, V, F> where F: Fn(&K, &K) -> Ordering {}

//-----------------------------------------------------------------------------------------------//

/// A simple map between strings and values, implemented using a splay tree.
///
/// This is specialised version of `Map` that stores keys as a string and allows a custom sorting
/// function to be used.
pub struct StringMapBy<V, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    tree: RefCell<Tree>,
    key_value: Vec<(CompactString, V)>,
    compare: F,
}

impl<V, F> StringMapBy<V, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    /// Constructor
    pub fn new(compare: F) -> StringMapBy<V, F> {
        StringMapBy {
            tree: RefCell::new(Tree::new()),
            key_value: Vec::new(),
            compare,
        }
    }

    /// Constructor
    pub fn with_capacity(capacity: usize) -> StringMap<V> {
        StringMap {
            tree: RefCell::new(Tree::with_capacity(capacity)),
            key_value: Vec::with_capacity(capacity),
        }
    }

    /// Get the number of string/value pairs in the `StringMap`
    #[inline]
    pub fn count(&self) -> usize {
        self.tree.borrow().count()
    }

    /// Check if there are any string/value pairs in the `StringMap`
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.tree.borrow().is_empty()
    }

    /// Remove all string/value pairs from the `StringMap`
    pub fn clear(&mut self) {
        self.tree.borrow_mut().clear();
        self.key_value.truncate(0);
    }

    /// Reserves capacity for at least `additional` more string/value pairs
    pub fn reserve(&mut self, additional: usize) {
        let tree = &mut self.tree.borrow_mut();
        debug_assert_eq!(self.key_value.len(), tree.allocated_count());

        let required = tree.reserve(additional);
        if required > 0 {
            self.key_value.reserve(required);
        }
    }

    /// Get a value by string.
    ///
    /// If the string is not in the tree then `None` is returned.
    pub fn get(&self, key: &str) -> Option<&V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_sv_by(key, &self.key_value, &self.compare);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&self.key_value[leaf].1)
    }

    /// Get a mutable referernce by string.
    ///
    /// If the string is not in the tree then `None` is returned - this function will not create a
    /// string if it does not exist. In this case use `set` instead.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.get_sv_by(key, &self.key_value, &self.compare);
        if !leaf == 0 {
            return None;
        }

        tree.promote(leaf);
        Some(&mut self.key_value[leaf].1)
    }

    /// Set a value by string.
    ///
    /// `set` attempts to reconfigure the tree for future lookups by promoting the string to the top
    /// of the tree.
    pub fn set(&mut self, key: &str, value: V) -> (&str, &V) {
        let tree = &mut self.tree.borrow_mut();

        let leaf = tree.set_sv_by(key, &self.key_value, &self.compare);
        tree.promote(leaf);

        if leaf == self.key_value.len() {
            self.key_value.push((CompactString::new(key), value));
        } else {
            self.key_value[leaf] = (CompactString::new(key), value);
        };

        let key_value = &self.key_value[leaf];
        (&key_value.0, &key_value.1)
    }

    /// Unset a value by string.
    ///
    /// If the string does not exist, then this function has no effect.
    pub fn unset(&mut self, key: &str) {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.get_sv_by(key, &self.key_value, &self.compare);
        if !leaf != 0 {
            tree.unset(leaf);
        }
    }

    /// Get the first string in the map
    pub fn first(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Get the last string in the map
    pub fn last(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the first string from the map
    pub fn pop_first(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.first();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Pop the last key from the map
    pub fn pop_last(&self) -> Option<(&str, &V)> {
        let tree = &mut self.tree.borrow_mut();
        let leaf = tree.last();
        if !leaf == 0 {
            None
        } else {
            tree.promote(leaf);
            tree.unset(leaf);
            let key_value = &self.key_value[leaf];
            Some((&key_value.0, &key_value.1))
        }
    }

    /// Iterate over the string/value pairs in the `StringMap`
    pub fn iter(&self) -> StringMapByIterator<'_, V, F> {
        let tree = &mut self.tree.borrow();
        StringMapByIterator {
            map: self,
            leaf: tree.first(),
            count: tree.count(),
        }
    }
}

impl<'a, V, F> IntoIterator for &'a StringMapBy<V, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    type Item = (&'a str, &'a V);
    type IntoIter = StringMapByIterator<'a, V, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

//-----------------------------------------------------------------------------------------------//

/// Iterator over a `StringMap`
pub struct StringMapByIterator<'a, V, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    map: &'a StringMapBy<V, F>,
    leaf: usize,
    count: usize,
}

impl<'a, V, F> Iterator for StringMapByIterator<'a, V, F>
where
    F: Fn(&str, &str) -> Ordering,
{
    type Item = (&'a str, &'a V);

    fn next(&mut self) -> Option<(&'a str, &'a V)> {
        if !self.leaf == 0 {
            return None;
        }

        let leaf = self.leaf;
        self.leaf = self.map.tree.borrow().next(self.leaf);
        self.count -= 1;

        let key_value = &self.map.key_value[leaf];
        Some((&key_value.0, &key_value.1))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<V, F> FusedIterator for StringMapByIterator<'_, V, F> where F: Fn(&str, &str) -> Ordering {}

//-----------------------------------------------------------------------------------------------//

#[test]
// A very simple test of setting a map
fn test_map_0() {
    use alloc::{
        string::{String, ToString},
        vec,
    };

    let mut map = Map::new();

    map.set(5, "Five".to_string());
    map.set(1, "One".to_string());
    map.set(9, "Nine".to_string());

    debug_assert_eq!(map.get(&5), Some(&"Five".to_string()));
    debug_assert_eq!(map.get(&4), None);

    let v: Vec<(i32, String)> = map.iter().cloned().collect();
    debug_assert_eq!(
        v,
        vec![
            (1, "One".to_string()),
            (5, "Five".to_string()),
            (9, "Nine".to_string())
        ]
    );
}

#[test]
// A very simple test of setting a map
fn test_map_1() {
    use alloc::{
        string::{String, ToString},
        vec,
    };

    let mut map = Map::new();

    map.set("Five".to_string(), 5);
    map.set("One".to_string(), 1);
    map.set("Nine".to_string(), 9);

    debug_assert_eq!(map.get(&"Five".to_string()), Some(&5));
    debug_assert_eq!(map.get(&"Seven".to_string()), None);

    let v: Vec<(String, i32)> = map.iter().cloned().collect();
    debug_assert_eq!(
        v,
        vec![
            ("Five".to_string(), 5),
            ("Nine".to_string(), 9),
            ("One".to_string(), 1)
        ]
    );
}

#[test]
// A stress test with setting and getting
fn test_map_2() {
    use alloc::string::ToString;
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(1234567890);

    let mut map = Map::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        let value = key.to_string();
        map.set(key, value);
    }

    debug_assert_eq!(map.count(), COUNT);

    let mut rng = SmallRng::seed_from_u64(1234567890);

    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        let value = key.to_string();
        debug_assert_eq!(map.get(&key), Some(&value));
    }

    debug_assert_eq!(map.count(), COUNT);
}

#[test]
// A stress test with setting and popping from the start
fn test_map_3() {
    use alloc::string::ToString;
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(9876543210);

    let mut map = Map::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        let value = key.to_string();
        map.set(key, value);
    }

    debug_assert_eq!(map.count(), COUNT);

    for _ in 0..COUNT {
        let (key, value) = map.pop_first().unwrap();
        debug_assert_eq!(&key.to_string(), value);
    }

    debug_assert_eq!(map.count(), 0);
}

#[test]
// A stress test with setting and popping from the end
fn test_map_4() {
    use alloc::string::ToString;
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(9876543210);

    let mut map = Map::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        let value = key.to_string();
        map.set(key, value);
    }

    debug_assert_eq!(map.count(), COUNT);

    for _ in 0..COUNT {
        let (key, value) = map.pop_last().unwrap();
        debug_assert_eq!(&key.to_string(), value);
    }

    debug_assert_eq!(map.count(), 0);
}

#[test]
// A stress test with setting and unsetting
fn test_map_5() {
    use alloc::string::ToString;
    use rand::prelude::*;

    const COUNT: usize = 1000000;

    let mut rng = SmallRng::seed_from_u64(5678901234);

    let mut map = Map::new();
    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        let value = key.to_string();
        map.set(key, value);
    }

    debug_assert_eq!(map.count(), COUNT);

    let mut rng = SmallRng::seed_from_u64(5678901234);

    for _ in 0..COUNT {
        let key = rng.random_range(0..usize::MAX);
        map.unset(&key);
    }

    debug_assert_eq!(map.count(), 0);
}
