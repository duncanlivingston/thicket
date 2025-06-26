//! Utility types to support self balancing binary splay trees

#![warn(missing_docs)]

extern crate alloc;
use alloc::vec::Vec;

use core::{cmp::Ordering, fmt::Display, ops::Deref};

//-----------------------------------------------------------------------------------------------//

// A leaf in a splay tree
#[derive(Clone)]
struct Leaf {
    parent: usize,
    left: usize,
    right: usize,
}

//-----------------------------------------------------------------------------------------------//

/// A tree of integer leaves
#[derive(Clone)]
pub struct Tree {
    leaf: Vec<Leaf>,
    root: usize,
    recycle: usize,
    count: usize,
}

impl Tree {
    /// Construct an empty tree
    pub fn new() -> Tree {
        Tree {
            leaf: Vec::new(),
            root: !0,
            recycle: !0,
            count: 0,
        }
    }

    /// Construct an empty tree, pre-allocating a given capacity
    pub fn with_capacity(capacity: usize) -> Tree {
        Tree {
            leaf: Vec::with_capacity(capacity),
            root: !0,
            recycle: !0,
            count: 0,
        }
    }

    /// Get the number of leaves in the tree
    #[inline]
    pub fn count(&self) -> usize {
        self.count
    }

    /// Get the number of recycled leaves in the splay tree
    #[inline]
    pub fn recycle_count(&self) -> usize {
        self.leaf.len() - self.count
    }

    /// Get the current allocated size of the splay tree. This is the current `count` plus the
    /// `recycle_count`. Note that this is not necessarily the same as the allocated capacity.
    #[inline]
    pub fn allocated_count(&self) -> usize {
        self.leaf.len()
    }

    /// Remove all keys from the splay tree
    pub fn clear(&mut self) {
        self.leaf.truncate(0);
        self.root = !0;
        self.recycle = !0;
        self.count = 0;
    }

    /// Get the number of keys in the splay tree
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Reserves capacity for at least `additional` more leaves
    ///
    /// Note the implementation is subtle. The tree may already have have some room that has been
    /// allocated then 'recycled', and this space is subtracted from the `additional` requested.
    /// This function returns the total amount of additional element storage that was required
    /// (if any), which is useful when implementing more complex types.
    pub fn reserve(&mut self, additional: usize) -> usize {
        let recycle_count = self.recycle_count();
        if additional > recycle_count {
            let required = additional - recycle_count;
            self.leaf.reserve(required);
            required
        } else {
            0
        }
    }

    /// Get a leaf by key
    ///
    /// If the key is not found, then `usize::MAX` is returned. If the slice of keys is not sorted
    /// properly according to the binary tree, then the results are undedined.
    pub fn get_k<K: Ord>(&self, key: &K, key_slice: &[K]) -> usize {
        get_k(&self.leaf, self.root, key, key_slice)
    }

    /// Insert a leaf by key
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of keys is not sorted properly according to the binary tree, then the results
    /// are undedined.
    pub fn set_k<K: Ord>(&mut self, key: &K, key_slice: &[K]) -> usize {
        match locate_k(&self.leaf, self.root, key, key_slice) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Get a leaf by string
    ///
    /// If the string is not found, then `usize::MAX` is returned. If the slice of strings is not
    /// sorted properly according to the binary tree, then the results are undedined.
    pub fn get_s<S: Deref<Target = str>>(&self, key: &str, key_slice: &[S]) -> usize {
        get_s(&self.leaf, self.root, key, key_slice)
    }

    /// Insert a leaf by string
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of strings is not sorted properly according to the binary tree, then the
    /// results are undedined.
    pub fn set_s<S: Deref<Target = str>>(&mut self, key: &str, key_slice: &[S]) -> usize {
        match locate_s(&self.leaf, self.root, key, key_slice) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Get a leaf by key/value pair
    ///
    /// If the key is not found, then `usize::MAX` is returned. If the slice of key/value pairs is
    /// not sorted properly according to the binary tree, then the results are undedined.
    pub fn get_kv<K: Ord, V>(&self, key: &K, key_value: &[(K, V)]) -> usize {
        get_kv(&self.leaf, self.root, key, key_value)
    }

    /// Insert a leaf by key/value pair
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of key/value pairs is not sorted properly according to the binary tree,
    /// then the results are undedined.
    pub fn set_kv<K: Ord, V>(&mut self, key: &K, key_value: &[(K, V)]) -> usize {
        match locate_kv(&self.leaf, self.root, key, key_value) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Get a leaf by string/value pair
    ///
    /// If the key is not found, then `usize::MAX` is returned. If the slice of string/value pairs
    /// is not sorted properly according to the binary tree, then the results are undedined.
    pub fn get_sv<S: Deref<Target = str>, V>(&self, key: &str, key_value: &[(S, V)]) -> usize {
        get_sv(&self.leaf, self.root, key, key_value)
    }

    /// Insert a leaf by string/value pair
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of string/value pairs is not sorted properly according to the binary tree,
    /// then the results are undedined.
    pub fn set_sv<S: Deref<Target = str>, V>(&mut self, key: &str, key_value: &[(S, V)]) -> usize {
        match locate_sv(&self.leaf, self.root, key, key_value) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    ////////////////. HERE

    /// Get a leaf by key
    ///
    /// If the key is not found, then `usize::MAX` is returned. If the slice of keys is not sorted
    /// properly according to the binary tree, then the results are undedined.
    pub fn get_k_by<K, F>(&self, key: &K, key_slice: &[K], compare: F) -> usize
    where
        F: Fn(&K, &K) -> Ordering,
    {
        get_k_by(&self.leaf, self.root, key, key_slice, compare)
    }

    /// Insert a leaf by key
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of keys is not sorted properly according to the binary tree, then the results
    /// are undedined.
    pub fn set_k_by<K, F>(&mut self, key: &K, key_slice: &[K], compare: F) -> usize
    where
        F: Fn(&K, &K) -> Ordering,
    {
        match locate_k_by(&self.leaf, self.root, key, key_slice, compare) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Get a leaf by string
    ///
    /// If the string is not found, then `usize::MAX` is returned. If the slice of strings is not
    /// sorted properly according to the binary tree, then the results are undedined.
    pub fn get_s_by<S: Deref<Target = str>, F>(
        &self,
        key: &str,
        key_slice: &[S],
        compare: F,
    ) -> usize
    where
        F: Fn(&str, &str) -> Ordering,
    {
        get_s_by(&self.leaf, self.root, key, key_slice, compare)
    }

    /// Insert a leaf by string
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of strings is not sorted properly according to the binary tree, then the
    /// results are undedined.
    pub fn set_s_by<S: Deref<Target = str>, F>(
        &mut self,
        key: &str,
        key_slice: &[S],
        compare: F,
    ) -> usize
    where
        F: Fn(&str, &str) -> Ordering,
    {
        match locate_s_by(&self.leaf, self.root, key, key_slice, compare) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Get a leaf by key/value pair
    ///
    /// If the key is not found, then `usize::MAX` is returned. If the slice of key/value pairs is
    /// not sorted properly according to the binary tree, then the results are undedined.
    pub fn get_kv_by<K, V, F>(&self, key: &K, key_value: &[(K, V)], compare: F) -> usize
    where
        F: Fn(&K, &K) -> Ordering,
    {
        get_kv_by(&self.leaf, self.root, key, key_value, compare)
    }

    /// Insert a leaf by key/value pair
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of key/value pairs is not sorted properly according to the binary tree,
    /// then the results are undedined.
    pub fn set_kv_by<K, V, F>(&mut self, key: &K, key_value: &[(K, V)], compare: F) -> usize
    where
        F: Fn(&K, &K) -> Ordering,
    {
        match locate_kv_by(&self.leaf, self.root, key, key_value, compare) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Get a leaf by string/value pair
    ///
    /// If the key is not found, then `usize::MAX` is returned. If the slice of string/value pairs
    /// is not sorted properly according to the binary tree, then the results are undedined.
    pub fn get_sv_by<S: Deref<Target = str>, V, F>(
        &self,
        key: &str,
        key_value: &[(S, V)],
        compare: F,
    ) -> usize
    where
        F: Fn(&str, &str) -> Ordering,
    {
        get_sv_by(&self.leaf, self.root, key, key_value, compare)
    }

    /// Insert a leaf by string/value pair
    ///
    /// The new leaf created by this operation is returned. Note that this may be a 'recycled' value
    /// that has previously been of removed, on a new leaf value that is the next in the ascending
    /// sequence that has not been used before. This method does not promote the inserted leaf to
    /// the root automatically, it is left to the calling function to decide if this is appropriate.
    /// If the slice of string/value pairs is not sorted properly according to the binary tree,
    /// then the results are undedined.
    pub fn set_sv_by<S: Deref<Target = str>, V, F>(
        &mut self,
        key: &str,
        key_value: &[(S, V)],
        compare: F,
    ) -> usize
    where
        F: Fn(&str, &str) -> Ordering,
    {
        match locate_sv_by(&self.leaf, self.root, key, key_value, compare) {
            Location::Found(leaf) => leaf,
            Location::Root => {
                let leaf = self.alloc(!0);
                self.root = leaf;
                leaf
            }
            Location::Left(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].left = leaf;
                leaf
            }
            Location::Right(parent) => {
                let leaf = self.alloc(parent);
                self.leaf[parent].right = leaf;
                leaf
            }
        }
    }

    /// Unset a leaf
    ///
    /// The leaf is deleted and added to the 'recycle bin' for possible future reallocation. This is
    /// the only metho of `Tree` that possibly needs to automnatically apply a large-scale
    /// restructuring of the tree using a splay. This may be required if the leaf is tricky to
    /// disconnect from it's neighbouring leaves.
    pub fn unset(&mut self, leaf: usize) {
        if let Some(root) = prune(&mut self.leaf, leaf) {
            self.root = root;
        }
        self.free(leaf);
    }

    /// Get the first leaf in the tree
    #[inline]
    pub fn first(&self) -> usize {
        first(&self.leaf, self.root)
    }

    /// Get the last leaf in the tree
    #[inline]
    pub fn last(&self) -> usize {
        last(&self.leaf, self.root)
    }

    /// Get the previous leaf in the tree
    #[inline]
    pub fn prev(&self, leaf: usize) -> usize {
        prev(&self.leaf, leaf)
    }

    /// Get the next leaf in the tree
    #[inline]
    pub fn next(&self, leaf: usize) -> usize {
        next(&self.leaf, leaf)
    }

    // Allocate and initialise a new leaf
    fn alloc(&mut self, parent: usize) -> usize {
        // Increase the leaf count
        self.count += 1;

        // Recycle an old leaf
        let leaf = self.recycle;
        if !leaf != 0 {
            let l = &mut self.leaf[leaf];
            self.recycle = l.parent;
            l.parent = parent;
            l.left = !0;
            l.right = !0;

            return leaf;
        }

        // Inititialise a new one
        let leaf = self.leaf.len();
        self.leaf.push(Leaf {
            parent,
            left: !0,
            right: !0,
        });

        // Return the new leaf
        leaf
    }

    // Free a leaf and add it to the recycle queue
    fn free(&mut self, leaf: usize) {
        // Decrease the leaf count
        self.count -= 1;

        // Recycle the leaf
        self.leaf[leaf].parent = self.recycle;
        self.recycle = leaf;
    }

    /// Promote a leaf to be root
    ///
    /// The order of the leaves is unchanged, however, this method reconfigures the tree to
    /// manipulate the target leaf to be the root. Repeated application of the splay should enable
    /// log(N) time searches for random lookups. Note than in general, insertion and removal
    /// operations do not automatically trigger a splay - this is left to the discretion of the
    /// calling function.
    pub(crate) fn promote(&mut self, leaf: usize) {
        promote(&mut self.leaf, leaf);
        self.root = leaf;
    }

    // Debug tests
    #[cfg(debug_assertions)]
    #[allow(dead_code)]
    fn check(&self) {
        check_tree(&self.leaf, self.root);
        debug_assert_eq!(check_count(&self.leaf, self.root), self.count);
    }
}

impl Default for Tree {
    fn default() -> Self {
        Tree::new()
    }
}

impl Display for Tree {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[ ")?;
        let mut leaf = self.first();
        while !leaf != 0 {
            write!(f, "{leaf} ")?;
            leaf = self.next(leaf);
        }
        write!(f, "]")?;
        Ok(())
    }
}

//-----------------------------------------------------------------------------------------------//

// IMPLEMENTATION NOTE
//
// The functions below are low level. They are not 'unsafe' in the Rust sense, but they implement
// very low level operations. Use with caution.

enum Location {
    Found(usize),
    Root,
    Left(usize),
    Right(usize),
}

// Get a leaf in a tree
fn get_k<K: Ord>(leaf: &[Leaf], mut x: usize, key: &K, key_slice: &[K]) -> usize {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match key.cmp(&key_slice[x]) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_k<K: Ord>(leaf: &[Leaf], mut x: usize, key: &K, key_slice: &[K]) -> Location {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match key.cmp(&key_slice[x]) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_s<S: Deref<Target = str>>(leaf: &[Leaf], mut x: usize, key: &str, key_slice: &[S]) -> usize {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match key.cmp(&key_slice[x]) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_s<S: Deref<Target = str>>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_slice: &[S],
) -> Location {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match key.cmp(&key_slice[x]) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_kv<K: Ord, V>(leaf: &[Leaf], mut x: usize, key: &K, key_value: &[(K, V)]) -> usize {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match key.cmp(&key_value[x].0) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_kv<K: Ord, V>(leaf: &[Leaf], mut x: usize, key: &K, key_value: &[(K, V)]) -> Location {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match key.cmp(&key_value[x].0) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_sv<S: Deref<Target = str>, V>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_value: &[(S, V)],
) -> usize {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match key.cmp(&key_value[x].0) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_sv<S: Deref<Target = str>, V>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_value: &[(S, V)],
) -> Location {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match key.cmp(&key_value[x].0) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_k_by<K, F>(leaf: &[Leaf], mut x: usize, key: &K, key_slice: &[K], compare: F) -> usize
where
    F: Fn(&K, &K) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match compare(key, &key_slice[x]) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_k_by<K, F>(leaf: &[Leaf], mut x: usize, key: &K, key_slice: &[K], compare: F) -> Location
where
    F: Fn(&K, &K) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match compare(key, &key_slice[x]) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_s_by<S: Deref<Target = str>, F>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_slice: &[S],
    compare: F,
) -> usize
where
    F: Fn(&str, &str) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match compare(key, &key_slice[x]) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_s_by<S: Deref<Target = str>, F>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_slice: &[S],
    compare: F,
) -> Location
where
    F: Fn(&str, &str) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match compare(key, &key_slice[x]) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_kv_by<K, V, F>(
    leaf: &[Leaf],
    mut x: usize,
    key: &K,
    key_value: &[(K, V)],
    compare: F,
) -> usize
where
    F: Fn(&K, &K) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match compare(key, &key_value[x].0) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_kv_by<K, V, F>(
    leaf: &[Leaf],
    mut x: usize,
    key: &K,
    key_value: &[(K, V)],
    compare: F,
) -> Location
where
    F: Fn(&K, &K) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match compare(key, &key_value[x].0) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Get a leaf in a tree
fn get_sv_by<S: Deref<Target = str>, V, F>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_value: &[(S, V)],
    compare: F,
) -> usize
where
    F: Fn(&str, &str) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    loop {
        if !x == 0 {
            return !0;
        }

        match compare(key, &key_value[x].0) {
            Ordering::Equal => {
                return x;
            }
            Ordering::Less => x = leaf[x].left,
            Ordering::Greater => x = leaf[x].right,
        }
    }
}

// Locate a leaf in a tree, or if not found identify where to insert it
fn locate_sv_by<S: Deref<Target = str>, V, F>(
    leaf: &[Leaf],
    mut x: usize,
    key: &str,
    key_value: &[(S, V)],
    compare: F,
) -> Location
where
    F: Fn(&str, &str) -> Ordering,
{
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    // First leaf is a special case
    if !x == 0 {
        return Location::Root;
    }

    loop {
        match compare(key, &key_value[x].0) {
            Ordering::Equal => return Location::Found(x),
            Ordering::Less => {
                let y = leaf[x].left;
                if !y == 0 {
                    return Location::Left(x);
                }
                x = y;
            }
            Ordering::Greater => {
                let y = leaf[x].right;
                if !y == 0 {
                    return Location::Right(x);
                }
                x = y;
            }
        }
    }
}

// Promote a leaf to the root of a tree
//
// This low-level function manipulates the binary tree, to move a leaf to be the root. It does this
// by repeated application of 'single' and 'double rotations. It is the responsibility of the
// caller to store the new root. Promotion is a the key mechnism that enables splay trees to
// achieve amortise time access.
fn promote(leaf: &mut [Leaf], x: usize) {
    // Check we aren't already at the root
    if !x == 0 || !leaf[x].parent == 0 {
        return;
    }

    // Repeatedly rotate until `x` is the root
    loop {
        let y = leaf[x].parent;
        if !leaf[y].parent == 0 {
            let b;

            if leaf[y].left == x {
                b = leaf[x].right;
                leaf[x].right = y;
                leaf[y].left = b;
            } else {
                debug_assert_eq!(leaf[y].right, x);

                b = leaf[x].left;
                leaf[x].left = y;
                leaf[y].right = b;
            }

            leaf[x].parent = !0;
            leaf[y].parent = x;

            if !b != 0 {
                leaf[b].parent = y;
            }

            // Finished
            return;
        }

        let z = leaf[y].parent;
        let e = leaf[z].parent;

        let b;
        let c;

        if leaf[y].left == x {
            b = leaf[x].right;
            leaf[x].right = y;
            if leaf[z].left == y {
                c = leaf[y].right;
                leaf[y].right = z;
                leaf[y].left = b;
                leaf[z].left = c;
                leaf[z].parent = y;
            } else {
                debug_assert_eq!(leaf[z].right, y);
                c = leaf[x].left;
                leaf[x].left = z;
                leaf[y].left = b;
                leaf[z].right = c;
                leaf[z].parent = x;
            }
        } else {
            debug_assert_eq!(leaf[y].right, x);

            b = leaf[x].left;
            leaf[x].left = y;
            if leaf[z].right == y {
                c = leaf[y].left;
                leaf[y].left = z;
                leaf[y].right = b;
                leaf[z].right = c;
                leaf[z].parent = y;
            } else {
                debug_assert_eq!(leaf[z].left, y);
                c = leaf[x].right;
                leaf[x].right = z;
                leaf[y].right = b;
                leaf[z].left = c;
                leaf[z].parent = x;
            }
        }

        leaf[x].parent = e;
        leaf[y].parent = x;

        if !b != 0 {
            leaf[b].parent = y;
        }

        if !c != 0 {
            leaf[c].parent = z;
        }

        if !e != 0 {
            if leaf[e].left == z {
                leaf[e].left = x;
            } else {
                debug_assert_eq!(leaf[e].right, z);
                leaf[e].right = x;
            }
        } else {
            // Finished
            return;
        }
    }
}

// Remove a leaf that has at least one free child connection
//
// On average, there is a 50% chance that any leaf in a tree will have one child free, in which
// case it can be removed easily. However, if it has two children the tree must be reconfigured.
// This is achieved by promoting either the previous or next leaf.
//
// This low level function removes a leaf assuming that the tree has already been manipulated so
// that at least one of it's children are free. Note that this function does not modify the pruned
// leaf, not free any memory associated with it, it just modifies the surrounding leaves.
//
// If the root is changed by this operation then Some(root) is returned, otherwise the root is
// unchanged.
fn prune(leaf: &mut [Leaf], x: usize) -> Option<usize> {
    debug_assert!(!x != 0);

    let y = leaf[x].parent;
    let a = leaf[x].left;
    let b = leaf[x].right;

    if !a == 0 {
        if !b != 0 {
            leaf[b].parent = y;
        }

        return if !y == 0 {
            Some(b)
        } else {
            if leaf[y].left == x {
                leaf[y].left = b;
            } else {
                debug_assert_eq!(leaf[y].right, x);
                leaf[y].right = b;
            }
            None
        };
    }

    if !b == 0 {
        leaf[a].parent = y;

        return if !y == 0 {
            Some(a)
        } else {
            if leaf[y].left == x {
                leaf[y].left = a;
            } else {
                debug_assert_eq!(leaf[y].right, x);
                leaf[y].right = a;
            }
            None
        };
    }

    let z = prev(leaf, x);
    promote(leaf, z);

    debug_assert_ne!(leaf[x].parent, !0);
    debug_assert_eq!(leaf[x].left, !0);
    debug_assert_ne!(leaf[x].right, !0);

    let y = leaf[x].parent;
    let b = leaf[x].right;

    leaf[b].parent = y;

    if leaf[y].left == x {
        leaf[y].left = b;
    } else {
        debug_assert_eq!(leaf[y].right, x);
        leaf[y].right = b;
    }

    Some(z)
}

// Get the root leaf (the top-most)
//
// Note that this function is provided for completeness and for debugging. It is expected that
// operations on trees will start at a root and propogate downwards, so a leaf shouldn't need to
// work upwards to a root.
#[allow(dead_code)]
fn root(leaf: &[Leaf], mut x: usize) -> usize {
    if !x == 0 {
        return !0;
    }

    loop {
        let y = leaf[x].parent;
        if !y == 0 {
            return x;
        }
        x = y;
    }
}

// Get the first leaf (the right-most)
fn first(leaf: &[Leaf], mut x: usize) -> usize {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    if !x == 0 {
        return !0;
    }

    loop {
        let y = leaf[x].left;
        if !y == 0 {
            return x;
        }
        x = y;
    }
}

// Get the last leaf (the right-most)
fn last(leaf: &[Leaf], mut x: usize) -> usize {
    // `x` should be a root
    debug_assert!(!x == 0 || leaf[x].parent == !0);

    if !x == 0 {
        return !0;
    }

    loop {
        let y = leaf[x].right;
        if !y == 0 {
            return x;
        }
        x = y;
    }
}

// Get the logical predecessor to a leaf
fn prev(leaf: &[Leaf], mut x: usize) -> usize {
    let mut y = leaf[x].left;
    if !y != 0 {
        loop {
            let z = leaf[y].right;
            if !z == 0 {
                return y;
            }
            y = z;
        }
    }

    loop {
        let y = leaf[x].parent;
        if !y == 0 {
            return !0;
        }
        if leaf[y].right == x {
            return y;
        }
        debug_assert_eq!(leaf[y].left, x);
        x = y;
    }
}

// Get the logical successor to a leaf
fn next(leaf: &[Leaf], mut x: usize) -> usize {
    let mut y = leaf[x].right;
    if !y != 0 {
        loop {
            let z = leaf[y].left;
            if !z == 0 {
                return y;
            }
            y = z;
        }
    }

    loop {
        let y = leaf[x].parent;
        if !y == 0 {
            return !0;
        }
        if leaf[y].left == x {
            return y;
        }
        debug_assert_eq!(leaf[y].right, x);
        x = y;
    }
}

//-----------------------------------------------------------------------------------------------//

// DEBUG : Check the tree structure
#[cfg(debug_assertions)]
fn check_tree(leaf: &[Leaf], root: usize) {
    // Check we are starting at the root
    debug_assert!(!root == 0 || leaf[root].parent == !0);

    // Iterate over leaves and check each one
    let mut x = first(leaf, root);

    while !x != 0 {
        let y = leaf[x].left;
        let z = leaf[x].right;

        if !y != 0 {
            debug_assert_eq!(x, leaf[y].parent);
        }

        if !z != 0 {
            debug_assert_eq!(x, leaf[z].parent);
        }

        x = next(leaf, x);
    }
}

// DEBUG : Check the leaf counts
#[cfg(debug_assertions)]
fn check_count(leaf: &[Leaf], root: usize) -> usize {
    // Count leaves (forwards)
    let mut x = first(leaf, root);
    let mut count_f = 0;

    while !x != 0 {
        count_f += 1;
        x = next(leaf, x);
    }

    // Count leaves (backwards)
    x = last(leaf, root);
    let mut count_b = 0;

    while !x != 0 {
        count_b += 1;
        x = prev(leaf, x);
    }

    debug_assert_eq!(count_f, count_b);

    // Return the count
    count_f
}

// DEBUG : Check the key order
#[cfg(debug_assertions)]
#[allow(dead_code)]
fn check_k<K: Ord>(leaf: &[Leaf], root: usize, key_slice: &[K]) {
    // Check we are starting at the root
    debug_assert!(!root == 0 || leaf[root].parent == !0);

    // Iterate over leaves and check each one
    let mut x = first(leaf, root);
    if !x == 0 {
        return;
    }

    let mut y = next(leaf, x);
    while !y != 0 {
        debug_assert!(key_slice[x] < key_slice[y]);
        x = y;
        y = next(leaf, y);
    }
}

// DEBUG : Check the key order
#[cfg(debug_assertions)]
#[allow(dead_code)]
fn check_kv<K: Ord, V>(leaf: &[Leaf], root: usize, key_value: &[(K, V)]) {
    // Check we are starting at the root
    debug_assert!(!root == 0 || leaf[root].parent == !0);

    // Iterate over leaves and check each one
    let mut x = first(leaf, root);
    if !x == 0 {
        return;
    }

    let mut y = next(leaf, x);
    while !y != 0 {
        debug_assert!(key_value[x].0 < key_value[y].0);
        x = y;
        y = next(leaf, y);
    }
}
