// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

use std::{mem, slice, ptr};
use std::cmp::Ordering;
use rand::{thread_rng, Rng, ThreadRng};

use util::mempool::MemPool;
use util::atomic::{AtomicPointer, AtomicUsize};
use super::comparator::Comparator;


/// A lockless concurrent skiplist implementation. This is mostly
/// a direct translation from the CPP version.
///
/// Struct doc mostly copied from CPP version about concurrency:
///
/// Writes require external synchronization, most likely a mutex.
/// Reads require a guarantee that the SkipList will not be destroyed
/// while the read is in progress. Apart from that, reads progress
/// without any internal locking or synchronization.
///
/// Invariants:
///
/// (1) Allocated nodes are never deleted until the SkipList is
/// destroyed. This is trivially guaranteed by the code since we
/// never delete any skip list nodes.
///
/// (2) The contents of a Node except for the next/prev pointers are
/// immutable after the Node has been linked into the SkipList.
/// Only `insert()` modifies the list, and it is careful to initialize
/// a node and use release-stores to publish the nodes in one or
/// more lists.
///
pub struct SkipList<'a, K> where K: 'a {
  cmp: Box<Comparator<K>>,
  mem_pool: &'a MemPool,
  head: *mut Node<'a, K>,
  max_height: AtomicUsize,
  rng: ThreadRng
}

const MAX_HEIGHT: usize = 12;
const BRANCHING: u32 = 4; // 25% chance to reach next level

// TODO: `Default` is required here because `head` needs to
// be initialized with an uninteresting value. How to avoid this?
//
// This implementation uses raw pointers for list nodes. This is
// to avoid perf penalty (potentially by `RefCell` and `Rc`), and
// the need to allocate nodes from pre-allocated memory
// (see `Node::new_node()`).
// Because of the above, this struct should NEVER leak node pointers,
// to avoid memory leak.
//
impl<'a, K> SkipList<'a, K> where K: 'a, K: Default {
  /// Create a new skiplist that uses `cmp` to compare keys, and
  /// `mem_pool` to allocate memory.
  pub fn new(
    cmp: Box<Comparator<K>>,
    mem_pool: &'a MemPool,
  ) -> Self {
    let h = Node::new_node(mem_pool, K::default(), MAX_HEIGHT);
    let rng = thread_rng();
    Self {
      cmp: cmp,
      mem_pool: mem_pool,
      head: h,
      max_height: AtomicUsize::new(1),
      rng: rng
    }
  }

  /// Insert the `key` into this skiplist.
  /// The `key` should NOT already exist in the skiplist and the caller
  /// of this function needs to make sure that.
  pub fn insert(&mut self, key: K) {
    let mut prev = [ptr::null_mut(); MAX_HEIGHT];
    let x = self.find_greater_or_equal(&key, Some(&mut prev));

    assert!(x.is_null() || !self.equal(&key, Node::get_key(x)));

    let height = self.random_height();
    let max_height = self.max_height();
    if height > max_height {
      for i in max_height..height {
        prev[i] = self.head;
      }
      self.max_height.no_barrier_store(height);
    }

    let x = Node::new_node(self.mem_pool, key, height);
    unsafe {
      for i in 0..height {
        (*x).set_next(i, (*(prev[i])).next(i));
        (*(prev[i])).set_next(i, x);
      }
    }
  }

  /// Return true if this skiplist contains the `key`.
  /// False otherwise.
  pub fn contains(&self, key: &K) -> bool {
    let x = self.find_greater_or_equal(key, None);
    if x.is_null() {
      false
    } else {
      self.equal(key, Node::get_key(x))
    }
  }

  /// Generate a random height in the range of `[1, MAX_HEIGHT]`.
  fn random_height(&mut self) -> usize {
    let mut height = 1;
    while height < MAX_HEIGHT && self.rng.next_u32() % BRANCHING == 0 {
      height += 1;
    }
    assert!(height > 0);
    assert!(height <= MAX_HEIGHT);
    height
  }

  /// Check whether `key` is after the key (greater in terms of ordering)
  /// in node `n`, using the comparator associated with this skiplist.
  /// If `n` is `None`, then it is treated as infinity.
  ///
  /// Return true if `key` is greater than `n`'s key. False otherwise.
  fn key_is_after(&self, key: &K, n: *mut Node<'a, K>) -> bool {
    if n.is_null() {
      false
    } else {
      match self.cmp.compare(key, Node::get_key(n)) {
          Ordering::Greater => true,
          _ => false
      }
    }
  }

  /// Find a key that is equal or greater than the input `key`.
  /// If `prev` is set, this will also populate all the previous links
  /// before the node where `key` should be.
  ///
  /// Return the node in this skiplist that is equal or greater than
  /// the `key`, or `null` if no such key exist in the list.
  fn find_greater_or_equal(
    &self,
    key: &K,
    mut prev: Option<&mut [*mut Node<'a, K>]>
  ) -> *mut Node<'a, K> {
    let mut x = self.head;
    let mut level = self.max_height() - 1;
    loop {
      let next = unsafe {
        (*x).next(level as usize)
      };
      if self.key_is_after(key, next) {
        // Keep searching in the list
        x = next;
      } else {
        if let Some(ref mut p) = prev {
          p[level as usize] = x;
        }
        if level == 0 {
          return next;
        } else {
          level -= 1;
        }
      }
    }
  }

  /// Return the last node in the list, or `head` if the list is empty.
  fn find_last(&self) -> *mut Node<'a, K> {
    let mut x = self.head;
    let mut level = self.max_height() - 1;
    loop {
      let next = unsafe {
        (*x).next(level as usize)
      };
      if next.is_null() {
        if level == 0 {
          return x
        } else {
          level -= 1;
        }
      } else {
        x = next;
      }
    }
  }

  /// Return the last node whose key is less than `key`, or `head` if
  /// there is no such node.
  fn find_less_than(&self, key: &K) -> *mut Node<'a, K> {
    let mut x = self.head;
    let mut level = self.max_height() - 1;
    loop {
      let next = unsafe {
        (*x).next(level as usize)
      };
      if next.is_null() || self.greater_or_equal(Node::get_key(next), key) {
        if level == 0 {
          return x
        } else {
          level -= 1;
        }
      } else {
        x = next;
      }
    }
  }

  #[inline(always)]
  fn equal(&self, k1: &K, k2: &K) -> bool {
    self.cmp.compare(k1, k2) == Ordering::Equal
  }

  #[inline(always)]
  fn greater_or_equal(&self, k1: &K, k2: &K) -> bool {
    match self.cmp.compare(k1, k2) {
      Ordering::Equal | Ordering::Greater => true,
      _ => false
    }
  }

  /// Return the maximum height in this skiplist.
  #[inline(always)]
  fn max_height(&self) -> usize {
    self.max_height.no_barrier_load()
  }
}

/// Internal node representation for the skiplist. Each node contains
/// a key and an vector of next links. The overall picture of a skiplist looks
/// like the following:
///
///    4       o------------------> null
///            |
///    3       o-----------> o----> null
///            |
///    2       o----> o----> o----> null
///            |
///    1       o----> o----> o----> null
///
///  level    head   node1   node2
///
/// In this case, `node1` has height = 2, and `node2` has height = 3.
/// `head` always has maximum height.
///
struct Node<'a, K> where K: 'a {
  // key for this node.
  key: K,

  // vector of next links, with length equal to the height of this node.
  next: &'a mut [AtomicPointer<Node<'a, K>>]
}

impl<'a, K> Node<'a, K> {
  /// Create a new node with `key` and `height`. The memory is allocated using
  /// `mem_pool`.
  ///
  /// Return a new unique node instance whose lifetime is the same as
  /// the `mem_pool`.
  pub fn new_node(
    mem_pool: &'a MemPool,
    key: K,
    height: usize
  ) -> *mut Node<'a, K> {
    let size = mem::size_of::<Node<'a, K>>() +
      mem::size_of::<AtomicPointer<Node<'a, K>>>() * height;
    let mut mem: &'a mut [u8] = mem_pool.alloc_aligned(size);
    let (left, right) = mem.split_at_mut(mem::size_of::<Node<'a, K>>());
    let node = left.as_mut_ptr() as *mut Node<'a, K>;
    let values = unsafe {
      slice::from_raw_parts_mut(
        right.as_mut_ptr() as *mut AtomicPointer<Node<'a, K>>,
        height
      )
    };
    unsafe {
      (*node).key = key;
      (*node).next = values;
    }
    node
  }

  /// Get the key for node `n`.
  /// REQUIRES: `n` is not null.
  #[inline(always)]
  pub fn get_key(n: *const Node<'a, K>) -> &K {
    assert!(!n.is_null());
    unsafe {
      &(*n).key
    }
  }

  /// Return the next node at level `n`. If there is no next
  /// at the position, return `None`.
  /// REQUIRES: `n` < height of this node
  #[inline(always)]
  pub fn next(&self, n: usize) -> *mut Node<'a, K> {
    assert!(n < self.next.len());
    self.next[n].acquire_load()
  }

  /// Set the next node at level `n` to be `node`.
  /// REQUIRES: `n` < height of this node
  #[inline(always)]
  pub fn set_next(&mut self, n: usize, node: *mut Node<'a, K>) {
    assert!(n < self.next.len());
    let ptr = AtomicPointer::new(node);
    self.next[n] = ptr;
  }
}

///
/// An iterator on a skiplist with ability to move forward and backward.
///
pub struct SkipListIterator<'a, 'b, K> where 'b: 'a, K: 'b + Default {
  list: &'a SkipList<'b, K>,
  node: *const Node<'b, K>
}

impl<'a, 'b, K> SkipListIterator<'a, 'b, K> where K: Default {
  #[inline(always)]
  pub fn new(list: &'a SkipList<'b, K>) -> Self {
    Self {
      list: list,
      node: ptr::null()
    }
  }

  /// Whether this iterator is in a valid state
  #[inline(always)]
  pub fn valid(&self) -> bool {
    !self.node.is_null()
  }

  /// Get the key at the current position.
  /// REQUIRES: `valid()` is true.
  #[inline(always)]
  pub fn key(&self) -> &K {
    assert!(self.valid());
    Node::get_key(self.node)
  }

  /// Move to the next entry.
  /// REQUIRES: `valid()` is true.
  #[inline(always)]
  pub fn next(&mut self) {
    assert!(self.valid());
    unsafe {
      self.node = (*self.node).next(0);
    }
  }

  /// Move to the previous entry.
  /// REQUIRES: `valid()` is true.
  #[inline(always)]
  pub fn prev(&mut self) {
    assert!(self.valid());
    self.node = self.list.find_less_than(Node::get_key(self.node));
    if self.node == self.list.head {
      self.node = ptr::null()
    }
  }

  /// Move to the first entry whose key >= `target`
  #[inline(always)]
  pub fn seek(&mut self, target: &K) {
    self.node = self.list.find_greater_or_equal(target, None);
  }

  /// Move to the first entry in this list.
  /// Final state of iterator is `valid()` iff list is not empty
  #[inline(always)]
  pub fn seek_to_first(&mut self) {
    self.node = unsafe {
      let h = self.list.head;
      (*h).next(0)
    };
  }

  /// Move to the last entry in this list.
  /// Final state of iterator is `valid()` iff list is not empty
  #[inline(always)]
  pub fn seek_to_last(&mut self) {
    self.node = self.list.find_last();
    if self.node == self.list.head {
      self.node = ptr::null();
    }
  }
}

#[cfg(test)]
mod tests {
  use std::collections::BTreeSet;
  use std::collections::Bound::{Included, Unbounded};

  use super::*;

  #[test]
  fn test_new_node() {
    let mem_pool = MemPool::new();

    let mut empty = Vec::new();
    let mut n0 = Node { key: 28, next: empty.as_mut_slice() };
    let n: &mut Node<i32> =
      unsafe {
        mem::transmute(Node::<i32>::new_node(&mem_pool, 42, 3))
      };
    n.set_next(0, &mut n0);

    assert_eq!(n.key, 42);
    assert_eq!(n.next.len(), 3);

    let nn0 = n.next(0);
    assert!(!nn0.is_null());
    let nn0: &mut Node<i32> = unsafe {
      mem::transmute(nn0)
    };
    assert_eq!(nn0.key, 28);
    assert_eq!(nn0.next.len(), 0);

    assert!(n.next(1).is_null());
    assert!(n.next(2).is_null());
  }

  #[test]
  fn test_empty() {
    let mem_pool = MemPool::new();
    let cmp = KeyComparator {};
    let list = SkipList::new(Box::new(cmp), &mem_pool);
    assert!(!list.contains(&10));

    let mut iter = SkipListIterator::new(&list);
    assert!(!iter.valid());
    iter.seek_to_first();
    assert!(!iter.valid());
    iter.seek(&100);
    assert!(!iter.valid());
    iter.seek_to_last();
    assert!(!iter.valid());
  }

  #[test]
  fn test_insert_and_lookup() {
    const N: i32 = 2000;
    const R: u32 = 5000;

    let mut keys: BTreeSet<u64> = BTreeSet::new();
    let cmp = KeyComparator {};
    let mem_pool = MemPool::new();
    let mut list = SkipList::new(Box::new(cmp), &mem_pool);
    let mut rnd = thread_rng();

    for _ in 0..N {
      let key = rnd.next_u32() % R;
      if keys.insert(key as u64) {
        list.insert(key as u64);
      }
    }

    for i in 0..R {
      if list.contains(&(i as u64)) {
        assert!(keys.contains(&(i as u64)));
      } else {
        assert!(!keys.contains(&(i as u64)));
      }
    }

    // simple iterator tests
    let mut iter = SkipListIterator::new(&list);
    assert!(!iter.valid());
    iter.seek(&0);
    assert!(iter.valid());
    assert_eq!(iter.key(), keys.iter().next().unwrap());

    iter.seek_to_first();
    assert!(iter.valid());
    assert_eq!(iter.key(), keys.iter().next().unwrap());

    iter.seek_to_last();
    assert!(iter.valid());
    assert_eq!(iter.key(), keys.iter().rev().next().unwrap());

    // forward iteration tests
    for i in 0..(R as u64) {
      let mut iter = SkipListIterator::new(&list);
      iter.seek(&i);

      let mut model_iter = keys.range((Included(i), Unbounded));
      for _ in 0..3 {
        match model_iter.next() {
          None => {
            assert!(!iter.valid());
            break;
          },
          Some(next) => {
            assert!(iter.valid());
            assert_eq!(iter.key(), next);
            iter.next();
          }
        }
      }
    }

    // backward iteration tests
    let mut iter = SkipListIterator::new(&list);
    iter.seek_to_last();

    let mut model_iter = keys.iter().rev();
    loop {
      match model_iter.next() {
        None => break,
        Some(next) => {
          assert!(iter.valid());
          assert_eq!(iter.key(), next);
          iter.prev();
        }
      };
    }
    assert!(!iter.valid());
  }

  // TODO: add concurrency tests

  type Key = u64;

  // TODO: think about other ways to do this.
  struct KeyComparator {
  }

  impl Comparator<Key> for KeyComparator {
    fn compare(&self, a: &Key, b: &Key) -> Ordering {
      a.cmp(b)
    }

    fn name(&self) -> &str {
      "KeyComparator"
    }
  }
}
