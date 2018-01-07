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
use std::rc::Rc;
use std::cell::RefCell;

use util::atomic::{AtomicPointer, AtomicUsize};
use util::arena::{Arena, ArenaRef};
use util::random::Random;
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
// TODO: implement `Send` and `Sync` for this struct?
pub struct SkipList<K> {
  cmp: Rc<Comparator<K>>,
  arena: ArenaRef,
  head: *mut Node<K>,
  max_height: AtomicUsize,
  rnd: Random
}

const MAX_HEIGHT: usize = 12;
const BRANCHING: u32 = 4; // 25% chance to reach next level

// This implementation uses raw pointers for list nodes. This is
// to avoid perf penalty (potentially by `RefCell` and `Rc`), and
// the need to allocate nodes from pre-allocated memory
// (see `Node::new_node()`).
// Because of the above, this struct should NEVER leak node pointers,
// to avoid memory leak.
//
impl<K> SkipList<K> {
  /// Create a new skiplist that uses `cmp` to compare keys, and
  /// `arena` to allocate memory.
  pub fn new(
    cmp: Rc<Comparator<K>>,
    arena: ArenaRef,
    root_key: K
  ) -> Self {
    let h = Node::new_node(&arena, root_key, MAX_HEIGHT);
    let rnd = Random::new(0xdeadbeef);
    Self {
      cmp: cmp,
      arena: arena,
      head: h,
      max_height: AtomicUsize::new(1),
      rnd: rnd
    }
  }

  /// Insert the `key` into this skiplist.
  /// The `key` should NOT already exist in the skiplist and the caller
  /// of this function needs to make sure that.
  pub fn insert(&self, key: K) {
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

    let x = Node::new_node(&self.arena, key, height);
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

  pub fn iter(&self) -> SkipListIterator<K> {
    SkipListIterator::new(self)
  }

  /// Generate a random height in the range of `[1, MAX_HEIGHT]`.
  fn random_height(&self) -> usize {
    let mut height = 1;
    while height < MAX_HEIGHT && self.rnd.next() % BRANCHING == 0 {
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
  fn key_is_after(&self, key: &K, n: *mut Node<K>) -> bool {
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
    mut prev: Option<&mut [*mut Node<K>]>
  ) -> *mut Node<K> {
    let mut x = self.head;
    if self.max_height() < 1 {
      panic!("failed");
    }
    let mut level = self.max_height() - 1;
    loop {
      let next = unsafe {
        let result = (*x).next(level as usize);
        result
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
  fn find_last(&self) -> *mut Node<K> {
    let mut x = self.head;
    let mut level = self.max_height() - 1;
    loop {
      let next = unsafe {
        let result = (*x).next(level as usize);
        result
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
  fn find_less_than(&self, key: &K) -> *mut Node<K> {
    let mut x = self.head;
    let mut level = self.max_height() - 1;
    loop {
      let next = unsafe {
        let result = (*x).next(level as usize);
        result
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
struct Node<K> {
  // key for this node.
  key: K,

  // vector of next links, with length equal to the height of this node.
  next: Box<[AtomicPointer<Node<K>>]>
}

impl<K> Node<K> {
  /// Create a new node with `key` and `height`. The memory is allocated using
  /// `arena`.
  ///
  /// Return a new unique node instance whose lifetime is the same as
  /// the `arena`.
  pub fn new_node(
    arena_ref: &RefCell<Arena>,
    key: K,
    height: usize
  ) -> *mut Node<K> {
    let size = mem::size_of::<Node<K>>() +
      mem::size_of::<AtomicPointer<Node<K>>>() * height;
    let mut arena = arena_ref.try_borrow_mut()
      .expect("Arena should not have been borrowed");
    let ptr = arena.alloc_aligned(size);
    let mem = unsafe { slice::from_raw_parts_mut(ptr, size) };
    let (left, right) = mem.split_at_mut(mem::size_of::<Node<K>>());
    let node = left.as_mut_ptr() as *mut Node<K>;
    let values = unsafe {
      Vec::from_raw_parts(
        right.as_mut_ptr() as *mut AtomicPointer<Node<K>>,
        height,
        height
      )
    };
    unsafe {
      (*node).key = key;
      (*node).next = values.into_boxed_slice();
    }
    node
  }

  /// Get the key for node `n`.
  /// REQUIRES: `n` is not null.
  #[inline(always)]
  pub fn get_key<'a>(n: *const Node<K>) -> &'a K {
    assert!(!n.is_null());
    unsafe {
      let result = &(*n).key;
      result
    }
  }

  /// Return the next node at level `n`. If there is no next
  /// at the position, return `None`.
  /// REQUIRES: `n` < height of this node
  #[inline(always)]
  pub fn next(&self, n: usize) -> *mut Node<K> {
    assert!(n < self.next.len());
    self.next[n].acquire_load()
  }

  /// Set the next node at level `n` to be `node`.
  /// REQUIRES: `n` < height of this node
  #[inline(always)]
  pub fn set_next(&mut self, n: usize, node: *mut Node<K>) {
    assert!(n < self.next.len());
    let ptr = AtomicPointer::new(node);
    self.next[n] = ptr;
  }
}

///
/// An iterator on a skiplist with ability to move forward and backward.
///
pub struct SkipListIterator<'a, K> where K: 'a {
  list: &'a SkipList<K>,
  node: *const Node<K>
}

impl<'a, K> SkipListIterator<'a, K> {
  #[inline(always)]
  pub fn new(list: &'a SkipList<K>) -> Self {
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
      let result = (*h).next(0);
      result
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
  use std::slice;
  use std::collections::BTreeSet;
  use std::collections::Bound::{Included, Unbounded};
  use std::sync::{Mutex, Condvar};
  use crossbeam;

  use super::*;
  use util::atomic::{AtomicU64, AtomicBool};
  use util::hash;

  #[test]
  fn new_node() {
    let arena = RefCell::new(Arena::new());

    let empty = Vec::new();
    let mut n0 = Node { key: 28, next: empty.into_boxed_slice() };
    let n: &mut Node<i32> =
      unsafe {
        mem::transmute(Node::<i32>::new_node(&arena, 42, 3))
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
  fn empty() {
    let arena = Rc::new(RefCell::new(Arena::new()));
    let cmp = KeyComparator {};
    let list = SkipList::new(Rc::new(cmp), arena, 0);
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
  fn insert_and_lookup() {
    const N: i32 = 2000;
    const R: u32 = 5000;

    let mut keys: BTreeSet<u64> = BTreeSet::new();
    let cmp = KeyComparator {};
    let arena = Rc::new(RefCell::new(Arena::new()));
    let list = SkipList::new(Rc::new(cmp), arena, 0);
    let rnd = Random::new(1000);

    for _ in 0..N {
      let key = rnd.next() % R;
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

  // concurrency tests

  const K: u64 = 4;

  fn key(key: &Key) -> u64 { key >> 40 }
  fn gen(key: &Key) -> u64 { (key >> 8) & 0xffffffffu64 }
  fn hash(key: &Key) -> u64 { key & 0xff }

  fn hash_numbers(k: u64, g: u64) -> u64 {
    let v: &[u8] = unsafe {
      let data: [u64; 2] = [k, g];
      let result = slice::from_raw_parts(
        &data as *const u64 as *const u8, 2 * 8);
      result
    };
    hash::hash(v, 0u32) as u64
  }

  fn make_key(k: u64, g: u64) -> Key {
    assert!(k <= K);
    assert!(g <= 0xffffffffu64);
    (k << 40) | (g << 8) | (hash_numbers(k, g) & 0xff)
  }

  fn is_valid_key(k: &Key) -> bool {
    hash(k) == (hash_numbers(key(k), gen(k)) & 0xff)
  }

  fn random_target(rnd: &Random) -> Key {
    match rnd.next() % 10 {
      0 => make_key(0, 0), // seek to beginning
      1 => make_key(K, 0), // seek to end
      _ => make_key(rnd.next() as u64 % K, 0) // seek to middle
    }
  }

  struct ConcurrencyTester<> {
    current: State,
    list: SkipList<Key>
  }

  // Should be safe since `current` and `list` are both thread-safe.

  unsafe impl Send for ConcurrencyTester {}
  unsafe impl Sync for ConcurrencyTester {}

  impl ConcurrencyTester {
    pub fn new(arena: Rc<RefCell<Arena>>) -> Self {
      let cmp = KeyComparator {};
      Self {
        current: State::new(),
        list: SkipList::new(Rc::new(cmp), arena, 0)
      }
    }

    fn write_step(&self, rnd: &Random) {
      let k = rnd.next() as u64 % K;
      let g = self.current.get(k) + 1;
      let key = make_key(k as u64, g as u64);
      self.list.insert(key);
      self.current.set(k, g);
    }

    fn read_step(&self, rnd: &Random) {
      let initial_state = State::new();
      for k in 0..K {
        initial_state.set(k, self.current.get(k));
      }

      let mut pos = random_target(rnd);
      let mut iter = SkipListIterator::new(&self.list);
      iter.seek(&pos);

      loop {
        let current = if !iter.valid() {
          make_key(K, 0)
        } else {
          let k = iter.key();
          assert!(is_valid_key(k));
          *k
        };

        assert!(pos <= current, "should not go backwards");

        // verify that everything in [pos, current) was not present in
        // `initial_state`
        while pos < current {
          assert!(key(&pos) < K);
          assert!(gen(&pos) == 0 || gen(&pos) > initial_state.get(key(&pos)),
                  "key = {}, gen(&pos) = {}, initial_state.get(key(&pos)) = {}",
                  key(&pos), gen(&pos), initial_state.get(key(&pos))
          );

          // advance to next key in the valid key space
          pos = if key(&pos) < key(&current) {
            make_key(key(&pos) + 1, 0)
          } else {
            make_key(key(&pos), gen(&pos) + 1)
          }
        }

        if !iter.valid() {
          break
        }

        if rnd.next() % 2 == 1 {
          iter.next();
          pos = make_key(key(&pos), gen(&pos) + 1);
        } else {
          let new_target = random_target(rnd);
          if new_target > pos {
            pos = new_target;
            iter.seek(&new_target);
          }
        }
      }
    }
  }

  struct State {
    generation: Vec<AtomicU64>
  }

  impl State {
    fn new() -> Self {
      let mut gen: Vec<AtomicU64> = Vec::new();
      for _ in 0..K {
        gen.push(AtomicU64::new(0));
      }
      State {
        generation: gen
      }
    }

    fn get(&self, k: u64) -> u64 {
      self.generation[k as usize].acquire_load() 
    }

    fn set(&self, k: u64, v: u64) {
      self.generation[k as usize].release_store(v);
    }
  }

  // TODO: make this configurable
  const SEED: u32 = 301;

  #[test]
  fn concurrent_without_threads() {
    let arena = Rc::new(RefCell::new(Arena::new()));
    let tester = ConcurrencyTester::new(arena);
    let rnd = Random::new(SEED);
    for _ in 0..10000 {
      tester.read_step(&rnd);
      tester.write_step(&rnd);
    }
  }


  struct TestState {
    seed: u32,
    quit_flag: AtomicBool,
    mu: (Mutex<ReaderState>, Condvar)
  }

  impl TestState {
    fn new(
      s: u32,
      flag: AtomicBool,
      mu: (Mutex<ReaderState>, Condvar)
    ) -> Self {
      TestState {
        seed: s,
        quit_flag: flag,
        mu: mu
      }
    }

    fn wait(&self, s: ReaderState) {
      let &(ref mu, ref cv) = &self.mu;
      let mut guard = mu.lock().unwrap();
      while *guard != s {
        guard = cv.wait(guard).unwrap();
      }
    }

    fn change(&self, state: ReaderState) {
      let &(ref mu, ref cv) = &self.mu;
      let mut guard = mu.lock().unwrap();
      *guard = state;
      cv.notify_all();
    }
  }

  #[derive(PartialEq, Eq)]
  enum ReaderState {
    STARTING,
    RUNNING,
    DONE
  }

  // Helper func that spawns two threads to do read/write concurrently.
  // Note that this uses scoped threads so no `Arc` is required.
  // TODO: should we declare `rnd` outside the loop? we need it to be
  // `Send/Sync` though.
  fn run_concurrent<'a>(run: u32) {
    let seed = SEED + run * 100;
    const N: u32 = 1000;
    const K_SIZE: u32 = 1000;

    for _ in 0..N {
      let state = TestState::new(
        seed + 1, AtomicBool::new(false),
        (Mutex::new(ReaderState::STARTING), Condvar::new())
      );
      let arena = Rc::new(RefCell::new(Arena::new()));
      let tester = ConcurrencyTester::new(arena);

      crossbeam::scope(|scope| {
        scope.spawn(|| {
          let rnd = Random::new(state.seed);
          state.change(ReaderState::RUNNING);
          while !state.quit_flag.acquire_load() {
            tester.read_step(&rnd);
          }
          state.change(ReaderState::DONE);
        });
        scope.spawn(|| {
          state.wait(ReaderState::RUNNING);
          let rnd = Random::new(seed);
          for _ in 0..K_SIZE {
            tester.write_step(&rnd);
          }
          state.quit_flag.release_store(true);
          state.wait(ReaderState::DONE);
        });
      });
    }
  }

  #[test] fn concurrent1() { run_concurrent(1); }
  #[test] fn concurrent2() { run_concurrent(2); }
  #[test] fn concurrent3() { run_concurrent(3); }
  #[test] fn concurrent4() { run_concurrent(4); }
  #[test] fn concurrent5() { run_concurrent(5); }


  // auxiliary definitions

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
