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

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{Hasher, BuildHasherDefault};
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::rc::Rc;
use std::sync::Mutex;

use slice::Slice;
use util::hash;

pub trait Handle<T> {
  fn get_value(&self) -> &T;
}

type HandlePtr<T> = Rc<RefCell<Handle<T>>>;

pub trait Cache<T> {
  /// Insert a mapping from key->value into the cache and assign it the specified charge
  /// against the total cache capacity.
  ///
  /// Return a handle that corresponds to the mapping. the caller must call
  /// `release(handle)` when the returned mapping is no longer needed.
  ///
  /// When the inserted entry is no longer needed, the key and value will be passed to
  /// `deleter`.
  fn insert(
    &mut self,
    key: Slice,
    value: T,
    charge: usize,
    deleter: Box<FnMut(&Slice, &T)>
  ) -> HandlePtr<T>;

  /// If the cache has no mapping for `key`, returns `None`. Otherwise, return a handle
  /// that corresponds to the mapping. The caller must call `release(handle)` when the
  /// returned mapping is no longer needed.
  fn lookup(&self, key: &Slice) -> Option<HandlePtr<T>>;

  /// Release a mapping returned by a previous `insert` or `lookup`.
  /// REQUIRES: `handle` must not have been released yet.
  /// REQUIRES: `handle` must have been returned by a method on this instance.
  fn release(&mut self, handle: HandlePtr<T>);

  /// If the cache contains entry for the key, erase it. Note that the underlying entry
  /// will be kept around until all existing handles to it have been released.
  fn erase(&mut self, key: &Slice);

  /// Return a new numeric id. May be used by multiple clients who are sharing the same
  /// cache to partition the key space. Typically the client will allocate a new id at
  /// startup and prepend the id to its cache keys.
  fn new_id(&self) -> u64;

  /// Remove all cache entries that are not actively in use. Memory-constrained
  /// applications may wish to call this method to reduce memory usage.
  fn prune(&mut self);

  /// Return an estimate of the combined charges of all elements stored in the cache.
  fn total_charge(&self) -> usize;
}

/// LRU cache implemenation
///
/// Cache entries have an `in_cache` boolean indicating whether the cache has a reference
/// on the entry.  The only ways that this can become false without the entry being passed
/// to its "deleter" are via `erase()`, via `insert()` when an element with a duplicate
/// key is inserted, or on destruction of the cache.
///
/// The cache keeps two linked lists of items in the cache.  All items in the cache are in
/// one list or the other, and never both.  Items still referenced by clients but erased
/// from the cache are in neither list.  The lists are:
/// - in-use:  contains the items currently referenced by clients, in no particular order.
///   (This list is used for invariant checking.  If we removed the check, elements that
///   would otherwise be on this list could be left as disconnected singleton lists.)
/// - LRU:  contains the items not currently referenced by clients, in LRU order
/// Elements are moved between these lists by the `inc_ref()` and `dec_ref()` methods,
/// when they detect an element in the cache acquiring or losing its only external
/// reference.
///
struct LRUCache<T: Default + Debug + 'static> {
  capacity: usize,
  mutex: Mutex<MutexData<T>>
}

/// An handle is a variable length heap-allocated structure. Handles are kept in a
/// circular doubly linked list ordered by access time.
struct LRUHandle<T: Default + Debug> {
  key: Box<[u8]>,
  value: T,
  charge: usize,
  deleter: Option<Box<FnMut(&Slice, &T)>>,
  next: *mut LRUHandle<T>,
  prev: *mut LRUHandle<T>
}

type LRUHandlePtr<T> = Rc<RefCell<LRUHandle<T>>>;

impl<T> Drop for LRUHandle<T> where T: Default + Debug {
  fn drop(&mut self) {
    // Only drop for non-dummy nodes with non-empty deleter.
    if let Some(ref mut deleter) = self.deleter {
      let key = self.key();
      (deleter)(&key, &self.value);
    }
  }
}

impl<T> Default for LRUHandle<T> where T: Default + Debug {
  fn default() -> Self {
    LRUHandle {
      key: Vec::new().into_boxed_slice(),
      value: T::default(),
      charge: 0,
      deleter: None,
      next: ptr::null_mut(),
      prev: ptr::null_mut()
    }
  }
}

impl<T> LRUHandle<T> where T: Default + Debug {
  fn new(
    key: Box<[u8]>,
    value: T,
    charge: usize,
    deleter: Box<FnMut(&Slice, &T)>
  ) -> Self {
    Self {
      key: key,
      value: value,
      charge: charge,
      deleter: Some(deleter),
      next: ptr::null_mut(),
      prev: ptr::null_mut()
    }
  }

  fn key(&self) -> Slice {
    Slice::from(&self.key[..])
  }
}

impl<T> Handle<T> for LRUHandle<T> where T: Default + Debug {
  fn get_value(&self) -> &T {
    &self.value
  }
}

/// A hashmap of slice->handle, which uses our own hash function on slices.
#[derive(Default)]
struct SliceHasher(u64);

impl Hasher for SliceHasher {
  #[inline]
  fn finish(&self) -> u64 {
    return self.0
  }
  #[inline]
  fn write(&mut self, bytes: &[u8]) {
    let result = hash::hash(bytes, 0) as u64;
    *self = SliceHasher(result);
  }
}

// TODO: consider implementing our own hash table and avoid recomputing the hash.
type HandleTable<T> =
  HashMap<Slice, LRUHandlePtr<T>, BuildHasherDefault<SliceHasher>>;


/// States that are protected by the mutex in the `LRUCache` struct.
struct MutexData<T: Default + Debug> {
  usage: usize,
  lru: *mut LRUHandle<T>,
  in_use: *mut LRUHandle<T>,
  table: HandleTable<T>
}

impl<T> Drop for LRUCache<T> where T: Default + Debug + 'static {
  fn drop(&mut self) {
    let mutex_data = self.mutex.lock().unwrap();
    Self::drop_dummy_node(mutex_data.lru);
    Self::drop_dummy_node(mutex_data.in_use);
  }
}

impl<T> LRUCache<T> where T: Default + Debug + 'static {
  fn new(capacity: usize) -> Self {
    let mutex_data = MutexData {
      usage: 0,
      lru: Self::create_dummy_node(),
      in_use: Self::create_dummy_node(),
      table: HashMap::default()
    };

    Self {
      capacity: capacity,
      mutex: Mutex::new(mutex_data)
    }
  }

  fn create_dummy_node() -> *mut LRUHandle<T> {
    unsafe {
      let n = Box::into_raw(box LRUHandle::default());
      (*n).next = n;
      (*n).prev = n;
      n
    }
  }

  fn drop_dummy_node(n: *mut LRUHandle<T>) {
    assert!(!n.is_null());
    unsafe { *Box::from_raw(n); }
  }

  fn inc_ref(list: *mut LRUHandle<T>, h: &LRUHandlePtr<T>) {
    if Rc::strong_count(h) == 1 {
      let p = h.borrow_mut().deref_mut() as *mut LRUHandle<T>;
      Self::lru_remove(p);
      Self::lru_append(list, p);
    }
  }

  fn dec_ref(list: *mut LRUHandle<T>, h: HandlePtr<T>) {
    let c = Rc::strong_count(&h);
    if c == 2 {
      let p = h.borrow_mut().deref_mut() as *mut Handle<T> as *mut LRUHandle<T>;
      Self::lru_remove(p);
      Self::lru_append(list, p);
    }
  }

  fn lru_remove(h: *mut LRUHandle<T>) {
    unsafe {
      (*(*h).next).prev = (*h).prev;
      (*(*h).prev).next = (*h).next;
    }
  }

  fn lru_append(list: *mut LRUHandle<T>, h: *mut LRUHandle<T>) {
    unsafe {
      (*h).next = list;
      (*h).prev = (*list).prev;
      (*(*h).prev).next = h;
      (*(*h).next).prev = h;
    }
  }

  fn finish_erase(mutex_data: &mut MutexData<T>, e: LRUHandlePtr<T>) {
    mutex_data.usage -= e.borrow().charge;
    Self::lru_remove(e.borrow_mut().deref_mut() as *mut LRUHandle<T>);
    Self::dec_ref(mutex_data.lru, e);
  }

}

impl<T: Default + Debug + 'static> Cache<T> for LRUCache<T> {
  fn insert(
    &mut self,
    key: Slice,
    value: T,
    charge: usize,
    deleter: Box<FnMut(&Slice, &T)>
  ) -> HandlePtr<T> {
    let mut mutex_data = self.mutex.lock().unwrap();

    let b = Vec::from(key.data()).into_boxed_slice();
    let mut e = LRUHandle::new(b, value, charge, deleter);

    let r =
      if self.capacity > 0 {
        let r = Rc::new(RefCell::new(e));
        Self::lru_append(mutex_data.in_use, r.clone().borrow_mut().deref_mut());
        mutex_data.usage += charge;
        if let Some(old) = mutex_data.table.insert(key, r.clone()) {
          Self::finish_erase(&mut mutex_data, old);
        };
        r
      } else { // don't cache
        e.next = ptr::null_mut();
        Rc::new(RefCell::new(e))
      };

    // Remove outdated items
    let lru: *mut LRUHandle<T> = mutex_data.lru;
    unsafe {
      // Remove items in lru until we have enough capacity
      while mutex_data.usage > self.capacity && (*lru).next != lru {
        let old: *mut LRUHandle<T> = (*lru).next;
        if let Some(old) = mutex_data.table.remove(&(*old).key()) {
          assert!(Rc::strong_count(&old) == 1);
          Self::finish_erase(&mut mutex_data, old);
        }
      }
    }

    r
  }

  fn lookup(&self, key: &Slice) -> Option<HandlePtr<T>> {
    let mutex_data = self.mutex.lock().unwrap();
    match mutex_data.table.get(&key) {
      Some(e) => {
        Self::inc_ref(mutex_data.in_use, e);
        Some(e.clone())
      },
      None => None
    }
  }

  fn release(&mut self, handle: HandlePtr<T>) {
    let mutex_data = self.mutex.lock().unwrap();
    Self::dec_ref(mutex_data.lru, handle);
  }

  fn erase(&mut self, key: &Slice) {
    let mut mutex_data = self.mutex.lock().unwrap();
    if let Some(p) = mutex_data.table.remove(key) {
      Self::finish_erase(&mut mutex_data, p);
    }
  }

  fn new_id(&self) -> u64 {
    0 // Dummy return value which never get used.
  }

  fn prune(&mut self) {
    let mut mutex_data = self.mutex.lock().unwrap();
    let lru = mutex_data.lru;
    unsafe {
      while (*lru).next != lru {
        let e = (*lru).next;
        let p = mutex_data.table.remove(&(*e).key()).expect("Key not found");
        Self::finish_erase(&mut mutex_data, p);
      }
    }
  }

  fn total_charge(&self) -> usize {
    let mutex_data = self.mutex.lock().unwrap();
    mutex_data.usage
  }
}

const NUM_SHARD_BITS: usize = 4;
const NUM_SHARDS: usize = 1 << NUM_SHARD_BITS;

pub struct ShardedLRUCache<T: Default + Debug + 'static> {
  shard: [LRUCache<T>; NUM_SHARDS],
  last_id: Mutex<u64>
}

impl<T: Default + Debug + 'static> ShardedLRUCache<T> {
  pub fn new(capacity: usize) -> Self {
    let per_shard = (capacity + (NUM_SHARDS - 1)) / NUM_SHARDS;
    Self {
      shard: unsafe {
        let mut shard: [LRUCache<T>; NUM_SHARDS] = ::std::mem::uninitialized();
        for e in shard.iter_mut() {
          ::std::ptr::write(e, LRUCache::new(per_shard));
        }
        shard
      },
      last_id: Mutex::new(0)
    }
  }
}

fn hash_slice(s: &Slice) -> u32 {
  let result = hash::hash(s.data(), 0);
  result
}

fn shard(hash: u32) -> usize {
  (hash >> (32 - NUM_SHARD_BITS)) as usize
}

impl<T: Default + Debug + 'static> Cache<T> for ShardedLRUCache<T> {
  fn insert(
    &mut self,
    key: Slice,
    value: T,
    charge: usize,
    deleter: Box<FnMut(&Slice, &T)>
  ) -> HandlePtr<T> {
    let hash = hash_slice(&key);
    self.shard[shard(hash)].insert(key, value, charge, deleter)
  }

  fn lookup(&self, key: &Slice) -> Option<HandlePtr<T>> {
    let hash = hash_slice(key);
    self.shard[shard(hash)].lookup(key)
  }

  fn release(&mut self, handle: HandlePtr<T>) {
    let key = unsafe {
      let h = handle.borrow().deref() as *const Handle<T> as *const LRUHandle<T>;
      (*h).key()
    };
    let hash = hash_slice(&key);
    self.shard[shard(hash)].release(handle);
  }

  fn erase(&mut self, key: &Slice) {
    let hash = hash_slice(key);
    self.shard[shard(hash)].erase(key)
  }

  fn new_id(&self) -> u64 {
    let mut l = self.last_id.lock().unwrap();
    *l += 1;
    *l
  }

  fn prune(&mut self) {
    for s in self.shard.iter_mut() {
      s.prune()
    }
  }

  fn total_charge(&self) -> usize {
    self.shard.iter().fold(0, |acc, s| acc + s.total_charge())
  }
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use std::cell::RefCell;

  use super::*;
  use util::coding;

  struct CacheTester {
    cache: Box<Cache<i32>>,
    inserted_keys: Vec<Vec<u8>>,
    deleted_keys: Rc<RefCell<Vec<i32>>>,
    deleted_values: Rc<RefCell<Vec<i32>>>
  }

  const CACHE_SIZE: usize = 1000;

  impl CacheTester {
    fn new() -> Self {
      let keys = Rc::new(RefCell::new(Vec::new()));
      let values = Rc::new(RefCell::new(Vec::new()));
      Self {
        cache: box ShardedLRUCache::new(CACHE_SIZE),
        inserted_keys: Vec::new(),
        deleted_keys: keys,
        deleted_values: values
      }
    }

    fn lookup(&mut self, key: i32) -> i32 {
      let k = self.gen_key(key);
      if let Some(handle) = self.cache.lookup(&k) {
        let result = *handle.borrow().get_value() as i32;
        self.cache.release(handle);
        result
      } else {
        -1
      }
    }

    fn insert(&mut self, key: i32, value: i32) {
      Self::insert_charge(self, key, value, 1);
    }

    fn insert_charge(&mut self, key: i32, value: i32, charge: i32) {
      let k = self.gen_key(key);
      let h = self.cache.insert(
        k, value, charge as usize,
        box fn_deleter(self.deleted_keys.clone(), self.deleted_values.clone()));
      self.cache.release(h);
    }

    fn insert_and_return_handle(&mut self, key: i32, value: i32) -> HandlePtr<i32> {
      let k = self.gen_key(key);
      self.cache.insert(
        k, value, 1,
        box fn_deleter(self.deleted_keys.clone(), self.deleted_values.clone()))
    }

    fn erase(&mut self, key: i32)  {
      let k = self.gen_key(key);
      self.cache.erase(&k);
    }

    fn gen_key(&mut self, k: i32) -> Slice {
      let mut v = vec![0; 4];
      coding::encode_fixed_32(&mut v[..], k as u32);
      self.inserted_keys.push(v);
      Slice::from(&self.inserted_keys[self.inserted_keys.len()-1])
    }

  }

  fn encode_key(k: i32) -> Vec<u8> {
    let mut v = vec![0; 4];
    coding::encode_fixed_32(&mut v[..], k as u32);
    v
  }

  fn fn_deleter(
    keys: Rc<RefCell<Vec<i32>>>,
    values: Rc<RefCell<Vec<i32>>>
  ) -> impl FnMut(&Slice, &i32) {
    move |k, v| {
      let dk = coding::decode_fixed_32(k.data());
      keys.borrow_mut().push(dk as i32);
      values.borrow_mut().push(*v);
    }
  }

  #[test]
  fn hit_and_miss() {
    let mut ct = CacheTester::new();
    assert_eq!(-1, ct.lookup(100));

    ct.insert(100, 101);
    assert_eq!(101, ct.lookup(100));
    assert_eq!(-1, ct.lookup(200));
    assert_eq!(-1, ct.lookup(300));

    ct.insert(200, 201);
    assert_eq!(101, ct.lookup(100));
    assert_eq!(201, ct.lookup(200));
    assert_eq!(-1, ct.lookup(300));

    ct.insert(100, 102);
    assert_eq!(102, ct.lookup(100));
    assert_eq!(201, ct.lookup(200));
    assert_eq!(-1, ct.lookup(300));

    assert_eq!(1, ct.deleted_keys.borrow().len());
    assert_eq!(100, ct.deleted_keys.borrow()[0]);
    assert_eq!(101, ct.deleted_values.borrow()[0]);
  }

  #[test]
  fn erase() {
    let mut ct = CacheTester::new();
    ct.erase(200);
    assert_eq!(0, ct.deleted_keys.borrow().len());

    ct.insert(100, 101);
    ct.insert(200, 201);
    ct.erase(100);
    assert_eq!(-1, ct.lookup(100));
    assert_eq!(201, ct.lookup(200));
    assert_eq!(1, ct.deleted_keys.borrow().len());
    assert_eq!(100, ct.deleted_keys.borrow()[0]);
    assert_eq!(101, ct.deleted_values.borrow()[0]);

    ct.erase(100);
    assert_eq!(-1, ct.lookup(100));
    assert_eq!(201, ct.lookup(200));
    assert_eq!(1, ct.deleted_keys.borrow().len());
  }

  #[test]
  fn entries_are_pinned() {
    let mut ct = CacheTester::new();
    ct.insert(100, 101);

    let key = encode_key(100);
    let s = Slice::from(&key);

    let h1 = ct.cache.lookup(&s).expect("lookup() should return Some");
    assert_eq!(101, *h1.borrow().get_value());

    ct.insert(100, 102);
    let h2 = ct.cache.lookup(&s).expect("lookup() should return Some");
    assert_eq!(102, *h2.borrow().get_value());
    assert_eq!(0, ct.deleted_keys.borrow().len());

    ct.cache.release(h1);
    assert_eq!(1, ct.deleted_keys.borrow().len());
    assert_eq!(100, ct.deleted_keys.borrow()[0]);
    assert_eq!(101, ct.deleted_values.borrow()[0]);

    ct.erase(100);
    assert_eq!(-1, ct.lookup(100));
    assert_eq!(1, ct.deleted_keys.borrow().len());

    ct.cache.release(h2);
    assert_eq!(2, ct.deleted_keys.borrow().len());
    assert_eq!(100, ct.deleted_keys.borrow()[1]);
    assert_eq!(102, ct.deleted_values.borrow()[1]);
  }

  #[test]
  fn eviction_policy() {
    let mut ct = CacheTester::new();
    ct.insert(100, 101);
    ct.insert(200, 201);
    ct.insert(300, 301);

    let key = encode_key(300);
    let s = Slice::from(&key);

    let h = ct.cache.lookup(&s).expect("lookup() should return Some");

    for i in 0..CACHE_SIZE + 100 {
      let i1 = i as i32;
      ct.insert(1000 + i1, 2000 + i1);
      assert_eq!(2000 + i1, ct.lookup(1000 + i1));
      assert_eq!(101, ct.lookup(100));
    }

    assert_eq!(101, ct.lookup(100));
    assert_eq!(-1, ct.lookup(200));
    assert_eq!(301, ct.lookup(300));
    ct.cache.release(h);
  }

  #[test]
  fn use_exceeds_cache_size() {
    let mut ct = CacheTester::new();
    let mut v = Vec::new();
    for i in 0..CACHE_SIZE + 100 {
      let i1 = i as i32;
      v.push(ct.insert_and_return_handle(1000 + i1, 2000 + i1));
    }
    for i in 0..v.len() {
      let i1 = i as i32;
      assert_eq!(2000 + i1, ct.lookup(1000 + i1));
    }
    for h in v {
      ct.cache.release(h);
    }
  }

  #[test]
  fn heavy_entries() {
    let mut ct = CacheTester::new();
    const LIGHT: i32 = 1;
    const HEAVY: i32 = 10;
    let mut added = 0;
    let mut index = 0;
    while added < 2 * CACHE_SIZE {
      let weight =
        if (index & 1) == 1 {
          LIGHT
        } else {
          HEAVY
        };
      ct.insert_charge(index, 1000 + index, weight);
      added += weight as usize;
      index += 1;
    }

    let mut cached_weight = 0;
    for i in 0..index {
      let weight =
        if i & 1 == 1 {
          LIGHT
        } else {
          HEAVY
        };
      let r = ct.lookup(i);
      if r >= 0 {
        cached_weight += weight;
        assert_eq!(1000 + i, r);
      }
    }

    assert!(cached_weight <= CACHE_SIZE as i32 + CACHE_SIZE as i32 / 10);
  }

  #[test]
  fn new_id() {
    let ct = CacheTester::new();
    let a = ct.cache.new_id();
    let b = ct.cache.new_id();
    assert!(a != b);
  }

  #[test]
  fn prune() {
    let mut ct = CacheTester::new();
    ct.insert(1, 100);
    ct.insert(2, 200);

    let key = encode_key(1);
    let s = Slice::from(&key);
    let h = ct.cache.lookup(&s).expect("lookup() should return Some");
    ct.cache.prune();
    ct.cache.release(h);

    assert_eq!(100, ct.lookup(1));
    assert_eq!(-1, ct.lookup(2));
  }

  #[test]
  fn zero_size_cache() {
    let mut ct = CacheTester::new();
    ct.cache = box ShardedLRUCache::new(0);
    ct.insert(1, 100);
    assert_eq!(-1, ct.lookup(1));
  }
}
