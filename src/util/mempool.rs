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

use std::ptr::null_mut;
use std::mem::size_of;
use std::cell::Cell;
use std::slice::from_raw_parts_mut;
use arena::TypedArena;

const K_BLOCK_SIZE: usize = 4096;

/// Similar to "Arena" in leveldb C++
/// Note that this implements "interior mutability", so caller
/// does not need to hold a unique reference to the struct in order
/// to call its functions.
pub struct MemPool {
  alloc_ptr: Cell<*mut u8>,
  alloc_bytes_remaining: Cell<usize>,
  arena: TypedArena<Vec<u8>>,
  memory_usage: Cell<i64>
}

impl MemPool {
  pub fn new() -> Self {
    Self {
      alloc_ptr: Cell::new(null_mut()),
      alloc_bytes_remaining: Cell::new(0),
      arena: TypedArena::new(),
      memory_usage: Cell::new(0)
    }
  }

  /// Allocate a byte slice with length `bytes`.
  /// Return a unique reference to the slice allocated.
  pub fn alloc(&self, bytes: usize) -> &mut [u8] {
    assert!(bytes > 0);
    if bytes <= self.alloc_bytes_remaining.get() {
      assert!(!self.alloc_ptr.get().is_null());
      let result = self.alloc_ptr.get();
      unsafe {
        self.alloc_ptr.set(self.alloc_ptr.get().offset(bytes as isize));
        self.alloc_bytes_remaining.set(
          self.alloc_bytes_remaining.get() - bytes);
        return from_raw_parts_mut(result, bytes)
      }
    }
    self.alloc_fallback(bytes)
  }

  /// Allocate a byte slice with length `bytes` that is aligned to pointer
  /// address.
  /// Return a unique reference to the slice allocated.
  pub fn alloc_aligned(&self, bytes: usize) -> &mut [u8] {
    let ptr_size = size_of::<usize>(); // TODO: double-check this
    assert!(ptr_size <= 128);
    let align = if ptr_size > 8 { ptr_size } else { 8 };
    assert!(align & (align - 1) == 0);
    let current_mod = self.alloc_ptr.get() as usize & (align-1);
    let slop = if current_mod == 0 { 0 } else { align - current_mod };
    let needed = bytes + slop;
    let result =
      if needed <= self.alloc_bytes_remaining.get() {
        unsafe {
          let r = self.alloc_ptr.get().offset(slop as isize);
          self.alloc_ptr.set(self.alloc_ptr.get().offset(needed as isize));
          self.alloc_bytes_remaining.set(
            self.alloc_bytes_remaining.get() - needed);
          r
        }
      } else {
        self.alloc_fallback(bytes).as_mut_ptr()
      };
    assert!(result as usize & (align-1) == 0);
    unsafe {
      from_raw_parts_mut(result, bytes)
    }
  }

  /// Return the memory usage for the memory pool, in number of bytes allocated.
  pub fn memory_usage(&self) -> i64 {
    self.memory_usage.get()
  }

  fn alloc_fallback(&self, bytes: usize) -> &mut [u8] {
    if bytes > K_BLOCK_SIZE / 4 {
      return self.alloc_new(bytes)
    }

    self.alloc_ptr.set(self.alloc_new(K_BLOCK_SIZE).as_mut_ptr());
    self.alloc_bytes_remaining.set(K_BLOCK_SIZE);

    let result = self.alloc_ptr.get();
    unsafe {
      self.alloc_ptr.set(self.alloc_ptr.get().offset(bytes as isize));
      self.alloc_bytes_remaining.set(self.alloc_bytes_remaining.get() - bytes);
      from_raw_parts_mut(result, bytes)
    }
  }

  fn alloc_new(&self, bytes: usize) -> &mut [u8] {
    let mut v = Vec::with_capacity(bytes);
    unsafe {
      v.set_len(bytes);
    }
    let result = self.arena.alloc(v);
    let memory_usage: i64 = self.memory_usage() + bytes as i64;
    self.memory_usage.set(memory_usage);
    println!("mem usage: {}", self.memory_usage());
    result
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_new() {
    let mem_pool = MemPool::new();
    assert!(mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 0);
    assert_eq!(mem_pool.memory_usage(), 0);
  }

  #[test]
  fn test_alloc_new() {
    let mem_pool = MemPool::new();

    let v1 = mem_pool.alloc_new(128);
    assert_eq!(v1.len(), 128);

    assert!(mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 0);
    assert_eq!(mem_pool.memory_usage(), 128);

    let v2 = mem_pool.alloc_new(256);
    assert_eq!(v2.len(), 256);

    assert!(mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 0);
    assert_eq!(mem_pool.memory_usage(), 256 + 128);
  }

  #[test]
  fn test_alloc_fallback() {
    let mem_pool = MemPool::new();

    let v1 = mem_pool.alloc_fallback(1025);
    assert_eq!(v1.len(), 1025);

    assert!(mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 0);
    assert_eq!(mem_pool.memory_usage(), 1025);

    let v2 = mem_pool.alloc_fallback(512);
    assert_eq!(v2.len(), 512);

    assert!(!mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(), K_BLOCK_SIZE - 512);
    assert_eq!(mem_pool.memory_usage(), 1025 + K_BLOCK_SIZE as i64);
  }

  #[test]
  fn test_alloc_aligned() {
    let mem_pool = MemPool::new();
    let ptr_size = ::std::mem::size_of::<usize>();
    assert!(ptr_size > 1);

    let v1 = mem_pool.alloc_fallback(1);
    assert_eq!(v1.len(), 1);

    let v2 = mem_pool.alloc_aligned(512);
    assert_eq!(v2.len(), 512);

    assert!(!mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(),
               K_BLOCK_SIZE - 512 - ptr_size);
  }

  #[test]
  fn test_alloc() {
    let mem_pool = MemPool::new();

    let _ = mem_pool.alloc(128);

    assert!(!mem_pool.alloc_ptr.get().is_null());
    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 3968);
    assert_eq!(mem_pool.memory_usage(), 4096);

    let _ = mem_pool.alloc(1024); // should allocate from existing block

    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 2944);
    assert_eq!(mem_pool.memory_usage(), 4096);

    let _ = mem_pool.alloc(8192); // should allocate new block

    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 2944);
    assert_eq!(mem_pool.memory_usage(), 12288);

    let _ = mem_pool.alloc(2048); // should allocate from existing block

    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 896);
    assert_eq!(mem_pool.memory_usage(), 12288);

    let _ = mem_pool.alloc(1024); // should allocate new block

    assert_eq!(mem_pool.alloc_bytes_remaining.get(), 3072);
    assert_eq!(mem_pool.memory_usage(), 16384);
  }
}
