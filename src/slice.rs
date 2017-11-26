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

use std::{ptr, slice};
use std::cmp::Ordering;
use std::ops::Index;

use util::bit;

/// Just like Rust's slice, except there's no borrowing.
/// Instead, the user needs to guarantee that
/// the instances of this struct should not live longer than
/// the memory that `data` points to.
#[derive(Clone)]
pub struct Slice {
  data: *const u8,
  size: usize
}

impl Slice {
  /// Create an empty slice
  pub fn new_empty() -> Self {
    Self {
      data: ptr::null(),
      size: 0
    }
  }

  /// Create a slice that refers to `d`
  pub fn new(data: *const u8, size: usize) -> Self {
    Self {
      data: data,
      size: size
    }
  }

  /// Return the length (in bytes) of the referenced data
  #[inline]
  pub fn size(&self) -> usize {
    self.size
  }

  /// Return the raw pointer to the internal data
  #[inline]
  pub fn raw_data(&self) -> *const u8 {
    self.data
  }

  /// Return a slice to the internal data.
  /// This should be preferred over `raw_data()`.
  #[inline]
  pub fn data(&self) -> &[u8] {
    unsafe {
      slice::from_raw_parts(self.data, self.size)
    }
  }

  /// Return true iff the length of the referenced data is zero
  #[inline]
  pub fn empty(&self) -> bool {
    self.size() == 0
  }

  /// Change this slice to refer to an empty array
  #[inline]
  pub fn clear(&mut self) {
    self.data = ptr::null();
    self.size = 0;
  }

  /// Drop the first `n` bytes from this slice
  pub fn remove_prefix(&mut self, n: usize) {
    assert!(n <= self.size());
    unsafe {
      self.data = self.data.offset(n as isize);
    }
    self.size -= n;
  }

  /// Return true iff `x` is a prefix of `self`
  pub fn starts_with(&self, x: &Slice) -> bool {
    unsafe {
      self.size() >= x.size() && bit::memcmp(self.data, x.data, x.size()) == 0
    }
  }

  /// Returns a string from the slice data
  pub fn to_str(&self) -> &str {
    unsafe {
      ::std::str::from_utf8_unchecked(self.data())
    }
  }

  /// Three-way comparison. Returns value:
  ///   `Ordering::Less`    iff `self` < `b`
  ///   `Ordering::Equal`   iff `self` = `b`
  ///   `Ordering::Greater` iff `self` > `b`
  #[inline]
  pub fn compare(&self, b: &Slice) -> Ordering {
    let min_len = if self.size() < b.size() { self.size() } else { b.size() };
    let r = unsafe { bit::memcmp(self.data, b.data, min_len) };
    match r {
      _ if r > 0 => Ordering::Greater,
      _ if r < 0 => Ordering::Less,
      0 if self.size > b.size => Ordering::Greater,
      0 if self.size < b.size => Ordering::Less,
      _ => Ordering::Equal
    }
  }
}

impl Index<usize> for Slice {
  type Output = u8;

  /// Return the ith byte in the referenced data
  /// REQUIRES: index < self.size()
  fn index(&self, index: usize) -> &u8 {
    unsafe {
      &*self.data.offset(index as isize)
    }
  }
}

impl<'a> From<&'a [u8]> for Slice {
  #[inline]
  fn from(s: &'a [u8]) -> Self {
    Slice::new(s.as_ptr(), s.len())
  }
}

impl<'a> From<&'a str> for Slice {
  #[inline]
  fn from(s: &'a str) -> Self {
    Slice::new(s.as_ptr(), s.len())
  }
}

impl From<String> for Slice {
  #[inline]
  fn from(s: String) -> Self {
    Slice::new(s.as_ptr(), s.len())
  }
}
