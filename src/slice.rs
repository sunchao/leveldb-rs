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

use std::cmp::Ordering;
use std::ops::Index;

// TODO: find a more space-efficient way to represent this
pub struct Slice {
  data: Vec<u8>,
  start: usize,
  len: usize
}

impl Slice {
  /// Create an empty slice
  pub fn new_empty() -> Self {
    Self {
      data: Vec::new(),
      start: 0,
      len: 0
    }
  }

  /// Create a slice that refers to `d`
  pub fn new(d: &[u8]) -> Self {
    let len = d.len();
    Self {
      data: Vec::from(d),
      start: 0,
      len: len
    }
  }

  /// Create a slice that refers to the content of `s`
  pub fn new_string(s: &str) -> Self {
    let len = s.len();
    Self {
      data: Vec::from(s.as_bytes()),
      start: 0,
      len: len
    }
  }

  /// Return the length (in bytes) of the referenced data
  pub fn size(&self) -> usize {
    self.len - self.start
  }

  /// Return a reference to the data
  #[inline]
  pub fn data(&self) -> &[u8] {
    &self.data[self.start..]
  }

  /// Return true iff the length of the referenced data is zero
  pub fn empty(&self) -> bool {
    self.size() == 0
  }

  /// Change this slice to refer to an empty array
  pub fn clear(&mut self) {
    self.data = Vec::new();
    self.start = 0;
    self.len = 0;
  }

  /// Drop the first `n` bytes from this slice
  pub fn remove_prefix(&mut self, n: usize) {
    assert!(n <= self.size());
    self.start = n;
  }

  /// Return true iff `x` is a prefix of `self`
  pub fn starts_with(&self, x: &Slice) -> bool {
    self.size() >= x.size() && &self.data()[..x.size()] == x.data()
  }

  /// Three-way comparison. Returns value:
  ///   `Ordering::Less`    iff `self` < `b`
  ///   `Ordering::Equal`   iff `self` = `b`
  ///   `Ordering::Greater` iff `self` > `b`
  #[inline]
  pub fn compare(&self, b: &Slice) -> Ordering {
    let min_len = if self.size() < b.size() { self.size() } else { b.size() };
    self.data()[..min_len].cmp(&b.data()[..min_len])
  }
}

impl Index<usize> for Slice {
  type Output = u8;

  /// Return the ith byte in the referenced data
  /// REQUIRES: index < self.size()
  fn index(&self, index: usize) -> &u8 {
    &self.data[index + self.start]
  }
}
