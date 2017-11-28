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

use slice::Slice;

/// A comparator for type `T`.
pub trait Comparator<T> {
  /// Three-way comparison. Returns value:
  ///   `Ordering::Less`    iff `self` < `b`
  ///   `Ordering::Equal`   iff `self` = `b`
  ///   `Ordering::Greater` iff `self` > `b`
  fn compare(&self, a: &T, b: &T) -> Ordering;

  // The name of the comparator.  Used to check for comparator
  // mismatches (i.e., a DB created with one comparator is
  // accessed using a different comparator.
  //
  // The client of this package should switch to a new name whenever
  // the comparator implementation changes in a way that will cause
  // the relative ordering of any two keys to change.
  //
  // Names starting with "leveldb." are reserved and should not be used
  // by any clients of this package.
  fn name(&self) -> &str;
}

pub type SliceComparator = Comparator<Slice>;


// TODO: add singleton pattern for BytewiseComparator

pub struct BytewiseComparator {
}

impl Comparator<Slice> for BytewiseComparator {
  fn compare(&self, a: &Slice, b: &Slice) -> Ordering {
    a.compare(b)
  }

  fn name(&self) -> &str {
    "leveldb.BytewiseComparator"
  }
}
