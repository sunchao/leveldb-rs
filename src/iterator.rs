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

use slice::Slice;

pub trait Iterator {
    /// An iterator is either positioned at a key/value pair, or
    /// invalid. This method returns true iff the iterator is valid.
    fn valid(&self) -> bool;

    /// Position at the first key in the source. The iterator is valid
    /// after this call iff the source is not empty.
    fn seek_to_first(&mut self);

    /// Position at the last key in the source. The iterator is valid
    /// after this call iff the source is not empty.
    fn seek_to_last(&mut self);

    /// Position at the first key in the source that is at or past target.
    /// The iterator is valid after this call iff the source contains
    /// an entry that comes at or past target.
    fn seek(&mut self, target: &Slice);

    /// Moves to the next entry in the source.  After this call, the iterator is
    /// valid iff the iterator was not positioned at the last entry in the source.
    /// REQUIRES: `valid()`
    fn next(&mut self);

    /// Moves to the previous entry in the source.  After this call, the iterator
    /// is valid iff the iterator was not positioned at the first entry in source.
    /// REQUIRES: `valid()`
    fn prev(&mut self);

    /// Return the key for the current entry.  The underlying storage for
    /// the returned slice is valid only until the next modification of
    /// the iterator.
    /// REQUIRES: `valid()`
    fn key(&self) -> Slice;

    /// Return the value for the current entry.  The underlying storage for
    /// the returned slice is valid only until the next modification of
    /// the iterator.
    /// REQUIRES: `valid()`
    fn value(&self) -> Slice;
}
