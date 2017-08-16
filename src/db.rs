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


pub trait DB {
  fn open(name: &str) -> Self;

  /// Set the database entry for `key` to `value`.
  /// Return OK on success, and Err on error.
  /// TODO: add WriteOptions as parameter
  fn put(key: &Slice, value: &Slice) -> Result<()>;

  /// Remove the database entry (if any) for `key`.
  /// Return OK on success, and Err on error.
  /// Note that it is not an error if `key` does not exist in
  /// the database.
  /// TODO: add WriteOptions as parameter
  fn delete(key: &Slice) -> Result<()>;

  /// If the database contains an entry for `key`, return OK with the corresponding
  /// value. If there's no entry for `key`, return `Err::IsNotFound`.
  /// This may also return other Err on error.
  fn get(key: &Slice) -> Result<&str>;
}
