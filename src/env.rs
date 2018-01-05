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

use std::rc::Rc;
use std::cell::RefCell;

use slice::Slice;
use result::Result;

pub trait WritableFile {
  fn append(&mut self, data: &Slice) -> Result<()>;
  fn close(&mut self) -> Result<()>;
  fn flush(&mut self) -> Result<()>;
  fn sync(&mut self) -> Result<()>;
}

pub type SequentialFileRef = Rc<RefCell<SequentialFile>>;

pub trait SequentialFile {
  /// Read up to `n` bytes from the file, and store them in `scratch`.
  ///
  /// Return a slice points to the data in `scratch`, whose lifetime must
  /// be longer than the slice.
  fn read(&mut self, n: u64, scratch: &mut [u8]) -> Result<Slice>;

  /// Skip `n` bytes from the file.
  fn skip(&mut self, n: u64) -> Result<()>;
}
