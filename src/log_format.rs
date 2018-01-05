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

use std::convert::TryFrom;

use result::{Error, ErrorType, Result};

#[derive(Clone, Copy, PartialEq)]
pub enum RecordType {
  ZERO = 0,
  FULL = 1,
  FIRST = 2,
  MIDDLE = 3,
  LAST = 4
}

impl TryFrom<i32> for RecordType {
  type Error = Error;
  fn try_from(i: i32) -> Result<Self> {
    match i {
      0 => Ok(RecordType::ZERO),
      1 => Ok(RecordType::FULL),
      2 => Ok(RecordType::FIRST),
      3 => Ok(RecordType::MIDDLE),
      4 => Ok(RecordType::LAST),
      _ => LEVELDB_ERR!(
        InvalidArgument,
        "Invalid input for RecordType. Valid range is [0, 4]"
      )
    }
  }
}

impl ::std::fmt::Display for RecordType {
  fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
    let str =
      match *self {
        RecordType::ZERO => "ZERO",
        RecordType::FULL => "FULL",
        RecordType::FIRST => "FIRST",
        RecordType::MIDDLE => "MIDDLE",
        RecordType::LAST => "LAST"
      };
    write!(f, "{}", str)
  }

}

pub const MAX_RECORD_TYPE: i32 = RecordType::LAST as i32;
pub const BLOCK_SIZE: usize = 32768;

// Header is checksum (4 bytes), length (2 bytes), type (1 byte).
pub const HEADER_SIZE: usize = 4 + 2 + 1;
