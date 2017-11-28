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

#[derive(Debug)]
pub enum ErrorType {
  NotFound,
  Corruption,
  NotSupported,
  InvalidArgument,
  IOError
}

impl ErrorType {
  pub fn as_str(&self) -> &'static str {
    match *self {
      ErrorType::NotFound => "NotFoundError",
      ErrorType::Corruption => "CorruptionError",
      ErrorType::NotSupported => "NotSupportedError",
      ErrorType::InvalidArgument => "InvalidArgumentError",
      ErrorType::IOError => "IOError",
    }
  }
}

#[derive(Debug)]
pub struct Error {
  ty: ErrorType,
  msg: &'static str
}

impl Error {
  pub fn new(ty: ErrorType, msg: &'static str) -> Error {
    Error { ty: ty, msg: msg }
  }
}

impl ::std::fmt::Display for Error {
  fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
    if self.msg.is_empty() {
      write!(f, "LevelDB {}", self.ty.as_str())
    } else {
      write!(f, "LevelDB {}: {}", self.ty.as_str(), self.msg)
    }
  }
}

impl ::std::error::Error for Error {
  fn description(&self) -> &str {
    self.msg
  }
}

pub type Result<T> = ::std::result::Result<T, Error>;

macro_rules! LEVELDB_ERR {
  ($tp:tt) => (Err(Error::new(ErrorType::$tp, "")));
  ($tp:tt, $msg:expr) => (Err(Error::new(ErrorType::$tp, $msg)));
}
