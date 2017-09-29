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

use std::convert::From;

#[derive(Debug)]
pub enum ErrorKind {
  NotFound,
  Corruption,
  NotSupported,
  InvalidArgument,
  IOError
}

impl ErrorKind {
  pub fn as_str(&self) -> &'static str {
    match *self {
      ErrorKind::NotFound => "not found",
      ErrorKind::Corruption => "corruption",
      ErrorKind::NotSupported => "not supported",
      ErrorKind::InvalidArgument => "invalid argument",
      ErrorKind::IOError => "IO error"
    }
  }
}

#[derive(Debug)]
pub struct Error {
  kind: ErrorKind
}

impl From<ErrorKind> for Error {
  fn from(k: ErrorKind) -> Error {
    Error {
      kind: k
    }
  }
}

impl ::std::fmt::Display for Error {
  fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
    write!(f, "LevelDB Error: {}", self.kind.as_str())
  }
}

impl ::std::error::Error for Error {
  fn description(&self) -> &str {
    self.kind.as_str()
  }
}

pub type Result<T> = ::std::result::Result<T, Error>;
