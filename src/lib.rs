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

#![feature(box_syntax)]
#![feature(rustc_private)]
#![feature(nll)]

extern crate arena;
extern crate crossbeam;
#[macro_use]
extern crate lazy_static;
extern crate byteorder;

pub mod env;
pub mod util;
#[macro_use]
pub mod result;
pub mod comparator;
pub mod config;
pub mod dbformat;
pub mod iterator;
pub mod log_format;
pub mod log_reader;
pub mod log_writer;
pub mod memtable;
pub mod skiplist;
pub mod slice;
pub mod version_edit;
pub mod write_batch;
