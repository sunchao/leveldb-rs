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

use crate::comparator::SliceComparator;

/// DB contents are stored in a set of blocks, each of which holds a
/// sequence of key,value pairs.  Each block may be compressed before
/// being stored in a file.  The following enum describes which
/// compression method (if any) is used to compress a block.
pub enum CompressionType {
    NoCompression,
    SnappyCompression,
}

/// Options to control the behavior of a database (passed to DB::Open)
pub struct Options {
    /// Comparator used to define the order of keys in the table.
    /// Default: a comparator that uses lexicographic byte-wise ordering
    ///
    /// REQUIRES: The client must ensure that the comparator supplied
    /// here has the same name and orders keys *exactly* the same as the
    /// comparator provided to previous open calls on the same DB.
    comparator: Box<SliceComparator>,

    /// If true, the database will be created if it is missing.
    /// Default: false
    create_if_missing: bool,

    /// If true, an error is raised if the database already exists.
    /// Default: false
    error_if_exists: bool,

    /// If true, the implementation will do aggressive checking of the
    /// data it is processing and will stop early if it detects any
    /// errors.  This may have unforeseen ramifications: for example, a
    /// corruption of one DB entry may cause a large number of entries to
    /// become unreadable or for the entire DB to become unopenable.
    /// Default: false
    paranoid_checks: bool,

    // TODO: add env and info_log

    // -------------------
    // Parameters that affect performance
    /// Amount of data to build up in memory (backed by an unsorted log
    /// on disk) before converting to a sorted on-disk file.
    ///
    /// Larger values increase performance, especially during bulk loads.
    /// Up to two write buffers may be held in memory at the same time,
    /// so you may wish to adjust this parameter to control memory usage.
    /// Also, a larger write buffer will result in a longer recovery time
    /// the next time the database is opened.
    ///
    /// Default: 4MB
    write_buffer_size: usize,

    /// Number of open files that can be used by the DB.  You may need to
    /// increase this if your database has a large working set (budget
    /// one open file per 2MB of working set).
    ///
    /// Default: 1000
    max_open_files: i32,
}

/// Options that control read operations.
pub struct ReadOptions {
    /// If true, all data read from underlying storage will be verified against
    /// corresponding checksums.
    /// Default: false
    verify_checksums: bool,

    /// Should the data read for this iteration be cached in memory?
    /// Callers may wish to set this field to false for bulk scans.
    /// Default: true
    fill_cache: bool,
}

impl ReadOptions {
    pub fn new() -> Self {
        Self {
            verify_checksums: false,
            fill_cache: true,
        }
    }
}

/// Options that control write operations.
pub struct WriteOptions {
    /// If true, the write will be flushed from the OS buffer cache before the write is
    /// considered complete. If the flag is true, writes will be slower.
    ///
    /// If the flag is false, and the machine crashes, some recent writes may be lost.
    /// Note that if it is just the process that crashes (i.e., the machine does not
    /// reboot), no writes will be lost even if sync is false.
    ///
    /// In other words, a DB write with sync == false has similar crash semantics as the
    /// `write()` system call. A DB write with sync == true has similar crash semantics
    /// to a `write()` system call followed by `fsync()`.
    ///
    /// Default: false
    sync: bool,
}

impl WriteOptions {
    pub fn new() -> Self { Self { sync: false } }
}
