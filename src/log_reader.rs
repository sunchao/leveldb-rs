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

use std::{cell::RefCell, convert::TryFrom, rc::Rc};

use crate::{
    env::SequentialFileRef,
    log_format::{RecordType, BLOCK_SIZE, HEADER_SIZE, MAX_RECORD_TYPE},
    result::{Error, ErrorType, Result},
    slice::Slice,
    util::{coding, crc32c},
};

pub const EOF: i32 = MAX_RECORD_TYPE + 1;

/// Returned whenever we find an invalid physical record.
/// There are 3 cases:
///   - the record has an invalid CRC (`read_physical_record()` reports a drop)
///   - the record is a 0-length record (no drop is reported)
///   - the record is below constructor's `initial_offset` (no drop is reported)
pub const BAD_RECORD: i32 = MAX_RECORD_TYPE + 2;

pub trait Reporter {
    /// Some corruption was detected. `bytes` is the approximate number of bytes dropped
    /// due to the corruption.
    /// Note: `reason` is a result of `()` here since we only care about the `Err` case.
    fn corruption(&mut self, bytes: usize, reason: Result<()>);
}

pub struct Reader {
    file: SequentialFileRef,
    reporter: Option<Rc<RefCell<Reporter>>>,
    checksum: bool,
    backing_store: [u8; BLOCK_SIZE],
    buffer: Slice,
    eof: bool,

    // Offset of the last record returned by `read_record()`
    last_record_offset: u64,

    // Offset of the first location past the end of `buffer`
    end_of_buffer_offset: u64,

    // Offset at which to start looking for the first record to return
    initial_offset: u64,

    // True if we are resynchronizing after a seek (`initial_offset` > 0). In particular,
    // a run of `RecordType.Middle` and `RecordType.Last` records can be silently skipped
    // in this mode.
    resyncing: bool,
}

impl Reader {
    /// Create a reader that will return log records from `file`.
    ///
    /// If `reporter` is not `None`, it is notified whenever some data is dropped to a
    /// detected corruption.
    /// If `checksum` is true, verify checksums if available.
    /// The Reader will start reading at the first record located at physical
    /// location >= `initial_offset` within the file.
    pub fn new(
        file: SequentialFileRef,
        reporter: Option<Rc<RefCell<Reporter>>>,
        checksum: bool,
        initial_offset: u64,
    ) -> Self
    {
        Self {
            file,
            reporter,
            checksum,
            backing_store: [0; BLOCK_SIZE],
            buffer: Slice::new_empty(),
            eof: false,
            last_record_offset: 0,
            end_of_buffer_offset: 0,
            initial_offset,
            resyncing: initial_offset > 0,
        }
    }

    /// Returns the physical offset of the last record returned by `read_record()`
    ///
    /// The result is undefined before the first call to `read_record()`.
    pub fn last_record_offset(&self) -> u64 { self.last_record_offset }

    fn report_drop(&mut self, bytes: u64, reason: Result<()>) {
        if let Some(ref mut reporter) = self.reporter {
            if self.end_of_buffer_offset
                >= self.buffer.size() as u64 + bytes + self.initial_offset
            {
                reporter.borrow_mut().corruption(bytes as usize, reason);
            }
        }
    }

    fn report_corruption<'a>(&mut self, bytes: u64, reason: &'static str) {
        self.report_drop(bytes, LEVELDB_ERR!(Corruption, reason))
    }

    /// Read the next record and potentially returns a slice for it.
    ///
    /// This returns `Some(slice)` if the read is successful, `None` if it hit the end of
    /// the input. The contents is read into `scratch`, whose lifetime must be longer than
    /// the returned slice.
    pub fn read_record(&mut self, scratch: &mut Vec<u8>) -> Option<Slice> {
        if self.last_record_offset < self.initial_offset {
            if !self.skip_to_initial_block() {
                return None;
            }
        }

        scratch.clear();
        let mut in_fragmented_record = false;
        let mut prospective_record_offset = 0;

        loop {
            let (record_type, record_result) = self.read_physical_record();
            let fragment_size: u64 = if record_result.is_some() {
                record_result.as_ref().unwrap().size() as u64
            } else {
                0
            };

            // The offset for the last record from `read_physical_record`.
            // Notice that we need to add HEADER_SIZE and `fragment_size` since
            // these are removed from the `buffer`.
            // Also note this could be negative so using `i64` here.
            let physical_record_offset: i64 = self.end_of_buffer_offset as i64
                - self.buffer.size() as i64
                - HEADER_SIZE as i64
                - fragment_size as i64;

            if self.resyncing {
                if record_type == RecordType::MIDDLE as i32 {
                    continue;
                } else if record_type == RecordType::LAST as i32 {
                    self.resyncing = false;
                    continue;
                } else {
                    self.resyncing = false;
                }
            }

            if record_type == EOF {
                if in_fragmented_record {
                    // This can be caused by the writer dying immediately after writing a
                    // physical record but before completing the next
                    // one; don't treat it as a corruption,
                    // just ignore the entire logical record.
                    scratch.clear();
                }
                return None;
            } else if record_type == BAD_RECORD {
                if in_fragmented_record {
                    self.report_corruption(
                        scratch.len() as u64,
                        "error in middle of record",
                    );
                    in_fragmented_record = false;
                    scratch.clear();
                }
            } else {
                assert!(record_result.is_some());
                let fragment = record_result.unwrap();
                let scratch_size = if in_fragmented_record {
                    scratch.len()
                } else {
                    0
                };

                if let Ok(tp) = RecordType::try_from(record_type) {
                    match tp {
                        RecordType::FULL => {
                            if in_fragmented_record {
                                self.report_corruption(
                                    scratch.len() as u64,
                                    "partial record without end(1)",
                                );
                            }

                            assert!(physical_record_offset >= 0);
                            prospective_record_offset = physical_record_offset;
                            self.last_record_offset = prospective_record_offset as u64;
                            return Some(fragment);
                        },

                        RecordType::FIRST => {
                            if in_fragmented_record {
                                self.report_corruption(
                                    scratch.len() as u64,
                                    "partial record without end(2)",
                                );
                            }
                            prospective_record_offset = physical_record_offset;
                            scratch.clear();
                            scratch.extend_from_slice(fragment.data());
                            in_fragmented_record = true;
                        },

                        RecordType::MIDDLE => {
                            if !in_fragmented_record {
                                self.report_corruption(
                                    fragment.size() as u64,
                                    "missing start of fragmented record(1)",
                                )
                            } else {
                                scratch.extend_from_slice(fragment.data());
                            }
                        },

                        RecordType::LAST => {
                            if !in_fragmented_record {
                                self.report_corruption(
                                    fragment.size() as u64,
                                    "missing start of fragmented record(2)",
                                );
                            } else {
                                scratch.extend_from_slice(fragment.data());
                                let record = Slice::from(&scratch[..]);
                                assert!(physical_record_offset >= 0);
                                self.last_record_offset =
                                    prospective_record_offset as u64;
                                return Some(record);
                            }
                        },

                        _ => {
                            // TODO: include the type in error message ('static str makes
                            // it tricky)
                            self.report_corruption(
                                (fragment.size() + scratch_size) as u64,
                                "unexpected record type",
                            );
                            in_fragmented_record = false;
                            scratch.clear();
                        },
                    }
                } else {
                    // TODO: include the type in error message ('static str makes it
                    // tricky)
                    self.report_corruption(
                        (fragment.size() + scratch_size) as u64,
                        "unknown record type",
                    );
                    in_fragmented_record = false;
                    scratch.clear();
                }
            }
        }
    }

    /// Read the next physical record and return a tuple where the first element is the
    /// integer representation of the record type, and the second element is an option
    /// containing the slice. The latter is only `Some` iff the record type is valid
    /// (e.g., NOT `EOF` or `BAD_RECORD`)
    fn read_physical_record(&mut self) -> (i32, Option<Slice>) {
        loop {
            if self.buffer.size() < HEADER_SIZE {
                if !self.eof {
                    // Last read was a full read, so this is a trailer to skip
                    self.buffer.clear();
                    let result = {
                        let mut file = self.file.borrow_mut();
                        file.read(BLOCK_SIZE as u64, &mut self.backing_store)
                    };
                    if !result.is_ok() {
                        self.report_drop(BLOCK_SIZE as u64, result.map(|_| {}));
                        self.eof = true;
                        return (EOF, None);
                    } else {
                        let buf = result.unwrap();
                        self.end_of_buffer_offset += buf.size() as u64;
                        self.buffer = buf;
                        if self.buffer.size() < BLOCK_SIZE as usize {
                            self.eof = true
                        }
                    }
                    continue;
                } else {
                    // If buffer is non-empty, it means we have a truncated header at the
                    // end of the file, which may be caused by writer
                    // crashing in the middle of writing the header.
                    // Instead of considering this an error, just report EOF.
                    self.buffer.clear();
                    return (EOF, None);
                }
            }

            // Parse the header
            let buffer_copy = self.buffer.clone();
            let header = buffer_copy.data();
            let a = header[4] & 0xff;
            let b = header[5] & 0xff;
            let tp = header[6] as i32;
            let length = (a as u32 | ((b as u32) << 8)) as usize;

            if HEADER_SIZE + length > self.buffer.size() {
                let drop_size = self.buffer.size() as u64;
                self.buffer.clear();
                if !self.eof {
                    self.report_corruption(drop_size, "bad record length");
                    return (BAD_RECORD, None);
                }

                // If the EOF has been reached without reading |length| bytes of payload,
                // assume the writer died in the middle of writing the record.
                // don't report a corruption.
                return (EOF, None);
            }

            if tp == (RecordType::ZERO as i32) && length == 0 {
                // TODO: double check here
                // Skip zero length record without reporting any drop.
                self.buffer.clear();
                return (BAD_RECORD, None);
            }

            // Check crc
            if self.checksum {
                let expected_crc = crc32c::unmask(coding::decode_fixed_32(header));
                let actual_crc = crc32c::value(&header[6..(7 + length as usize)]);
                if expected_crc != actual_crc {
                    let drop_size = self.buffer.size() as u64;
                    self.buffer.clear();
                    self.report_corruption(drop_size, "checksum mismatch");
                    return (BAD_RECORD, None);
                }
            }

            self.buffer.remove_prefix(HEADER_SIZE + (length as usize));

            // Skip physical record that started before initial_offset
            if (self.end_of_buffer_offset
                - self.buffer.size() as u64
                - HEADER_SIZE as u64
                - length as u64)
                < self.initial_offset
            {
                return (BAD_RECORD, None);
            }

            return (
                tp,
                Some(Slice::from(
                    &header[HEADER_SIZE..(HEADER_SIZE + (length as usize))],
                )),
            );
        }
    }

    /// Skips all blocks that are completely before `initial_offset`
    ///
    /// Returns true on success. Handles reporting.
    fn skip_to_initial_block(&mut self) -> bool {
        let offset_in_block = self.initial_offset % (BLOCK_SIZE as u64);
        let mut block_start_location = self.initial_offset - offset_in_block;

        // Don't search a block if we'd be in the trailer
        if offset_in_block > BLOCK_SIZE as u64 - 6 {
            block_start_location += BLOCK_SIZE as u64;
        }

        self.end_of_buffer_offset = block_start_location;

        if block_start_location > 0 {
            let result = {
                let mut file = self.file.borrow_mut();
                file.skip(block_start_location)
            };
            if !result.is_ok() {
                self.report_drop(block_start_location, result);
                return false;
            }
        }

        true
    }
}
