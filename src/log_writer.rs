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

use std::{convert::TryFrom, mem};

use crate::{
    env::WritableFile,
    log_format::{RecordType, BLOCK_SIZE, HEADER_SIZE, MAX_RECORD_TYPE},
    result::Result,
    slice::Slice,
    util::{coding, crc32c},
};

pub struct Writer {
    // The destination file to store the logs
    dest: Box<WritableFile>,

    // The current offset in block
    block_offset: usize,

    // crc32c values for all supported record types.
    // These are pre-computed to reduce the overhead of computing the crc of the record
    // type stored in the header.
    type_crc: [u32; (MAX_RECORD_TYPE + 1) as usize],
}

impl Writer {
    /// Create a writer that will append data to `dest`.
    /// `dest` must be initially empty.
    pub fn new(dest: Box<WritableFile>) -> Self { Self::new_with_dest_length(dest, 0) }

    /// Create a writer that will append data to `dest`.
    /// `dest` must have initial length `dest_length`.
    pub fn new_with_dest_length(dest: Box<WritableFile>, dest_length: usize) -> Self {
        let mut type_crc = [0; (MAX_RECORD_TYPE + 1) as usize];
        Writer::init_type_crc(&mut type_crc);
        Self {
            dest,
            block_offset: dest_length % BLOCK_SIZE as usize,
            type_crc,
        }
    }

    /// Consume this Writer and returns a tuple containing the current `block_offset` and
    /// the written file.
    pub fn consume(self) -> (usize, Box<WritableFile>) { (self.block_offset, self.dest) }

    pub fn add_record(&mut self, slice: &Slice) -> Result<()> {
        let mut data: &[u8] = slice.data();
        let mut left = slice.len();

        let mut begin = true;
        loop {
            assert!(BLOCK_SIZE as usize >= self.block_offset);
            let leftover = BLOCK_SIZE - self.block_offset;
            if leftover < HEADER_SIZE {
                // Switch to a new block
                // Fill the rest of the block with zero
                if leftover > 0 {
                    assert!(HEADER_SIZE == 7);
                    let slice =
                        Slice::from(&"\x00\x00\x00\x00\x00\x00"[..leftover as usize]);
                    self.dest.append(&slice)?;
                }
                self.block_offset = 0;
            }

            // Invariant: we never leave < HEADER_SIZE bytes in a block
            assert!(BLOCK_SIZE >= self.block_offset + HEADER_SIZE);

            let avail = BLOCK_SIZE - self.block_offset - HEADER_SIZE;
            let fragment_length = if left < avail { left } else { avail };

            let end = left == fragment_length;
            let ty: RecordType = if begin && end {
                RecordType::FULL
            } else if begin {
                RecordType::FIRST
            } else if end {
                RecordType::LAST
            } else {
                RecordType::MIDDLE
            };

            self.emit_physical_record(ty, &data[..fragment_length])?;
            data = &data[fragment_length..];
            left -= fragment_length;
            begin = false;

            if left <= 0 {
                break;
            }
        }

        Ok(())
    }

    fn emit_physical_record(&mut self, t: RecordType, data: &[u8]) -> Result<()> {
        let n = data.len();
        assert!(n <= 0xffff); // Must fit in two bytes
        assert!(self.block_offset + HEADER_SIZE + n <= BLOCK_SIZE);

        // Format the header
        let mut buf: [u8; HEADER_SIZE] = [0; HEADER_SIZE];
        buf[4] = (n & 0xff) as u8;
        buf[5] = (n >> 8) as u8;
        buf[6] = t as u8;

        let mut crc = crc32c::extend(self.type_crc[t as usize], data);
        crc = crc32c::mask(crc);
        coding::encode_fixed_32(&mut buf[..], crc);

        // Write the header and the payload
        self.dest.append(&Slice::from(&buf[..]))?;
        self.dest.append(&Slice::from(data))?;
        self.dest.flush()?;
        self.block_offset += HEADER_SIZE + n;

        Ok(())
    }

    fn init_type_crc(type_crc: &mut [u32]) {
        for h in 0..MAX_RECORD_TYPE + 1 {
            let v: [u8; 1] =
                unsafe { mem::transmute(RecordType::try_from(h).unwrap() as u8) };
            type_crc[h as usize] = crc32c::value(&v);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{cell::RefCell, error::Error as StdError, rc::Rc};

    use crate::{
        env::SequentialFile,
        log_reader::*,
        result::{Error, ErrorType, Result},
        util::{coding::encode_fixed_32, crc32c, random::Random},
    };

    struct StringDest {
        contents: Rc<RefCell<Vec<u8>>>,
    }

    impl StringDest {
        pub fn new(c: Rc<RefCell<Vec<u8>>>) -> Self { Self { contents: c } }
    }

    impl WritableFile for StringDest {
        fn close(&mut self) -> Result<()> { Ok(()) }

        fn flush(&mut self) -> Result<()> { Ok(()) }

        fn sync(&mut self) -> Result<()> { Ok(()) }

        fn append(&mut self, slice: &Slice) -> Result<()> {
            let mut contents = self.contents.borrow_mut();
            contents.extend_from_slice(slice.data());
            Ok(())
        }
    }

    struct StringSource {
        contents: Slice,
        force_error: bool,
        returned_partial: bool,
    }

    impl StringSource {
        pub fn new() -> Self {
            Self {
                contents: Slice::new_empty(),
                force_error: false,
                returned_partial: false,
            }
        }
    }

    impl SequentialFile for StringSource {
        fn read(&mut self, mut n: u64, _: &mut [u8]) -> Result<Slice> {
            assert!(!self.returned_partial, "must not read() after eof/error");

            if self.force_error {
                self.force_error = false;
                self.returned_partial = true;
                return LEVELDB_ERR!(Corruption, "read error");
            }

            if (self.contents.len() as u64) < n {
                n = self.contents.len() as u64;
                self.returned_partial = true;
            }
            let result = Slice::from(&self.contents.data()[..n as usize]);
            self.contents.skip(n as usize);
            Ok(result)
        }

        fn skip(&mut self, n: u64) -> Result<()> {
            if n > self.contents.len() as u64 {
                self.contents.clear();
                return LEVELDB_ERR!(NotFound, "in-memory file skipped past end");
            }
            self.contents.skip(n as usize);
            Ok(())
        }
    }

    struct ReportCollector {
        dropped_bytes: usize,
        message: String,
    }

    impl ReportCollector {
        pub fn new() -> Self {
            Self {
                dropped_bytes: 0,
                message: String::new(),
            }
        }
    }

    impl Reporter for ReportCollector {
        fn corruption(&mut self, bytes: usize, reason: Result<()>) {
            self.dropped_bytes += bytes;
            self.message.push_str(reason.err().unwrap().description())
        }
    }

    const INITIAL_OFFSET_RECORD_SIZES: [usize; 6] = [
        10000,
        10000,
        2 * BLOCK_SIZE - 1000,
        1,
        13716,
        BLOCK_SIZE - HEADER_SIZE,
    ];

    const INITIAL_OFFSET_LAST_RECORD_OFFSETS: [usize; 6] = [
        0,
        HEADER_SIZE + 10000,
        2 * (HEADER_SIZE + 10000),
        2 * (HEADER_SIZE + 10000) + (2 * BLOCK_SIZE - 1000) + 3 * HEADER_SIZE,
        2 * (HEADER_SIZE + 10000)
            + (2 * BLOCK_SIZE - 1000)
            + 3 * HEADER_SIZE
            + HEADER_SIZE
            + 1,
        3 * BLOCK_SIZE,
    ];

    struct LogTest {
        vec: Rc<RefCell<Vec<u8>>>,
        dest: StringDest,
        source: Rc<RefCell<StringSource>>,
        reporter: Rc<RefCell<ReportCollector>>,
        reading: bool,
        writer: Writer,
        reader: Reader,
    }

    impl LogTest {
        pub fn new() -> Self {
            let c = Rc::new(RefCell::new(Vec::new()));
            let sd = StringDest::new(c.clone());
            let ss = Rc::new(RefCell::new(StringSource::new()));
            let r = Rc::new(RefCell::new(ReportCollector::new()));

            Self {
                vec: c.clone(),
                dest: StringDest::new(c),
                source: ss.clone(),
                reporter: r.clone(),
                reading: false,
                writer: Writer::new(Box::new(sd)),
                reader: Reader::new(ss, Some(r), true, 0),
            }
        }

        pub fn read(&mut self) -> String {
            if !self.reading {
                self.reading = true;
                {
                    let mut source = self.source.borrow_mut();
                    source.contents = Slice::from(&self.dest.contents.borrow()[..]);
                }
            }

            let mut scratch = Vec::new();
            if let Some(record) = self.reader.read_record(&mut scratch) {
                record.to_string()
            } else {
                "EOF".to_string()
            }
        }

        pub fn write<'a>(&mut self, msg: &'a str) {
            assert!(!self.reading, "write() after starting to read");
            self.writer
                .add_record(&Slice::from(msg))
                .expect("add_record() should be OK");
        }

        pub fn written_bytes(&self) -> usize { self.dest.contents.borrow().len() }

        pub fn dropped_bytes(&self) -> usize { self.reporter.borrow().dropped_bytes }

        pub fn report_message(&self) -> String { self.reporter.borrow().message.clone() }

        pub fn reopen_for_append(&mut self) {
            let dest = StringDest::new(self.vec.clone());
            self.writer = Writer::new(Box::new(dest));
        }

        #[allow(dead_code)]
        pub fn force_error(&mut self) { self.source.borrow_mut().force_error = true; }

        pub fn match_error(&self, msg: &'static str) -> String {
            let reporter = self.reporter.borrow();
            if !reporter.message.contains(msg) {
                reporter.message.clone()
            } else {
                "OK".to_string()
            }
        }

        pub fn increment_bytes(&mut self, offset: i32, delta: u8) {
            self.dest.contents.borrow_mut()[offset as usize] += delta;
        }

        pub fn fix_checksum(&mut self, header_offset: usize, len: usize) {
            let mut contents = self.dest.contents.borrow_mut();
            let mut crc =
                crc32c::value(&contents[header_offset + 6..header_offset + 7 + len]);
            crc = crc32c::mask(crc);
            encode_fixed_32(&mut contents[header_offset..], crc);
        }

        pub fn shrink_size(&mut self, bytes: usize) {
            let mut contents = self.dest.contents.borrow_mut();
            let len = contents.len();
            contents.truncate(len - bytes);
        }

        pub fn set_byte(&mut self, offset: usize, new_byte: u8) {
            self.dest.contents.borrow_mut()[offset] = new_byte;
        }

        pub fn start_reading_at(&mut self, initial_offset: u64) {
            self.reader = Reader::new(
                self.source.clone(),
                Some(self.reporter.clone()),
                true,
                initial_offset,
            )
        }

        pub fn write_initial_offset_log(&mut self) {
            for i in 0..INITIAL_OFFSET_LAST_RECORD_OFFSETS.len() {
                let record = (0..INITIAL_OFFSET_RECORD_SIZES[i])
                    .map(|_| ('a' as u8 + i as u8) as char)
                    .collect::<String>();
                self.write(&record);
            }
        }

        pub fn check_initial_offset_record(
            &mut self,
            initial_offset: u64,
            mut expected_record_offset: usize,
        )
        {
            self.write_initial_offset_log();
            self.reading = true;
            {
                let mut source = self.source.borrow_mut();
                let contents = self.dest.contents.borrow();
                source.contents = Slice::from(&contents[..]);
            }
            let mut offset_reader = Reader::new(
                self.source.clone(),
                Some(self.reporter.clone()),
                true,
                initial_offset,
            );

            let num_initial_offset_records = INITIAL_OFFSET_RECORD_SIZES.len();
            assert!(expected_record_offset < num_initial_offset_records);
            loop {
                if expected_record_offset >= num_initial_offset_records {
                    break;
                }
                let mut scratch = Vec::new();
                let record = offset_reader
                    .read_record(&mut scratch)
                    .expect("read_record() should be OK");
                assert_eq!(
                    INITIAL_OFFSET_RECORD_SIZES[expected_record_offset],
                    record.len()
                );
                assert_eq!(
                    INITIAL_OFFSET_LAST_RECORD_OFFSETS[expected_record_offset],
                    offset_reader.last_record_offset() as usize
                );
                assert_eq!('a' as u8 + expected_record_offset as u8, record.data()[0]);
                expected_record_offset += 1;
            }
        }

        pub fn check_offset_past_end_returns_no_records(&mut self, offset_past_end: u64) {
            self.write_initial_offset_log();
            self.reading = true;
            {
                let mut source = self.source.borrow_mut();
                let contents = self.dest.contents.borrow();
                source.contents = Slice::from(&contents[..]);
            }
            let mut offset_reader = Reader::new(
                self.source.clone(),
                Some(self.reporter.clone()),
                true,
                self.written_bytes() as u64 + offset_past_end,
            );
            let mut scratch = Vec::new();
            assert!(offset_reader.read_record(&mut scratch).is_none());
        }
    }

    fn number_string(n: i32) -> String { n.to_string() }

    fn big_string<'a>(partial_str: &'a str, n: usize) -> String {
        let mut result = String::new();
        while result.len() < n {
            result.push_str(partial_str);
        }
        result.truncate(n);
        result
    }

    fn random_skewed_string(i: i32, rnd: &Random) -> String {
        big_string(&number_string(i), rnd.skewed(17) as usize)
    }

    #[test]
    pub fn empty() {
        let mut test = LogTest::new();
        assert_eq!("EOF".to_string(), test.read());
    }

    #[test]
    pub fn read_write() {
        let mut test = LogTest::new();
        test.write("foo");
        test.write("bar");
        test.write("");
        test.write("xxxx");
        assert_eq!("foo", test.read());
    }

    #[test]
    pub fn many_blocks() {
        let mut test = LogTest::new();
        for i in 0..100000 {
            test.write(&number_string(i));
        }
        for i in 0..100000 {
            assert_eq!(number_string(i), test.read());
        }
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn fragmentation() {
        let mut test = LogTest::new();
        test.write("small");
        test.write(&big_string("medium", 50000));
        test.write(&big_string("large", 100000));
        assert_eq!("small", test.read());
        assert_eq!(big_string("medium", 50000), test.read());
        assert_eq!(big_string("large", 100000), test.read());
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn marginal_trailer() {
        let mut test = LogTest::new();
        let n = BLOCK_SIZE - 2 * HEADER_SIZE;
        test.write(&big_string("foo", n));
        assert_eq!(BLOCK_SIZE - HEADER_SIZE, test.written_bytes());
        test.write("");
        test.write("bar");
        assert_eq!(big_string("foo", n), test.read());
        assert_eq!("", test.read());
        assert_eq!("bar", test.read());
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn marginal_trailer_2() {
        let mut test = LogTest::new();
        let n = BLOCK_SIZE - 2 * HEADER_SIZE;
        test.write(&big_string("foo", n));
        assert_eq!(BLOCK_SIZE - HEADER_SIZE, test.written_bytes());
        test.write("bar");
        assert_eq!(big_string("foo", n), test.read());
        assert_eq!("bar", test.read());
        assert_eq!("EOF", test.read());
        assert_eq!(0, test.dropped_bytes());
        assert_eq!("", test.report_message());
    }

    #[test]
    pub fn short_trailer() {
        let mut test = LogTest::new();
        let n = BLOCK_SIZE - 2 * HEADER_SIZE + 4;
        test.write(&big_string("foo", n));
        assert_eq!(BLOCK_SIZE - HEADER_SIZE + 4, test.written_bytes());
        test.write("");
        test.write("bar");
        assert_eq!(big_string("foo", n), test.read());
        assert_eq!("", test.read());
        assert_eq!("bar", test.read());
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn aligned_eof() {
        let mut test = LogTest::new();
        let n = BLOCK_SIZE - 2 * HEADER_SIZE + 4;
        test.write(&big_string("foo", n));
        assert_eq!(BLOCK_SIZE - HEADER_SIZE + 4, test.written_bytes());
        assert_eq!(big_string("foo", n), test.read());
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn open_for_append() {
        let mut test = LogTest::new();
        test.write("hello");
        test.reopen_for_append();
        test.write("world");
        assert_eq!("hello", test.read());
        assert_eq!("world", test.read());
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn rand_read() {
        let mut test = LogTest::new();
        let n = 500;
        let write_rnd = Random::new(301);
        for i in 0..n {
            test.write(&random_skewed_string(i, &write_rnd));
        }
        let read_rnd = Random::new(301);
        for i in 0..n {
            assert_eq!(random_skewed_string(i, &read_rnd), test.read());
        }
        assert_eq!("EOF", test.read());
    }

    // Test all error cases in log_reader.rs follow:

    // TODO: this fails because the second condition in `Reader::report_drop()` is false.
    // interestingly in LevelDB CPP this works because the negative result is implicitly
    // converted to uint64_t, and thus always greater than 0. It could be a bug.
    #[allow(dead_code)]
    pub fn read_error() {
        let mut test = LogTest::new();
        test.write("foo");
        test.force_error();
        assert_eq!("EOF", test.read());
        assert_eq!(BLOCK_SIZE, test.dropped_bytes());
        assert_eq!("OK", test.match_error("read error"));
    }

    #[test]
    pub fn bad_record_type() {
        let mut test = LogTest::new();
        test.write("foo");
        test.increment_bytes(6, 100);
        test.fix_checksum(0, 3);
        assert_eq!("EOF", test.read());
        assert_eq!(3, test.dropped_bytes());
    }

    #[test]
    pub fn truncated_trailing_record_is_ignored() {
        let mut test = LogTest::new();
        test.write("foo");
        test.shrink_size(4);
        assert_eq!("EOF", test.read());
        assert_eq!(0, test.dropped_bytes());
        assert_eq!("", test.report_message());
    }

    #[test]
    pub fn bad_length() {
        let mut test = LogTest::new();
        let payload_size = BLOCK_SIZE - HEADER_SIZE;
        test.write(&big_string("bar", payload_size));
        test.write("foo");
        test.increment_bytes(4, 1);
        assert_eq!("foo", test.read());
        assert_eq!(BLOCK_SIZE, test.dropped_bytes());
        assert_eq!("OK", test.match_error("bad record length"));
    }

    #[test]
    pub fn bad_length_at_end_is_ignored() {
        let mut test = LogTest::new();
        test.write("foo");
        test.shrink_size(1);
        assert_eq!("EOF", test.read());
        assert_eq!(0, test.dropped_bytes());
        assert_eq!("", test.report_message());
    }

    #[test]
    pub fn checksum_mismatch() {
        let mut test = LogTest::new();
        test.write("foo");
        test.increment_bytes(0, 10);
        assert_eq!("EOF", test.read());
        assert_eq!(10, test.dropped_bytes());
        assert_eq!("OK", test.match_error("checksum mismatch"));
    }

    #[test]
    pub fn unexpected_middle_type() {
        let mut test = LogTest::new();
        test.write("foo");
        test.set_byte(6, RecordType::MIDDLE as u8);
        test.fix_checksum(0, 3);
        assert_eq!("EOF", test.read());
        assert_eq!(3, test.dropped_bytes());
        assert_eq!("OK", test.match_error("missing start"));
    }

    #[test]
    pub fn unexpected_last_type() {
        let mut test = LogTest::new();
        test.write("foo");
        test.set_byte(6, RecordType::LAST as u8);
        test.fix_checksum(0, 3);
        assert_eq!("EOF", test.read());
        assert_eq!(3, test.dropped_bytes());
        assert_eq!("OK", test.match_error("missing start"));
    }

    #[test]
    pub fn unexpected_full_type() {
        let mut test = LogTest::new();
        test.write("foo");
        test.write("bar");
        test.set_byte(6, RecordType::FIRST as u8);
        test.fix_checksum(0, 3);
        assert_eq!("bar", test.read());
        assert_eq!("EOF", test.read());
        assert_eq!(3, test.dropped_bytes());
        assert_eq!("OK", test.match_error("partial record without end"));
    }

    #[test]
    pub fn unexpected_first_type() {
        let mut test = LogTest::new();
        test.write("foo");
        test.write(&big_string("bar", 100000));
        test.set_byte(6, RecordType::FIRST as u8);
        test.fix_checksum(0, 3);
        assert_eq!(big_string("bar", 100000), test.read());
        assert_eq!("EOF", test.read());
        assert_eq!(3, test.dropped_bytes());
        assert_eq!("OK", test.match_error("partial record without end"));
    }

    #[test]
    pub fn missing_last_is_ignored() {
        let mut test = LogTest::new();
        test.write(&big_string("bar", BLOCK_SIZE));
        test.shrink_size(14);
        assert_eq!("EOF", test.read());
        assert_eq!(0, test.dropped_bytes());
        assert_eq!("", test.report_message());
    }

    #[test]
    pub fn partial_last_is_ignored() {
        let mut test = LogTest::new();
        test.write(&big_string("bar", BLOCK_SIZE));
        test.shrink_size(1);
        assert_eq!("EOF", test.read());
        assert_eq!(0, test.dropped_bytes());
        assert_eq!("", test.report_message());
    }

    #[test]
    pub fn skip_into_multi_record() {
        let mut test = LogTest::new();
        test.write(&big_string("foo", 3 * BLOCK_SIZE));
        test.write("correct");
        test.start_reading_at(BLOCK_SIZE as u64);

        assert_eq!("correct", test.read());
        assert_eq!(0, test.dropped_bytes());
        assert_eq!("", test.report_message());
        assert_eq!("EOF", test.read());
    }

    #[test]
    pub fn error_joins_record() {
        let mut test = LogTest::new();

        // Consider two fragmented records:
        //    first(R1) last(R1) first(R2) last(R2)
        // where the middle two fragments disappear.  We do not want
        // first(R1),last(R2) to get joined and returned as a valid record.

        // Write records that span two blocks
        test.write(&big_string("foo", BLOCK_SIZE));
        test.write(&big_string("bar", BLOCK_SIZE));
        test.write("correct");

        // Wipe the middle block
        for offset in BLOCK_SIZE..2 * BLOCK_SIZE {
            test.set_byte(offset, 'x' as u8);
        }

        assert_eq!("correct", test.read());
        assert_eq!("EOF", test.read());
        let dropped = test.dropped_bytes();
        assert!(dropped <= 2 * BLOCK_SIZE + 100);
        assert!(dropped >= 2 * BLOCK_SIZE);
    }

    #[test]
    pub fn read_start() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(0, 0);
    }

    #[test]
    pub fn read_second_one_off() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(1, 1);
    }

    #[test]
    pub fn read_second_ten_thousand() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(10000, 1);
    }

    #[test]
    pub fn read_second_start() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(10007, 1);
    }

    #[test]
    pub fn read_third_one_off() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(10008, 2);
    }

    #[test]
    pub fn read_third_start() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(20014, 2);
    }

    #[test]
    pub fn read_fourth_one_off() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(20015, 3);
    }

    #[test]
    pub fn read_fourth_first_block_trailer() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(BLOCK_SIZE as u64 - 4, 3);
    }

    #[test]
    pub fn read_fourth_middle_block() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(BLOCK_SIZE as u64 + 1, 3);
    }

    #[test]
    pub fn read_fourth_last_block() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(2 * (BLOCK_SIZE as u64) + 1, 3);
    }

    #[test]
    pub fn read_fourth_start() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(
            (2 * (HEADER_SIZE + 10000) + (2 * BLOCK_SIZE - 1000) + 3 * HEADER_SIZE)
                as u64,
            3,
        );
    }

    #[test]
    pub fn read_initial_offset_into_block_padding() {
        let mut test = LogTest::new();
        test.check_initial_offset_record(3 * (BLOCK_SIZE as u64) - 3, 5);
    }

    #[test]
    pub fn read_end() {
        let mut test = LogTest::new();
        test.check_offset_past_end_returns_no_records(0);
    }

    #[test]
    pub fn read_past_end() {
        let mut test = LogTest::new();
        test.check_offset_past_end_returns_no_records(5);
    }
}
