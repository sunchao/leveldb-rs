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

use std::{
    collections::BTreeSet,
    convert::TryFrom,
    fmt::{Debug, Formatter, Result as DebugResult},
};

use crate::{
    config,
    dbformat::{InternalKey, SequenceNumber},
    result::{Error, ErrorType, Result},
    slice::Slice,
    util::coding,
};

enum Tag {
    Comparator = 1,
    LogNumber = 2,
    NextFileNumber = 3,
    LastSequence = 4,
    CompactPointer = 5,
    DeletedFile = 6,
    NewFile = 7,
    // 8 was used for large value refs
    PrevLogNumber = 9,
}

impl TryFrom<u8> for Tag {
    type Error = Error;

    fn try_from(t: u8) -> Result<Tag> {
        match t {
            1 => Ok(Tag::Comparator),
            2 => Ok(Tag::LogNumber),
            3 => Ok(Tag::NextFileNumber),
            4 => Ok(Tag::LastSequence),
            5 => Ok(Tag::CompactPointer),
            6 => Ok(Tag::DeletedFile),
            7 => Ok(Tag::NewFile),
            9 => Ok(Tag::PrevLogNumber),
            _ => LEVELDB_ERR!(InvalidArgument, "undefined value for Tag"),
        }
    }
}

// TODO: remove the dead_code annotation
pub struct FileMetaData {
    #[allow(dead_code)]
    refs: i32,
    #[allow(dead_code)]
    allowed_seeks: i32, // Seeks allowed until compaction
    number: u64,
    file_size: u64,        // File size in bytes
    smallest: InternalKey, // Smallest internal key served by table
    largest: InternalKey,  // Largest internal key served by table
}

impl FileMetaData {
    pub fn new(
        number: u64,
        file_size: u64,
        smallest: InternalKey,
        largest: InternalKey,
    ) -> Self
    {
        Self {
            refs: 0,
            allowed_seeks: 1 << 30,
            number,
            file_size,
            smallest,
            largest,
        }
    }
}

type DeletedFileSet = BTreeSet<(i32, u64)>;

pub struct VersionEdit {
    comparator: String,
    log_number: u64,
    prev_log_number: u64,
    next_file_number: u64,
    last_sequence: SequenceNumber,
    has_comparator: bool,
    has_log_number: bool,
    has_prev_log_number: bool,
    has_next_file_number: bool,
    has_last_sequence: bool,

    compact_pointers: Vec<(i32, InternalKey)>,
    deleted_files: DeletedFileSet,
    new_files: Vec<(i32, FileMetaData)>,
}

impl VersionEdit {
    pub fn new() -> Self {
        Self {
            comparator: String::new(), // empty string is used as dummy initial value
            log_number: 0,
            prev_log_number: 0,
            next_file_number: 0,
            last_sequence: 0,
            has_comparator: false,
            has_log_number: false,
            has_prev_log_number: false,
            has_next_file_number: false,
            has_last_sequence: false,
            compact_pointers: Vec::new(),
            deleted_files: BTreeSet::new(),
            new_files: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.comparator.clear();
        self.log_number = 0;
        self.prev_log_number = 0;
        self.next_file_number = 0;
        self.last_sequence = 0;
        self.has_comparator = false;
        self.has_prev_log_number = false;
        self.has_next_file_number = false;
        self.has_last_sequence = false;
    }

    pub fn set_comparator_name(&mut self, name: &'static str) {
        self.has_comparator = true;
        self.comparator = String::from(name);
    }

    pub fn set_log_number(&mut self, num: u64) {
        self.has_log_number = true;
        self.log_number = num;
    }

    pub fn set_prev_log_number(&mut self, num: u64) {
        self.has_prev_log_number = true;
        self.prev_log_number = num;
    }

    pub fn set_next_file(&mut self, num: u64) {
        self.has_next_file_number = true;
        self.next_file_number = num;
    }

    pub fn set_last_sequence(&mut self, seq: SequenceNumber) {
        self.has_last_sequence = true;
        self.last_sequence = seq;
    }

    pub fn set_compact_pointer(&mut self, level: i32, key: InternalKey) {
        self.compact_pointers.push((level, key));
    }

    /// Add the specified file at the specified number.
    /// REQUIRES: this version has not been saved (see `version_set::save_to()`)
    /// REQUIRES: `smallest` and `largest` are smallest and largest keys in the file
    pub fn add_file(
        &mut self,
        level: i32,
        file: u64,
        file_size: u64,
        smallest: InternalKey,
        largest: InternalKey,
    )
    {
        let f = FileMetaData::new(file, file_size, smallest, largest);
        self.new_files.push((level, f));
    }

    pub fn delete_file(&mut self, level: i32, file: u64) {
        self.deleted_files.insert((level, file));
    }

    pub fn encode_to(&self, dst: &mut Vec<u8>) {
        if self.has_comparator {
            coding::encode_varint_32_vec(dst, Tag::Comparator as u32);
            coding::encode_length_prefixed_slice(
                dst,
                &Slice::from(self.comparator.as_str()),
            );
        }
        if self.has_log_number {
            coding::encode_varint_32_vec(dst, Tag::LogNumber as u32);
            coding::encode_varint_64_vec(dst, self.log_number);
        }
        if self.has_prev_log_number {
            coding::encode_varint_32_vec(dst, Tag::PrevLogNumber as u32);
            coding::encode_varint_64_vec(dst, self.prev_log_number);
        }
        if self.has_next_file_number {
            coding::encode_varint_32_vec(dst, Tag::NextFileNumber as u32);
            coding::encode_varint_64_vec(dst, self.next_file_number);
        }
        if self.has_last_sequence {
            coding::encode_varint_32_vec(dst, Tag::LastSequence as u32);
            coding::encode_varint_64_vec(dst, self.last_sequence);
        }
        for &(l, ref p) in self.compact_pointers.iter() {
            coding::encode_varint_32_vec(dst, Tag::CompactPointer as u32);
            coding::encode_varint_32_vec(dst, l as u32);
            coding::encode_length_prefixed_slice(dst, &p.encode());
        }
        for &(l, n) in self.deleted_files.iter() {
            coding::encode_varint_32_vec(dst, Tag::DeletedFile as u32);
            coding::encode_varint_32_vec(dst, l as u32);
            coding::encode_varint_64_vec(dst, n);
        }
        for &(l, ref f) in self.new_files.iter() {
            coding::encode_varint_32_vec(dst, Tag::NewFile as u32);
            coding::encode_varint_32_vec(dst, l as u32);
            coding::encode_varint_64_vec(dst, f.number);
            coding::encode_varint_64_vec(dst, f.file_size);
            coding::encode_length_prefixed_slice(dst, &f.smallest.encode());
            coding::encode_length_prefixed_slice(dst, &f.largest.encode());
        }
    }

    pub fn decode_from(&mut self, src: &Slice) -> Result<()> {
        self.clear();

        let mut input = src.clone();
        let mut msg = None;
        loop {
            if msg.is_some() {
                // Missing some tag
                break;
            }
            let tag_num = coding::decode_varint_32_slice(&mut input);
            if tag_num.is_err() {
                // No more input
                break;
            }
            if let Ok(tag) = Tag::try_from(tag_num.unwrap() as u8) {
                match tag {
                    Tag::Comparator => {
                        let s = coding::decode_length_prefixed_slice(&mut input)?;
                        self.comparator = s.to_string();
                        self.has_comparator = true;
                    },
                    Tag::LogNumber => {
                        let log_number = coding::decode_varint_64_slice(&mut input)?;
                        self.has_log_number = true;
                        self.log_number = log_number;
                    },
                    Tag::PrevLogNumber => {
                        let prev_log_number = coding::decode_varint_64_slice(&mut input)?;
                        self.has_prev_log_number = true;
                        self.prev_log_number = prev_log_number;
                    },
                    Tag::NextFileNumber => {
                        let next_file_number =
                            coding::decode_varint_64_slice(&mut input)?;
                        self.has_next_file_number = true;
                        self.next_file_number = next_file_number;
                    },
                    Tag::LastSequence => {
                        let last_sequence = coding::decode_varint_64_slice(&mut input)?;
                        self.has_last_sequence = true;
                        self.last_sequence = last_sequence;
                    },
                    Tag::CompactPointer => {
                        let maybe_level = get_level(&mut input)?;
                        let maybe_key = get_internal_key(&mut input)?;
                        self.compact_pointers.push((maybe_level, maybe_key));
                    },
                    Tag::DeletedFile => {
                        let maybe_level = get_level(&mut input)?;
                        let maybe_num = coding::decode_varint_64_slice(&mut input)?;
                        self.deleted_files.insert((maybe_level, maybe_num));
                    },
                    Tag::NewFile => {
                        let maybe_level = get_level(&mut input)?;
                        let maybe_num = coding::decode_varint_64_slice(&mut input)?;
                        let maybe_file_size = coding::decode_varint_64_slice(&mut input)?;
                        let maybe_smallest = get_internal_key(&mut input)?;
                        let maybe_largest = get_internal_key(&mut input)?;
                        let f = FileMetaData::new(
                            maybe_num,
                            maybe_file_size,
                            maybe_smallest,
                            maybe_largest,
                        );
                        self.new_files.push((maybe_level, f));
                    },
                }
            } else {
                msg = Some("unknown tag");
            }
        }

        if msg.is_none() && !input.empty() {
            msg = Some("invalid tag")
        }

        if msg.is_some() {
            LEVELDB_ERR!(Corruption, msg.unwrap())
        } else {
            Ok(())
        }
    }
}

impl Debug for VersionEdit {
    fn fmt(&self, f: &mut Formatter) -> DebugResult {
        write!(f, "VersionEdit {{")?;
        if self.has_comparator {
            write!(f, "\n  Comparator: {}", self.comparator)?;
        }
        if self.has_log_number {
            write!(f, "\n  LogNumber: {}", self.log_number)?;
        }
        if self.has_prev_log_number {
            write!(f, "\n  PrevLogNumber: {}", self.prev_log_number)?;
        }
        if self.has_next_file_number {
            write!(f, "\n  NextFile: {}", self.next_file_number)?;
        }
        if self.has_last_sequence {
            write!(f, "\n  LastSeq: {}", self.last_sequence)?;
        }
        for &(l, ref p) in self.compact_pointers.iter() {
            write!(f, "\n  CompactPointer: {} {:?}", l, p)?;
        }
        for &(l, n) in self.deleted_files.iter() {
            write!(f, "\n  DeleteFile: {} {}", l, n)?;
        }
        for &(l, ref nf) in self.new_files.iter() {
            write!(
                f,
                "\n  AddFile: {} {} {} {:?}..{:?}",
                l, nf.number, nf.file_size, nf.smallest, nf.largest
            )?;
        }
        write!(f, "\n}}\n")?;
        Ok(())
    }
}

fn get_internal_key(input: &mut Slice) -> Result<InternalKey> {
    coding::decode_length_prefixed_slice(input).and_then(|s| Ok(InternalKey::from(&s)))
}

fn get_level(input: &mut Slice) -> Result<i32> {
    coding::decode_varint_32_slice(input).and_then(|v| {
        if (v as i32) < config::NUM_LEVELS {
            Ok(v as i32)
        } else {
            Err(Error::new(ErrorType::Corruption, "exceeded max level"))
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dbformat::ValueType;

    fn test_encode_decode(edit: &VersionEdit) {
        let mut encoded = Vec::new();
        edit.encode_to(&mut encoded);
        let mut parsed = VersionEdit::new();
        parsed
            .decode_from(&Slice::from(&encoded))
            .expect("decode_from() should be OK");
        let mut encoded2 = Vec::new();
        parsed.encode_to(&mut encoded2);
        assert_eq!(encoded.len(), encoded2.len());
        for i in 0..encoded.len() {
            assert_eq!(encoded[i], encoded2[i], "index: {}", i);
        }
    }

    #[test]
    fn encode_decode() {
        const BIG: u64 = 1u64 << 50;
        let mut edit = VersionEdit::new();

        for i in 0..4 {
            test_encode_decode(&edit);
            edit.add_file(
                3,
                BIG + 300 + i,
                BIG + 400 + i,
                InternalKey::new(Slice::from("foo"), BIG + 500 + i, ValueType::VALUE),
                InternalKey::new(Slice::from("zoo"), BIG + 600 + i, ValueType::DELETION),
            );
            edit.delete_file(4, BIG + 700 + i);
            edit.set_compact_pointer(
                i as i32,
                InternalKey::new(Slice::from("x"), BIG + 900 + i, ValueType::VALUE),
            );
        }

        edit.set_comparator_name("foo");
        edit.set_log_number(BIG + 100);
        edit.set_next_file(BIG + 200);
        edit.set_last_sequence(BIG + 1000);
        test_encode_decode(&edit);
    }
}
