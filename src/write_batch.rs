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

use std::{convert::TryFrom, rc::Rc};

use dbformat::{SequenceNumber, ValueType};
use memtable::MemTable;
use result::{Error, ErrorType, Result};
use slice::Slice;
use util::coding;

// WriteBatch header has a 8-byte sequence number followed by 4-byte count.
const HEADER_SIZE: usize = 12;

/// `WriteBatch` holds a collection of updates to apply atomically to a DB.
///
/// The updates are applied in the order in which they are added. For example, the value
/// of `"key"` will be `"v3"` after the following batch is written.
///     batch.put("key", "v1");
///     batch.delete("key");
///     batch.put("key", "v2");
///     batch.put("key", "v3");
/// Multiple threads can invoke const methods on a `WriteBatch` without external
/// synchronization, but if any of the threads may call a non-const method, all threads
/// accessing the same `WriteBatch` must use external synchronization.
pub struct WriteBatch {
    rep: Vec<u8>,
}

/// WriteBatch::rep :=
///   sequence: fixed64
///   count:    fixed32
///   data:     record[count]
/// record :=
///   ValueType::VALUE varstring varstring
///   ValueType::DELETION varstring
/// varstring :=
///   len:  varint32
///   data: u8[len]
impl WriteBatch {
    pub fn new() -> Self {
        let mut v = Vec::new();
        v.resize(HEADER_SIZE, 0);
        Self { rep: v }
    }

    /// Store the mapping "key->value" in the database.
    pub fn put(&mut self, key: &Slice, value: &Slice) {
        let count = WriteBatchInternal::count(self);
        WriteBatchInternal::set_count(self, count + 1);
        self.rep.push(ValueType::VALUE as u8);
        coding::encode_length_prefixed_slice(&mut self.rep, key);
        coding::encode_length_prefixed_slice(&mut self.rep, value);
    }

    /// If the database contains a mapping for `key`, erase it. Otherwise do nothing.
    pub fn delete(&mut self, key: &Slice) {
        let count = WriteBatchInternal::count(self);
        WriteBatchInternal::set_count(self, count + 1);
        self.rep.push(ValueType::DELETION as u8);
        coding::encode_length_prefixed_slice(&mut self.rep, key);
    }

    /// Clear all updates buffered in this batch.
    pub fn clear(&mut self) {
        self.rep.clear();
        self.rep.resize(HEADER_SIZE, 0);
    }

    /// The size of the database changes caused by this batch.
    ///
    /// This number is tied to implementation details, and may change across releases. It
    /// is intended for LevelDB usage metrics.
    pub fn approximate_size(&self) -> usize { self.rep.len() }

    pub fn iterate(&self, handler: &mut Box<Handler>) -> Result<()> {
        let mut input: Slice = Slice::from(&self.rep[..]);
        if input.size() < HEADER_SIZE {
            return LEVELDB_ERR!(Corruption, "malformed WriteBatch (too small)");
        }

        input.remove_prefix(HEADER_SIZE);
        let mut found = 0;
        while !input.empty() {
            found += 1;
            let tag: u8 = input[0];
            input.remove_prefix(1);
            match ValueType::try_from(tag).expect("invalid tag") {
                ValueType::VALUE => {
                    let key = coding::decode_length_prefixed_slice(&mut input);
                    let value = coding::decode_length_prefixed_slice(&mut input);
                    if key.is_some() && value.is_some() {
                        handler.put(&key.unwrap(), &value.unwrap());
                    } else {
                        return LEVELDB_ERR!(Corruption, "bad WriteBatch Put");
                    }
                },
                ValueType::DELETION => {
                    let key = coding::decode_length_prefixed_slice(&mut input);
                    if key.is_some() {
                        handler.delete(&key.unwrap());
                    } else {
                        return LEVELDB_ERR!(Corruption, "bad WriteBatch delete");
                    }
                },
            }
        }

        if found != WriteBatchInternal::count(self) {
            return LEVELDB_ERR!(Corruption, "WriteBatch has wrong count");
        }

        Ok(())
    }
}

/// `WriteBatchInternal` provides static methods for manipulating a `WriteBatch` that we
/// don't want in the public `WriteBatch` struct.
pub struct WriteBatchInternal {
    // No field
}

impl WriteBatchInternal {
    pub fn count(b: &WriteBatch) -> u32 { coding::decode_fixed_32(&b.rep[8..]) }

    pub fn set_count(b: &mut WriteBatch, n: u32) {
        coding::encode_fixed_32(&mut b.rep[8..], n)
    }

    pub fn sequence(b: &WriteBatch) -> SequenceNumber {
        coding::decode_fixed_64(&b.rep[..])
    }

    pub fn set_sequence(b: &mut WriteBatch, seq: SequenceNumber) {
        coding::encode_fixed_64(&mut b.rep[..], seq)
    }

    pub fn contents(b: &mut WriteBatch) -> &mut Vec<u8> { &mut b.rep }

    pub fn insert_into(b: &WriteBatch, mem: Rc<MemTable>) -> Result<()> {
        let mut inserter =
            Box::new(MemTableInserter::new(WriteBatchInternal::sequence(b), mem))
                as Box<Handler>;
        b.iterate(&mut inserter)?;
        Ok(())
    }

    pub fn append(dst: &mut WriteBatch, src: &WriteBatch) {
        let dst_count = WriteBatchInternal::count(dst);
        WriteBatchInternal::set_count(dst, WriteBatchInternal::count(src) + dst_count);
        assert!(src.rep.len() >= HEADER_SIZE);
        dst.rep.extend_from_slice(&src.rep[HEADER_SIZE..])
    }
}

pub trait Handler {
    fn put(&mut self, key: &Slice, value: &Slice);
    fn delete(&mut self, key: &Slice);
}

pub struct MemTableInserter {
    seqno: SequenceNumber,
    mem: Rc<MemTable>,
}

impl MemTableInserter {
    pub fn new(seqno: SequenceNumber, mem: Rc<MemTable>) -> Self { Self { seqno, mem } }
}

impl Handler for MemTableInserter {
    fn put(&mut self, key: &Slice, value: &Slice) {
        self.mem.add(self.seqno, ValueType::VALUE, key, value);
        self.seqno += 1;
    }

    fn delete(&mut self, key: &Slice) {
        self.mem
            .add(self.seqno, ValueType::DELETION, key, &Slice::new_empty());
        self.seqno += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use comparator::BytewiseComparator;
    use dbformat::{InternalKeyComparator, ParsedInternalKey};
    use std::convert::TryFrom;

    fn print_contents(b: &WriteBatch) -> String {
        let cmp = InternalKeyComparator::new(Rc::new(BytewiseComparator {}));
        let mem: Rc<MemTable> = Rc::new(MemTable::new(Rc::new(cmp)));

        let mut state = String::new();
        let s = WriteBatchInternal::insert_into(b, mem.clone());
        let mut count = 0;
        let mut iter = mem.iter();
        iter.seek_to_first();
        while iter.valid() {
            let ikey = ParsedInternalKey::try_from(&iter.key()).expect("should be OK");
            match ikey.value_type {
                ValueType::VALUE => {
                    state.push_str("Put(");
                    state.push_str(ikey.user_key.as_str());
                    state.push_str(", ");
                    state.push_str(iter.value().as_str());
                    state.push_str(")");
                },
                ValueType::DELETION => {
                    state.push_str("Delete(");
                    state.push_str(ikey.user_key.as_str());
                    state.push_str(")");
                },
            }
            state.push_str("@");
            state.push_str(&ikey.seqno.to_string());
            iter.next();
            count += 1;
        }

        if s.is_err() {
            state.push_str("ParseError()");
        } else if count != WriteBatchInternal::count(&b) {
            state.push_str("CountMismatch()");
        }

        state
    }

    #[test]
    fn empty() {
        let batch = WriteBatch::new();
        assert_eq!(print_contents(&batch), "");
        assert_eq!(WriteBatchInternal::count(&batch), 0);
    }

    #[test]
    fn multiple() {
        let mut batch = WriteBatch::new();
        batch.put(&Slice::from("foo"), &Slice::from("bar"));
        batch.delete(&Slice::from("box"));
        batch.put(&Slice::from("baz"), &Slice::from("boo"));
        WriteBatchInternal::set_sequence(&mut batch, 100);
        assert_eq!(WriteBatchInternal::sequence(&batch), 100);
        assert_eq!(WriteBatchInternal::count(&batch), 3);
        assert_eq!(
            print_contents(&batch),
            "Put(baz, boo)@102Delete(box)@101Put(foo, bar)@100"
        );
    }

    #[test]
    fn corruption() {
        let mut batch = WriteBatch::new();
        batch.put(&Slice::from("foo"), &Slice::from("bar"));
        batch.delete(&Slice::from("box"));
        WriteBatchInternal::set_sequence(&mut batch, 200);
        {
            let contents = WriteBatchInternal::contents(&mut batch);
            let old_len = contents.len();
            contents.truncate(old_len - 1);
        }
        assert_eq!(print_contents(&batch), "Put(foo, bar)@200ParseError()");
    }

    #[test]
    fn append() {
        let mut b1 = WriteBatch::new();
        let mut b2 = WriteBatch::new();
        WriteBatchInternal::set_sequence(&mut b1, 200);
        WriteBatchInternal::set_sequence(&mut b2, 300);
        WriteBatchInternal::append(&mut b1, &b2);
        assert_eq!(print_contents(&b1), "");
        b2.put(&Slice::from("a"), &Slice::from("va"));
        WriteBatchInternal::append(&mut b1, &b2);
        assert_eq!(print_contents(&b1), "Put(a, va)@200");
        b2.clear();
        b2.put(&Slice::from("b"), &Slice::from("vb"));
        WriteBatchInternal::append(&mut b1, &b2);
        assert_eq!(print_contents(&b1), "Put(a, va)@200Put(b, vb)@201");
        b2.delete(&Slice::from("foo"));
        WriteBatchInternal::append(&mut b1, &b2);
        assert_eq!(
            print_contents(&b1), // TODO: the order is different from cpp, visit again.
            "Put(a, va)@200Put(b, vb)@201Put(b, vb)@202Delete(foo)@203"
        );
    }

    #[test]
    fn approximate_size() {
        let mut batch = WriteBatch::new();
        let empty_size = batch.approximate_size();

        batch.put(&Slice::from("foo"), &Slice::from("bar"));
        let one_key_size = batch.approximate_size();
        assert!(empty_size < one_key_size);

        batch.put(&Slice::from("baz"), &Slice::from("boo"));
        let two_key_size = batch.approximate_size();
        assert!(one_key_size < two_key_size);

        batch.delete(&Slice::from("box"));
        let post_delete_size = batch.approximate_size();
        assert!(two_key_size < post_delete_size);
    }
}
