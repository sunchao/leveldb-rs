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

use std::{mem, slice};
use std::rc::Rc;
use std::cell::RefCell;
use std::cmp::Ordering;

use super::skiplist::{SkipList, SkipListIterator};
use dbformat::{SequenceNumber, ValueType, LookupKey, InternalKeyComparator};
use slice::Slice;
use util::arena::{Arena, ArenaRef};
use util::{coding, bit};
use result::{Result, Error, ErrorType};
use iterator::Iterator;

type Table = SkipList<Slice>;

pub struct MemTable {
  refs: u32,
  arena: ArenaRef, // shared between this and `table`
  table: Table,
  comparator: Rc<InternalKeyComparator>
}

impl MemTable {
  pub fn new(cmp: Rc<InternalKeyComparator>) -> Self {
    let arena = Rc::new(RefCell::new(Arena::new()));
    Self {
      refs: 0,
      arena: arena.clone(),
      table: SkipList::new(cmp.clone(), arena, Slice::new_empty()),
      comparator: cmp
    }
  }

  /// Increment the reference count of this memtable.
  pub fn inc_ref(&mut self) {
    self.refs += 1;
  }

  /// Decrement the reference count of this memtable.
  /// Delete if no more references exist.
  pub fn dec_ref(&mut self) {
    self.refs -= 1;
    if self.refs <= 0 {
      mem::drop(self);
    }
  }

  /// Returns an interator on this memtable.
  pub fn iter<'a>(&'a self) -> Box<Iterator + 'a> {
    let table_iter = MemTableIterator {
      internal_iter: self.table.iter()
    };
    Box::new(table_iter)
  }

  /// Add an entry into this memtable, that maps the `key` to the `val`
  /// at the specific sequence number `seq`. Typically `val` will be empty
  /// if `val_ty` is `ValueType::DELETION`.
  pub fn add(
    &self,
    seq: SequenceNumber,
    val_ty: ValueType,
    key: &Slice,
    val: &Slice
  ) {
    // format of an entry is concatenation of:
    //  key_size: varint32 of internal_key.size()
    //  key bytes: char[internal_key.size()]
    //  value_size: varint32 of value.size()
    //  value bytes: char[value.size()]
    let key_size = key.size();
    let val_size = val.size();
    let internal_key_size = key_size + 8;
    let encoded_len = coding::varint_length(internal_key_size as u64)
      + internal_key_size + coding::varint_length(val_size as u64) + val_size;
    let mut buf = unsafe {
      let mut arena = self.arena.borrow_mut();
      slice::from_raw_parts_mut(arena.alloc(encoded_len), encoded_len)
    };
    let mut offset = coding::encode_varint_32(&mut buf, internal_key_size as u32);
    bit::memcpy(&mut buf[offset..], key.data());
    offset += key_size;
    coding::encode_fixed_64(&mut buf[offset..], (seq << 8) | val_ty as u64);
    offset += 8;
    let val_encoded_len = coding::encode_varint_32(&mut buf[offset..], val_size as u32);
    offset += val_encoded_len;
    bit::memcpy(&mut buf[offset..], val.data());
    assert!(offset + val_size == encoded_len);
    self.table.insert(Slice::new(buf.as_ptr(), encoded_len));
  }

  /// If table contains a value for `key`, return `Some(Ok(value))`;
  /// If table contains a deletion for `key`, returns `Some(Err(NOT_FOUND))`;
  /// Otherwise, return `None`.
  pub fn get(&self, key: &LookupKey) -> Option<Result<String>> {
    let mem_key = key.memtable_key();
    let mut iter = self.table.iter();
    iter.seek(&mem_key);
    if iter.valid() {
      // entry format is:
      //  key_length varint32
      //  user_key   char[key_length - 8]
      //  tag        u64
      //  val_length varint32
      //  value      char[val_length]
      let mut entry: &[u8] = iter.key().data();
      let (key_length_32, length) =
        coding::decode_varint_32_limit(entry, 5)
        .expect("Invalid varint32 for key length");
      let key_length = key_length_32 as usize;
      entry = &entry[length..];
      let user_key = &entry[..key_length-8];
      if self.comparator.user_comparator().compare(
        &Slice::from(user_key), &key.user_key()) == Ordering::Equal {
        // Correct user key
        let tag = coding::decode_fixed_64(&entry[(key_length-8)..key_length]);
        match ValueType::from((tag & 0xff) as u8) {
          ValueType::VALUE => {
            let v = get_length_prefixed_slice(&entry[key_length..]);
            return Some(Ok(get_string_from_slice(&v)))
          },
          ValueType::DELETION => {
            return Some(LEVELDB_ERR!(NotFound))
          }
        }
      }
    }
    None
  }
}


pub struct MemTableIterator<'a> {
  internal_iter: SkipListIterator<'a, Slice>
}

impl<'a> Iterator for MemTableIterator<'a> {
  fn valid(&self) -> bool { self.internal_iter.valid() }
  fn seek_to_first(&mut self) { self.internal_iter.seek_to_first(); }
  fn seek_to_last(&mut self) { self.internal_iter.seek_to_last(); }
  fn seek(&mut self, target: &Slice) { self.internal_iter.seek(target); }
  fn next(&mut self) { self.internal_iter.next(); }
  fn prev(&mut self) { self.internal_iter.prev(); }
  fn key(&self) -> Slice {
    let mut s = self.internal_iter.key().clone();
    if let Some(key_slice) = coding::decode_length_prefixed_slice(&mut s) {
      return key_slice
    }
    Slice::new_empty()
  }
  fn value(&self) -> Slice {
    let mut s = self.internal_iter.key().clone();
    if let Some(_) = coding::decode_length_prefixed_slice(&mut s) {
      if let Some(val_slice) = coding::decode_length_prefixed_slice(&mut s) {
        return val_slice
      }
    }
    Slice::new_empty()
  }
}

/// A few utility functions

fn get_length_prefixed_slice(val: &[u8]) -> Slice {
  match coding::decode_varint_32_limit(val, 5) {
    None => Slice::new_empty(),
    Some((val_len, len)) => Slice::from(&val[len..(len+val_len as usize)])
  }
}

fn get_string_from_slice(slice: &Slice) -> String {
  unsafe {
    let mut v: Vec<u8> = Vec::with_capacity(slice.size());
    bit::memcpy(&mut v, slice.data());
    String::from_raw_parts(v.as_mut_ptr(), slice.size(), slice.size())
  }
}
