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

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::rc::Rc;

use slice::Slice;
use util::{coding, bit};
use comparator::Comparator;
use result::{Result, Error, ErrorType};

pub type SequenceNumber = u64;

/// The last eight bits are reserved for value type.
pub const MAX_SEQUENCE_NUMBER: u64 = (0x1u64 << 56) - 1;

#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
pub enum ValueType {
  DELETION = 0x0,
  VALUE = 0x1
}

impl TryFrom<u8> for ValueType {
  type Error = super::result::Error;
  fn try_from(v: u8) -> Result<ValueType> {
    match v {
      0x00 => Ok(ValueType::DELETION),
      0x01 => Ok(ValueType::VALUE),
      _ => LEVELDB_ERR!(InvalidArgument, "undefined value for ValueType")
    }
  }
}

// `VALUE_TYPE_FOR_SEEK` defines the `ValueType` that should be passed when
// constructing a `ParsedInternalKey` object for seeking to a particular
// sequence number (since we sort sequence numbers in decreasing order
// and the value type is embedded as the low 8 bits in the sequence
// number in internal keys, we need to use the highest-numbered
// `ValueType`, not the lowest).
pub const VALUE_TYPE_FOR_SEEK: ValueType = ValueType::VALUE;

pub struct LookupKey {
  // Layout:
  //    key_length  varint32                     <- data
  //    user_key    char[key_length - 8]         <- kstart
  //    tag         u64
  //                                             <- size
  data: *const u8,
  kstart: usize,
  size: usize,

  // These two fields are never used: they are here to keep the
  // `data` pointer alive.
  _space: [u8; 200], // for short keys - allocated on stack.
  _vec: Option<Vec<u8>> // keep heap allocated memory alive.
}

impl LookupKey {
  pub fn new(user_key: &Slice, s: SequenceNumber) -> Self {
    let size = user_key.size();
    let needed = size + 13; // a conservative estimate
    let mut space: [u8; 200] = [0; 200];
    let (ptr, vec) = if needed <= 200 {
      (space.as_mut_ptr(), None)
    } else {
      let mut v = Vec::with_capacity(needed);
      (v.as_mut_ptr(), Some(v))
    };
    let mut dst = unsafe {
      ::std::slice::from_raw_parts_mut(ptr, needed)
    };
    let mut offset = coding::encode_varint_32(&mut dst, size as u32 + 8);
    let kstart = offset;
    bit::memcpy(&mut dst[offset..], user_key.data());
    offset += size;
    coding::encode_fixed_64(
      &mut dst[offset..], pack_sequence_and_type(s, VALUE_TYPE_FOR_SEEK));
    offset += 8;
    Self {
      data: ptr,
      kstart: kstart,
      size: offset,
      _space: space,
      _vec: vec
    }
  }

  /// Returns the whole key
  pub fn memtable_key(&self) -> Slice {
    Slice::new(self.data, self.size)
  }

  /// Returns the `user_key` and `tag` part
  pub fn internal_key(&self) -> Slice {
    unsafe {
      Slice::new(self.data.offset(self.kstart as isize),
                 self.size - self.kstart)
    }
  }

  /// Returns the `user_key` part
  pub fn user_key(&self) -> Slice {
    unsafe {
      Slice::new(self.data.offset(self.kstart as isize),
                 self.size - self.kstart - 8)
    }
  }
}

fn pack_sequence_and_type(seq: u64, t: ValueType) -> u64 {
  assert!(seq <= MAX_SEQUENCE_NUMBER);
  assert!(t <= VALUE_TYPE_FOR_SEEK);
  (seq << 8) | t as u64
}


/// A comparator for internal keys that uses a specific comparator for user
/// key portion and breaks ties by decreasing sequence number.
#[derive(Clone)]
pub struct InternalKeyComparator {
  user_comparator: Rc<Comparator<Slice>>
}

impl InternalKeyComparator {
  pub fn new(uc: Rc<Comparator<Slice>>) -> Self {
    Self {
      user_comparator: uc
    }
  }

  pub fn compare_key(&self, a: &InternalKey, b: &InternalKey) -> Ordering {
    self.compare(&a.encode(), &b.encode())
  }

  pub fn user_comparator(&self) -> &Rc<Comparator<Slice>> {
    &self.user_comparator
  }
}

impl Comparator<Slice> for InternalKeyComparator {
  fn compare(&self, a: &Slice, b: &Slice) -> Ordering {
    let r = self.user_comparator.compare(
      &extract_user_key(a), &extract_user_key(b));
    match r {
      Ordering::Equal => {
        let anum = coding::decode_fixed_64(&a.data()[a.size()-8..]);
        let bnum = coding::decode_fixed_64(&b.data()[b.size()-8..]);
        if anum > bnum {
          Ordering::Less
        } else {
          Ordering::Greater
        }
      },
      rp => rp
    }
  }

  fn name(&self) -> &str {
    "leveldb.InternalKeyComparator"
  }
}

pub struct InternalKey {
  rep: Vec<u8>
}

impl InternalKey {
  pub fn new(user_key: Slice, s: SequenceNumber, t: ValueType) -> Self {
    let mut v = Vec::new();
    let k = ParsedInternalKey::new(user_key, s, t);
    append_internal_key(&mut v, &k);
    Self {
      rep: v
    }
  }

  pub fn encode(&self) -> Slice {
    Slice::from(&self.rep[..])
  }

  pub fn decode_from(&mut self, s: &Slice) {
    self.rep.clear();
    self.rep.extend_from_slice(&s.data());
  }

  pub fn user_key(&self) -> Slice {
    let s = Slice::from(&self.rep[..]);
    extract_user_key(&s)
  }

  pub fn set_from(&mut self, p: &ParsedInternalKey) {
    self.rep.clear();
    append_internal_key(&mut self.rep, p);
  }

  pub fn clear(&mut self) {
    self.rep.clear();
  }
}

fn append_internal_key(result: &mut Vec<u8>, key: &ParsedInternalKey) {
  result.extend_from_slice(&key.user_key.data());
  let key_len = result.len();
  unsafe {
    result.reserve(8);
    result.set_len(key_len + 8);
  }
  coding::encode_fixed_64(
    &mut result[key_len..], pack_sequence_and_type(key.seqno, key.value_type));
}

fn extract_user_key(internal_key: &Slice) -> Slice {
  assert!(internal_key.size() >= 8);
  Slice::new(internal_key.raw_data(), internal_key.size() - 8)
}


pub struct ParsedInternalKey {
  pub user_key: Slice,
  pub seqno: SequenceNumber,
  pub value_type: ValueType
}

impl ParsedInternalKey {
  pub fn new(user_key: Slice, seqno: SequenceNumber, value_type: ValueType) -> Self {
    Self {
      user_key: user_key,
      seqno: seqno,
      value_type: value_type
    }
  }

  pub fn encoding_length(&self) -> usize {
    self.user_key.size() + 8
  }
}

impl<'a> TryFrom<&'a Slice> for ParsedInternalKey {
  type Error = super::result::Error;

  /// Attempt to parse an internal key from `internal_key`. On success, return `Some`
  /// with the parsed data. Otherwise, return `None`.
  fn try_from(s: &Slice) -> Result<ParsedInternalKey> {
    let n = s.size();
    if n < 8 {
      return LEVELDB_ERR!(InvalidArgument, "Invalid Slice size");
    }
    let num = coding::decode_fixed_64(&s.data()[n-8..]);
    let vt = ValueType::try_from((num & 0xff) as u8)?;
    Ok(ParsedInternalKey::new(Slice::new(s.raw_data(), n - 8), num >> 8, vt))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn ikey(user_key: &'static str, seq: u64, vt: ValueType) -> Vec<u8> {
    let mut encoded = Vec::new();
    let parsed_key = ParsedInternalKey::new(Slice::from(user_key), seq, vt);
    append_internal_key(&mut encoded, &parsed_key);
    encoded
  }

  fn test_key(key: &'static str, seq: u64, vt: ValueType) {
    let encoded = ikey(key, seq, vt);
    let input = Slice::from(&encoded[..]);
    let decoded = ParsedInternalKey::try_from(&input).expect("try_from() should be OK");
    assert_eq!(key, decoded.user_key.as_str());
    assert_eq!(seq, decoded.seqno);
    assert_eq!(vt, decoded.value_type);
    assert!(ParsedInternalKey::try_from(&Slice::from("bar")).is_err());
  }

  #[test]
  fn lookup_key() {
    let short_key = Slice::from("hello");
    let mut key = LookupKey::new(&short_key, 0);
    let mut v = [0; 4];
    let len = coding::encode_varint_32(&mut v, short_key.size() as u32);
    assert_eq!(len, key.kstart);
    assert_eq!(
      short_key,
      Slice::new(unsafe { key.data.offset(len as isize) }, short_key.size()));
    assert_eq!(len + short_key.size() + 8, key.size);
    assert_eq!(None, key._vec);

    let v = (0..256).map(|_| 'a' as u8).collect::<Vec<u8>>();
    let long_key = Slice::from(&v[..]);
    key = LookupKey::new(&long_key, 1);
    assert!(key._vec.is_some());
  }

  #[test]
  fn internal_key_encode_decode() {
    let keys = ["", "k", "hello", "longggggggggggggggggggggg"];
    let seq = [
      1, 2, 3,
      (1u64 << 8) - 1, 1u64 << 8, (1u64 << 8) + 1,
      (1u64 << 16) - 1, 1u64 << 16, (1u64 << 16) + 1,
      (1u64 << 32) - 1, 1u64 << 32, (1u64 << 32) + 1
    ];
    for k in 0..keys.len() {
      for s in 0..seq.len() {
        test_key(keys[k], seq[s], ValueType::VALUE);
        test_key("hello", 1, ValueType::DELETION);
      }
    }
  }
}
