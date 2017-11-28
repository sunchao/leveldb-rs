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

#[derive(PartialEq, PartialOrd)]
pub enum ValueType {
  DELETION = 0x0,
  VALUE = 0x1
}

impl From<u8> for ValueType {
  fn from(v: u8) -> ValueType {
    match v {
      0x00 => ValueType::DELETION,
      0x01 => ValueType::VALUE,
      _ => panic!("Undefined value for ValueType: {}", v)
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

#[allow(dead_code)]
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
  space: [u8; 200], // for short keys - allocated on stack.
  vec: Option<Vec<u8>> // keep heap allocated memory alive.
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
      space: space,
      vec: vec
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

  fn try_from(s: &Slice) -> Result<ParsedInternalKey> {
    let n = s.size();
    if n < 8 {
      return LEVELDB_ERR!(Corruption);
    }
    let num = coding::decode_fixed_64(&s.data()[n-8..]);
    let c: u8 = (num & 0xff) as u8;
    Ok(ParsedInternalKey::new(
      Slice::new(s.raw_data(), n - 8), num >> 8, ValueType::from(c)))
  }
}
