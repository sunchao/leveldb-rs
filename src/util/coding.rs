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

use std::mem::transmute;
use std::ptr::copy_nonoverlapping;

/// Encode `value` in little-endian and put in the first 4-bytes of `dst`.
pub fn encode_fixed_32(dst: &mut [u8], value: u32) {
  assert!(dst.len() >= 4);
  unsafe {
    let bytes = transmute::<_, [u8; 4]>(value.to_le());
    copy_nonoverlapping(bytes.as_ptr(), dst.as_mut_ptr(), 4);
  }
}

/// Encode `value` in little-endian and put in the first 8-bytes of `dst`.
pub fn encode_fixed_64(dst: &mut [u8], value: u64) {
  assert!(dst.len() >= 8);
  unsafe {
    let bytes = transmute::<_, [u8; 8]>(value.to_le());
    copy_nonoverlapping(bytes.as_ptr(), dst.as_mut_ptr(), 8);
  }
}

/// Decode the first 4-bytes of `src` in little-endian and return the result.
pub fn decode_fixed_32(src: &[u8]) -> u32 {
  assert!(src.len() >= 4);
  let mut data: u32 = 0;
  unsafe {
    copy_nonoverlapping(
      src.as_ptr(),
      &mut data as *mut u32 as *mut u8,
      4
    );
  }
  data.to_le()
}

/// Decode the first 8-bytes of `src` in little-endian and return the result.
pub fn decode_fixed_64(src: &[u8]) -> u64 {
  assert!(src.len() >= 8);
  let mut data: u64 = 0;
  unsafe {
    copy_nonoverlapping(
      src.as_ptr(),
      &mut data as *mut u64 as *mut u8,
      8
    );
  }
  data.to_le()
}

/// Encode the `value` in varint32 and put it in the first N-bytes of `dst`.
/// Return N+1.
pub fn encode_varint_32(dst: &mut [u8], value: u32) -> usize {
  const B: u32 = 0x80;
  let mut idx = 0;
  if value < (1 << 7) {
    dst[idx] = value as u8;
    idx += 1;
  } else if value < (1 << 14) {
    dst[idx] = (value | B) as u8;
    dst[idx + 1] = (value >> 7) as u8;
    idx += 2;
  } else if value < (1 << 21) {
    dst[idx] = (value | B) as u8;
    dst[idx + 1] = ((value >> 7) | B) as u8;
    dst[idx + 2] = (value >> 14) as u8;
    idx += 3;
  } else if value < (1 << 28) {
    dst[idx] = (value | B) as u8;
    dst[idx + 1] = ((value >> 7) | B) as u8;
    dst[idx + 2] = ((value >> 14) | B) as u8;
    dst[idx + 3] = (value >> 21) as u8;
    idx += 4;
  } else {
    dst[idx] = (value | B) as u8;
    dst[idx + 1] = ((value >> 7) | B) as u8;
    dst[idx + 2] = ((value >> 14) | B) as u8;
    dst[idx + 3] = ((value >> 21) | B) as u8;
    dst[idx + 4] = (value >> 28) as u8;
    idx += 5;
  }
  idx
}

/// Encode the `value` in varint64 and put it in the first N-bytes of `dst`.
/// Return N+1.
pub fn encode_varint_64(dst: &mut [u8], mut value: u64) -> usize {
  let mut idx = 0;
  while value & 0xFFFFFFFFFFFFFF80 != 0 {
    dst[idx] = ((value & 0x7F) | 0x80) as u8;
    idx += 1;
    value >>= 7;
  }
  dst[idx] = (value & 0x7F) as u8;
  idx + 1
}

/// Decode the first N-bytes of `src` in varint32.
/// Return a tuple where the first element is the decoded value,
/// and the second element is N+1.
pub fn decode_varint_32(src: &[u8]) -> (u32, usize) {
  assert!(src.len() >= 4);
  let mut shift = 0;
  let mut idx = 0;
  let mut result: u32 = 0;
  while shift <= 28 {
    let byte = src[idx];
    idx += 1;
    result |= ((byte & 0x7F) as u32) << shift;
    shift += 7;
    if byte & 0x80 == 0 {
      break;
    }
  }
  (result, idx)
}

/// Decode the first N-bytes of `src` in varint64.
/// Return a tuple where the first element is the decoded value,
/// and the second element is N+1.
pub fn decode_varint_64(src: &[u8]) -> (u64, usize) {
  assert!(src.len() >= 8);
  let mut shift = 0;
  let mut idx = 0;
  let mut result: u64 = 0;
  while shift <= 63 {
    let byte = src[idx];
    idx += 1;
    result |= ((byte & 0x7F) as u64) << shift;
    shift += 7;
    if byte & 0x80 == 0 {
      break;
    }
  }
  (result, idx)
}


#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_fixed_32() {
    const N: usize = 100000;
    let mut data: Vec<u8> = vec![0; N * 4];

    for i in 0..N {
      encode_fixed_32(&mut data[i*4..], i as u32);
    }

    for i in 0..N {
      let actual: u32 = decode_fixed_32(&data[i*4..]);
      assert_eq!(actual, i as u32);
    }
  }

  #[test]
  fn test_fixed_64() {
    let mut data: Vec<u8> = vec![0; 64 * 3 * 8];

    for power in 0..64 {
      let v = 1 << power as u64;
      encode_fixed_64(&mut data[(power*3+0)*8..], v - 1);
      encode_fixed_64(&mut data[(power*3+1)*8..], v + 0);
      encode_fixed_64(&mut data[(power*3+2)*8..], v + 1);
    }

    for power in 0..64 {
      let v = 1 << power as u64;
      let actual = decode_fixed_64(&data[(power*3+0)*8..]);
      assert_eq!(actual, v - 1);

      let actual = decode_fixed_64(&data[(power*3+1)*8..]);
      assert_eq!(actual, v + 0);

      let actual = decode_fixed_64(&data[(power*3+2)*8..]);
      assert_eq!(actual, v + 1);
    }
  }

  #[test]
  fn test_varint_32() {
    let mut idx = 0;
    let mut data: Vec<u8> = vec![0; 32 * 32 * 5];

    for i in 0..32*32 {
      let v: u32 = (i / 32) << (i % 32);
      idx += encode_varint_32(&mut data[idx..], v);
    }

    idx = 0;
    for i in 0..32*32 {
      let expected = (i / 32) << (i % 32);
      let (actual, next_idx) = decode_varint_32(&data[idx..]);
      assert_eq!(actual, expected);
      idx += next_idx;
    }
  }

  #[test]
  fn test_varint_64() {
    let mut values = Vec::new();
    values.push(0);
    values.push(100);
    values.push(!0u64);
    values.push(!0u64 - 1);
    for k in 0..64 {
      let power = 1u64 << k;
      values.push(power);
      values.push(power-1);
      values.push(power+1);
    }

    let mut data: Vec<u8> = vec![0; 196 * 10];
    let mut idx = 0;
    for v in &values {
      idx += encode_varint_64(&mut data[idx..], *v);
    }

    idx = 0;
    for v in &values {
      let (actual, offset) = decode_varint_64(&data[idx..]);
      assert_eq!(actual, *v);
      idx += offset;
    }
  }
}
