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

use std::{mem::transmute, ptr::copy_nonoverlapping};

use crate::{
    result::{Error, ErrorType, Result},
    slice::Slice,
};

/// --------------------------------------------------------------------------------
/// Encoding & Decoding which deal with primitive Rust slices
/// --------------------------------------------------------------------------------

/// Encodes `value` in little-endian and puts it in the first 4-bytes of `dst`.
///
/// Panics if `dst.len()` is less than 4.
pub fn encode_fixed_32(dst: &mut [u8], value: u32) {
    assert!(dst.len() >= 4);
    unsafe {
        let bytes = transmute::<_, [u8; 4]>(value.to_le());
        copy_nonoverlapping(bytes.as_ptr(), dst.as_mut_ptr(), 4);
    }
}

/// Encodes `value` in little-endian and puts in the first 8-bytes of `dst`.
///
/// Panics if `dst.len()` is less than 8.
pub fn encode_fixed_64(dst: &mut [u8], value: u64) {
    assert!(dst.len() >= 8);
    unsafe {
        let bytes = transmute::<_, [u8; 8]>(value.to_le());
        copy_nonoverlapping(bytes.as_ptr(), dst.as_mut_ptr(), 8);
    }
}

/// Decodes the first 4-bytes of `src` in little-endian and returns the decoded value.
///
/// Panics if `src.len()` is less than 4.
pub fn decode_fixed_32(src: &[u8]) -> u32 {
    assert!(src.len() >= 4);
    let mut data: u32 = 0;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), &mut data as *mut u32 as *mut u8, 4);
    }
    data.to_le()
}

/// Decodes the first 8-bytes of `src` in little-endian and returns the decoded value.
///
/// Panics if `src.len()` is less than 8.
pub fn decode_fixed_64(src: &[u8]) -> u64 {
    assert!(src.len() >= 8);
    let mut data: u64 = 0;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), &mut data as *mut u64 as *mut u8, 8);
    }
    data.to_le()
}

/// Encode thes `value` in varint32 and puts it in the first `N`-bytes of `dst`.
/// Returns N.
///
/// Panics if `dst` doesn't have enough space to encode the value.
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

/// Encode thes `value` in varint32 and append it to the last `N`-bytes of `dst`.
/// Returns N.
/// Note this will increase the capacity of `dst` if there's not enough space.
pub fn encode_varint_32_vec(dst: &mut Vec<u8>, value: u32) -> usize {
    let enc_len = varint_length(value as u64);
    let old_len = dst.len();
    unsafe {
        dst.reserve(enc_len);
        dst.set_len(old_len + enc_len);
    }
    encode_varint_32(&mut dst[old_len..], value)
}

/// Encodes the `value` in varint64 and puts it in the first `N`-bytes of `dst`.
/// Returns N.
///
/// Panics if `dst` doesn't have enough space to encode the value.
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

/// Encode thes `value` in varint64 and append it to the last `N`-bytes of `dst`.
/// Returns N.
/// Note this will increase the capacity of `dst` if there's not enough space.
pub fn encode_varint_64_vec(dst: &mut Vec<u8>, value: u64) -> usize {
    let enc_len = varint_length(value);
    let old_len = dst.len();
    unsafe {
        dst.reserve(enc_len);
        dst.set_len(old_len + enc_len);
    }
    encode_varint_64(&mut dst[old_len..], value)
}

/// Decodes varint32 from `src`, and returns a tuple of which the first element is the
/// decoded value, and the second element is the number of bytes used to encode the result
/// value.
///
/// Returns error if `src` doesn't contain a valid varint32.
pub fn decode_varint_32(src: &[u8]) -> Result<(u32, usize)> {
    decode_varint_32_limit(src, src.len())
}

/// Decodes varint32 from the first `limit` bytes of `src`, and returns a tuple of which
/// the first is the decoded value, and the second element is the number of bytes used to
/// encode the result value.

/// Returns error if the first `limit` bytes of `src` doesn't contain a valid varint32.
///
/// # Panics
///
/// Panics if `src.len` is less than `limit`.
pub fn decode_varint_32_limit(src: &[u8], limit: usize) -> Result<(u32, usize)> {
    assert!(src.len() >= limit);
    let mut shift = 0;
    let mut idx = 0;
    let mut result: u32 = 0;
    while shift <= 28 && idx < limit {
        let byte = src[idx];
        idx += 1;
        result |= ((byte & 0x7F) as u32) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return Ok((result, idx));
        }
    }
    Err(Error::new(
        ErrorType::Corruption,
        "Error when decoding varint-32",
    ))
}

/// Decodes varint64 from `src`, and returns a tuple of which the first is the decoded
/// value, and the second element is the number of bytes used to encode the result value.
///
/// Returns error if `src` doesn't contain a valid varint64.
pub fn decode_varint_64(src: &[u8]) -> Result<(u64, usize)> {
    decode_varint_64_limit(src, src.len())
}

/// Decodes varint64 from the first `limit` bytes of `src`, and returns a tuple of which
/// the first is the decoded value, and the second element is the number of bytes used to
/// encode the result value.
///
/// Returns error if first `limit` bytes of `src` doesn't contain a valid varint64.
///
/// # Panics
///
/// Panics if `src.len` is less than `limit`.
pub fn decode_varint_64_limit(src: &[u8], limit: usize) -> Result<(u64, usize)> {
    assert!(src.len() >= limit);
    let mut shift = 0;
    let mut idx = 0;
    let mut result: u64 = 0;
    while shift <= 63 && idx < limit {
        let byte = src[idx];
        idx += 1;
        result |= ((byte & 0x7F) as u64) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return Ok((result, idx));
        }
    }
    Err(Error::new(
        ErrorType::Corruption,
        "Input doesn't contain a valid varint-64.",
    ))
}

/// Returns the length of the varint32 or varint64 encoding of `v`
pub fn varint_length(mut v: u64) -> usize {
    let mut len = 1;
    while v >= 128 {
        v >>= 7;
        len += 1;
    }
    len
}

/// --------------------------------------------------------------------------------
/// Encoding & Decoding which deal with LevelDB Slice type
/// --------------------------------------------------------------------------------

/// Encodes the slice `v` using length prefixed encoding, and appends the encoded value
/// to `dst` .
pub fn encode_length_prefixed_slice(dst: &mut Vec<u8>, v: &Slice) {
    let len = dst.len();
    let encoded_len = varint_length(v.size() as u64);
    unsafe {
        dst.reserve(encoded_len);
        dst.set_len(len + encoded_len);
    }
    encode_varint_32(&mut dst[len..], v.size() as u32);
    dst.extend_from_slice(v.data());
}

/// Decodes the varint32 encoded u32 value from the `input`, and advances the slice past
/// the decoded value.
///
/// Returns a u32 value if the decoding is successful, otherwise returns error.
pub fn decode_varint_32_slice(input: &mut Slice) -> Result<u32> {
    let (result, len) = decode_varint_32(input.data())?;
    input.remove_prefix(len);
    Ok(result)
}

/// Decodes the varint64 encoded u64 value from the `input`, and advances the slice past
/// the decoded value.
///
/// Returns a u64 value if the decoding is successful, otherwise returns error.
pub fn decode_varint_64_slice(input: &mut Slice) -> Result<u64> {
    let (result, len) = decode_varint_64(input.data())?;
    input.remove_prefix(len);
    Ok(result)
}

/// Decodes the value from the slice using length-prefixed encoding, and advance the slice
/// past the value.
///
/// Returns a slice which contains the decoded value, or error if the input is malformed.
pub fn decode_length_prefixed_slice(input: &mut Slice) -> Result<Slice> {
    let len = decode_varint_32_slice(input)? as usize;
    if input.size() >= len {
        let result = Slice::new(input.raw_data(), len);
        input.remove_prefix(len);
        return Ok(result);
    }
    Err(Error::new(
        ErrorType::Corruption,
        "Input slice doesn't contain a length-prefixed encoded value.",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::random::Random;

    #[test]
    fn fixed_32() {
        const N: usize = 100000;
        let mut data: Vec<u8> = vec![0; N * 4];

        for i in 0..N {
            encode_fixed_32(&mut data[i * 4..], i as u32);
        }

        for i in 0..N {
            let actual: u32 = decode_fixed_32(&data[i * 4..]);
            assert_eq!(actual, i as u32);
        }
    }

    #[test]
    #[should_panic]
    fn fixed_32_panic() {
        let mut data = vec![0; 3];
        encode_fixed_32(&mut data, 100);
    }

    #[test]
    fn fixed_64() {
        let mut data: Vec<u8> = vec![0; 64 * 3 * 8];

        for power in 0..64 {
            let v = 1 << power as u64;
            encode_fixed_64(&mut data[(power * 3 + 0) * 8..], v - 1);
            encode_fixed_64(&mut data[(power * 3 + 1) * 8..], v + 0);
            encode_fixed_64(&mut data[(power * 3 + 2) * 8..], v + 1);
        }

        for power in 0..64 {
            let v = 1 << power as u64;
            let actual = decode_fixed_64(&data[(power * 3 + 0) * 8..]);
            assert_eq!(actual, v - 1);

            let actual = decode_fixed_64(&data[(power * 3 + 1) * 8..]);
            assert_eq!(actual, v + 0);

            let actual = decode_fixed_64(&data[(power * 3 + 2) * 8..]);
            assert_eq!(actual, v + 1);
        }
    }

    #[test]
    #[should_panic]
    fn fixed_64_panic() {
        let mut data = vec![0; 6];
        encode_fixed_64(&mut data, 100);
    }

    #[test]
    fn varint_32() {
        let mut idx = 0;
        let mut data: Vec<u8> = vec![0; 32 * 32 * 5];

        for i in 0..32 * 32 {
            let v: u32 = (i / 32) << (i % 32);
            idx += encode_varint_32(&mut data[idx..], v);
        }

        idx = 0;
        for i in 0..32 * 32 {
            let expected = (i / 32) << (i % 32);
            let (actual, next_idx) = decode_varint_32(&data[idx..]).expect("OK");
            assert_eq!(actual, expected);
            idx += next_idx;
        }
    }

    #[test]
    #[should_panic]
    fn varint_32_no_space() {
        let mut data = vec![0; 1];
        let _ = encode_varint_32(&mut data, 128);
    }

    #[test]
    fn varint_32_limit() {
        let mut data = vec![0; 5];
        for i in 0..32 * 32 {
            let v: u32 = (i / 32) << (i % 32);
            let limit = encode_varint_32(&mut data, v);
            assert!(limit <= 5);
            let (actual, len) = decode_varint_32_limit(&mut data, limit).expect("OK");
            assert_eq!(actual, v);
            assert_eq!(len, limit);
        }
    }

    #[test]
    fn varint_64() {
        let mut values = Vec::new();
        values.push(0);
        values.push(100);
        values.push(!0u64);
        values.push(!0u64 - 1);
        for k in 0..64 {
            let power = 1u64 << k;
            values.push(power);
            values.push(power - 1);
            values.push(power + 1);
        }

        let mut data: Vec<u8> = vec![0; 196 * 10];
        let mut idx = 0;
        for v in &values {
            idx += encode_varint_64(&mut data[idx..], *v);
        }

        idx = 0;
        for v in &values {
            let (actual, offset) = decode_varint_64(&data[idx..]).expect("OK");
            assert_eq!(actual, *v);
            idx += offset;
        }
    }

    #[test]
    fn varint_64_limit() {
        let mut data = vec![0; 10];
        for i in 0..64 * 64 {
            let v: u64 = (i / 64) << (i % 64);
            let limit = encode_varint_64(&mut data, v);
            assert!(limit <= 10);
            let (actual, len) = decode_varint_64_limit(&mut data, limit).expect("OK");
            assert_eq!(actual, v);
            assert_eq!(len, limit);
        }
    }

    #[test]
    #[should_panic]
    fn varint_64_no_space() {
        let mut data = vec![0; 4];
        let _ = encode_varint_64(&mut data, 2147483648u64);
    }

    #[test]
    fn varint_32_vec() {
        let rnd = Random::new(301);
        let mut data = Vec::new();
        let mut total_size = 0;
        for _ in 0..100 {
            let n = rnd.next();
            let size = encode_varint_32_vec(&mut data, n);
            let (a, b) = decode_varint_32(&data[total_size..total_size + size])
                .expect("decode_varint_32() should be OK");
            assert_eq!(n, a);
            assert_eq!(size, b);
            total_size += size;
        }
        assert_eq!(total_size, data.len());
    }

    #[test]
    fn varint_64_vec() {
        let mut data = Vec::new();
        let size = encode_varint_64_vec(&mut data, !0u64 - 1);
        let (a, b) =
            decode_varint_64(&data[0..size]).expect("decode_varint_64() should be OK");
        assert_eq!(data.len(), size);
        assert_eq!(!0u64 - 1, a);
        assert_eq!(size, b);
    }

    #[test]
    fn varint_length() {
        let rand = Random::new(0xbaaaaaad);
        let mut data = vec![0; 5];
        for _ in 0..1000 {
            let v = rand.next();
            let len = encode_varint_32(&mut data, v);
            assert_eq!(super::varint_length(v as u64), len);
        }
    }

    #[test]
    fn decode_varint_32_slice() {
        let mut v = vec![0; 4];
        let len = encode_varint_32(&mut v, 1000);
        let mut s = Slice::from(&v[..]);
        let v = super::decode_varint_32_slice(&mut s).expect("shouldn't be None");
        assert_eq!(v, 1000);
        assert_eq!(s.size(), 4 - len);
    }

    #[test]
    fn decode_varint_64_slice() {
        let mut v = vec![0; 10];
        let c = 1 << 60 as u64;
        let len = encode_varint_64(&mut v, c);
        let mut s = Slice::from(&v[..]);
        let v = super::decode_varint_64_slice(&mut s).expect("shouldn't be None");
        assert_eq!(v, c);
        assert_eq!(s.size(), 10 - len);
    }

    #[test]
    fn prefix_length_slice() {
        let mut v: Vec<u8> = Vec::new();
        encode_length_prefixed_slice(&mut v, &Slice::from(""));
        encode_length_prefixed_slice(&mut v, &Slice::from("hello"));
        encode_length_prefixed_slice(&mut v, &Slice::from("world"));

        let mut input = Slice::from(&v[..]);
        let mut v;
        v = decode_length_prefixed_slice(&mut input).expect("shouldn't be None");
        assert_eq!(v.as_str(), "");
        v = decode_length_prefixed_slice(&mut input).expect("shouldn't be None");
        assert_eq!(v.as_str(), "hello");
        v = decode_length_prefixed_slice(&mut input).expect("shouldn't be None");
        assert_eq!(v.as_str(), "world");

        assert_eq!(input.size(), 0);
    }
}
