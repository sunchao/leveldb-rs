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

use byteorder::{ByteOrder, LittleEndian as LE};
#[cfg(target_feature = "sse4.2")]
use x86intrin::sse42;

const CRC32_XOR: u32 = 0xffffffff;
const CASTAGNOLI_POLY: u32 = 0x82f63b78;
const MASK_DELTA: u32 = 0xa282ead8;

lazy_static! {
    static ref TABLE16: [[u32; 256]; 16] = {
        let mut tab = [[0; 256]; 16];
        tab[0] = make_table(CASTAGNOLI_POLY);
        for i in 0..256 {
            let mut crc = tab[0][i];
            for j in 1..16 {
                crc = (crc >> 8) ^ tab[0][crc as u8 as usize];
                tab[j][i] = crc;
            }
        }
        tab
    };
}

pub fn value(data: &[u8]) -> u32 { extend(0, data) }

pub fn extend(crc: u32, data: &[u8]) -> u32 {
    #[cfg(target_feature = "sse4.2")]
    {
        extend_hw(crc, data)
    }
    #[cfg(not(target_feature = "sse4.2"))]
    {
        extend_sw(crc, data)
    }
}

/// Return a masked representation of `crc`.
pub fn mask(crc: u32) -> u32 {
    // Rotate right by 15 bits and add a constant
    ((crc >> 15) | (crc << 17)).wrapping_add(MASK_DELTA)
}

/// Return the crc whose masked representation is `masked_crc`.
pub fn unmask(masked_crc: u32) -> u32 {
    let rot = masked_crc.wrapping_sub(MASK_DELTA);
    (rot >> 17) | (rot << 15)
}

pub fn extend_sw(crc: u32, mut data: &[u8]) -> u32 {
    let tab8 = &*TABLE16;
    let mut l: u32 = crc ^ CRC32_XOR;
    while data.len() >= 8 {
        l ^= LE::read_u32(&data[0..4]);
        l = tab8[0][data[7] as usize]
            ^ tab8[1][data[6] as usize]
            ^ tab8[2][data[5] as usize]
            ^ tab8[3][data[4] as usize]
            ^ tab8[4][(l >> 24) as u8 as usize]
            ^ tab8[5][(l >> 16) as u8 as usize]
            ^ tab8[6][(l >> 8) as u8 as usize]
            ^ tab8[7][(l) as u8 as usize];
        data = &data[8..];
    }
    for &b in data {
        l = tab8[0][((l as u8) ^ b) as usize] ^ (l >> 8);
    }
    l ^ CRC32_XOR
}

#[cfg(target_feature = "sse4.2")]
pub fn extend_hw(crc: u32, data: &[u8]) -> u32 {
    let mut l: u32 = crc ^ CRC32_XOR;
    let size = data.len();
    let mut offset = 0;
    if size > 16 {
        let start_offset = align_offset(8, data);
        while offset != start_offset {
            l = sse42::mm_crc32_u8(l, data[offset]);
            offset += 1;
        }
        while size - offset >= 8 {
            l = sse42::mm_crc32_u64(l as u64, LE::read_u64(&data[offset..])) as u32;
            offset += 8;
        }
        while size - offset >= 4 {
            l = sse42::mm_crc32_u32(l, LE::read_u32(&data[offset..]));
            offset += 4;
        }
    }

    while offset != size {
        l = sse42::mm_crc32_u8(l, data[offset]);
        offset += 1;
    }
    l ^ CRC32_XOR
}

#[cfg(target_feature = "sse4.2")]
fn align_offset(align: usize, data: &[u8]) -> usize {
    assert!(align & (align - 1) == 0);
    let ptr = data.as_ptr() as usize;
    ((ptr + (align - 1)) & !(align - 1)) - ptr
}

fn make_table(poly: u32) -> [u32; 256] {
    let mut tab = [0; 256];
    for i in 0u32..256u32 {
        let mut crc = i;
        for _ in 0..8 {
            if crc & 1 == 1 {
                crc = (crc >> 1) ^ poly;
            } else {
                crc >>= 1;
            }
        }
        tab[i as usize] = crc;
    }
    tab
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn standard_results() {
        let buf: Vec<u8> = vec![0; 32];
        assert_eq!(value(&buf), 0x8a9136aa);

        let mut buf: Vec<u8> = vec![0xff; 32];
        assert_eq!(value(&buf), 0x62a8ab43);

        for i in 0..32 {
            buf[i] = i as u8;
        }
        assert_eq!(value(&buf), 0x46dd794e);

        for i in 0..32 {
            buf[i] = (31 - i) as u8;
        }
        assert_eq!(value(&buf), 0x113fdb5c);

        let data = [
            0x01, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
            0x00, 0x14, 0x00, 0x00, 0x00, 0x18, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        assert_eq!(value(&data), 0xd9963a56);
    }

    #[test]
    pub fn values() {
        assert_ne!(value("a".as_bytes()), value("foo".as_bytes()));
    }

    #[test]
    pub fn extend() {
        assert_eq!(
            value("hello world".as_bytes()),
            super::extend(value("hello ".as_bytes()), "world".as_bytes())
        );
    }

    #[test]
    pub fn mask() {
        let crc = value("foo".as_bytes());
        assert_ne!(super::mask(crc), crc);
        assert_ne!(super::mask(super::mask(crc)), crc);
        assert_eq!(unmask(super::mask(crc)), crc);
        assert_eq!(unmask(unmask(super::mask(super::mask(crc)))), crc);
    }
}
