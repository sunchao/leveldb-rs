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

use crate::{
    result::{Error, ErrorType, Result},
    slice::Slice,
    util::coding,
};

const TABLE_MAGIC_NUMBER: u64 = 0xdb4775248b80fb57u64;

/// BlockHandle is a pointer to the extent of a file that stores a data block or a meta
/// data block.
#[derive(PartialEq, Debug)]
pub struct BlockHandle {
    offset: u64,
    size: u64,
}

impl BlockHandle {
    pub const MAX_ENCODED_LENGTH: usize = 10 + 10;

    pub fn encode_to(&self, dst: &mut Vec<u8>) {
        coding::encode_varint_64_vec(dst, self.offset);
        coding::encode_varint_64_vec(dst, self.size);
    }

    pub fn decode_from(src: &mut Slice) -> Result<BlockHandle> {
        let offset = coding::decode_varint_64_slice(src)
            .or(Err(Error::new(ErrorType::Corruption, "bad handle")))?;
        let size = coding::decode_varint_64_slice(src)
            .or(Err(Error::new(ErrorType::Corruption, "bad handle")))?;
        let result = BlockHandle { offset, size };
        Ok(result)
    }
}

/// Footer encapsulates the fixed information stored at the tail end of every table file.
/// Format of the footer:
///
/// metaindex_handle: u8[p]      // BlockHandle for metaindex.
/// index_handle:     u8[q]      // BlockHandle for index.
/// padding:          u8[40-p-q] // Zeroed bytes to make fixed length.
/// magic:            fixed64    // == 0xdb4775248b80fb57 (little-endian)
///
/// The total number of bytes for footer is 40 + 8 = 48 bytes.
#[derive(PartialEq, Debug)]
pub struct Footer {
    metaindex_handle: BlockHandle,
    index_handle: BlockHandle,
}

impl Footer {
    pub const ENCODED_LENGTH: usize = 2 * BlockHandle::MAX_ENCODED_LENGTH + 8;

    pub fn encode_to(&self, dst: &mut Vec<u8>) {
        let original_size = dst.len();
        self.metaindex_handle.encode_to(dst);
        self.index_handle.encode_to(dst);
        dst.resize(2 * BlockHandle::MAX_ENCODED_LENGTH, 0);
        coding::encode_fixed_32_vec(dst, (TABLE_MAGIC_NUMBER & 0xffffffff) as u32);
        coding::encode_fixed_32_vec(dst, (TABLE_MAGIC_NUMBER >> 32) as u32);
        assert_eq!(dst.len(), original_size + Footer::ENCODED_LENGTH);
    }

    pub fn decode_from(src: &mut Slice) -> Result<Footer> {
        let original_size = src.size();

        let magic_data = &src.data()[Footer::ENCODED_LENGTH - 8..];
        let magic_lo: u32 = coding::decode_fixed_32(&magic_data);
        let magic_hi: u32 = coding::decode_fixed_32(&magic_data[4..]);
        let magic = ((magic_hi as u64) << 32) | (magic_lo as u64);
        if magic != TABLE_MAGIC_NUMBER {
            return Err(Error::new(
                ErrorType::Corruption,
                "not a sstable (bad magic number)",
            ));
        }

        let metaindex_handle = BlockHandle::decode_from(src)?;
        let index_handle = BlockHandle::decode_from(src)?;
        src.remove_prefix(Footer::ENCODED_LENGTH - original_size + src.size());

        let result = Footer {
            metaindex_handle,
            index_handle,
        };
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn block_handle() {
        let actual = BlockHandle {
            offset: 10,
            size: 20,
        };

        let mut encoded = Vec::new();
        actual.encode_to(&mut encoded);

        let mut slice = Slice::from(&encoded);
        let expected = BlockHandle::decode_from(&mut slice).expect("OK");
        assert_eq!(expected, actual);
    }

    #[test]
    fn footer() {
        let metaindex_handle = BlockHandle {
            offset: 50,
            size: 100,
        };
        let index_handle = BlockHandle {
            offset: 200,
            size: 400,
        };
        let actual = Footer {
            metaindex_handle,
            index_handle,
        };

        let mut encoded = Vec::new();
        actual.encode_to(&mut encoded);
        assert_eq!(Footer::ENCODED_LENGTH, encoded.len());

        let mut slice = Slice::from(&encoded);
        let expected = Footer::decode_from(&mut slice).expect("OK");
        assert_eq!(expected, actual);
    }
}
