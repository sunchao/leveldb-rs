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

#![feature(test)]
extern crate leveldb;
extern crate rand;
extern crate test;

macro_rules! bench_sw {
    ($bench_name:ident, $block_size:expr) => {
        #[bench]
        fn $bench_name(b: &mut ::test::Bencher) {
            let block_data = vec!['x' as u8; $block_size];
            b.bytes = block_data.len() as u64;
            b.iter(|| {
                ::leveldb::util::crc32c::extend_sw(0, &block_data);
            })
        }
    };
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse4.2")]
macro_rules! bench_hw {
    ($bench_name:ident, $block_size:expr) => {
        #[bench]
        fn $bench_name(b: &mut ::test::Bencher) {
            let block_data = vec!['x' as u8; $block_size];
            b.bytes = block_data.len() as u64;
            b.iter(|| unsafe {
                ::leveldb::util::crc32c::extend_hw(0, &block_data);
            })
        }
    };
}

bench_sw!(sw_00000256, 00000256);
bench_sw!(sw_00004096, 00004096);
bench_sw!(sw_00060056, 00060056);
bench_sw!(sw_01048576, 01048576);
bench_sw!(sw_16777216, 16777216);

bench_hw!(hw_00000256, 00000256);
bench_hw!(hw_00004096, 00004096);
bench_hw!(hw_00060056, 00060056);
bench_hw!(hw_01048576, 01048576);
bench_hw!(hw_16777216, 16777216);
