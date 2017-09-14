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

pub struct Random {
  seed: u32
}

/// A simple random number generator that uses multiplicative
/// congruential generator (MCG).
impl Random {
  pub fn new(s: u32) -> Self {
    let mut seed = s & 0x7fffffffu32;
    if seed == 0 || seed == 2147483647 {
      seed = 1
    }
    Self { seed: seed }
  }

  /// Returns the next random number in this generator.
  pub fn next(&mut self) -> u32 {
    // See https://en.wikipedia.org/wiki/Linear_congruential_generator
    let m: u32 = 2147483647;
    let a: u64 = 16807;
    let product: u64 = self.seed as u64 * a;

    self.seed = (product >> 31) as u32 + ((product as u32) & m);

    if self.seed > m { self.seed -= m }
    self.seed
  }

  /// Returns a uniformly distributed value in the range `[0..n)`
  #[inline(always)]
  pub fn uniform(&mut self, n: u32) -> u32 {
    self.next() % n
  }

  /// Randomly returns true ~ "1/n" of the time. False otherwise.
  #[inline(always)]
  pub fn one_in(&mut self, n: u32) -> bool {
    self.next() % n == 0
  }

  /// Skewed: this first pick "base" uniformly from range `[0, max_log]`,
  /// and then return "base" random bits. The effect is to pick a random
  /// number in the range `[0, 2^max_log)` with exponential bias towards
  /// smaller numbers.
  #[inline(always)]
  pub fn skewed(&mut self, max_log: u32) -> u32 {
    let r = 1 << self.uniform(max_log + 1);
    self.uniform(r)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  // Some simple sanity tests
  #[test]
  fn test_random() {
    let mut rnd = Random::new(0);
    assert_eq!(rnd.seed, 1);
    rnd = Random::new(2147483647);
    assert_eq!(rnd.seed, 1);

    rnd = Random::new(3);
    assert_eq!(rnd.next(), 50421);
    assert_eq!(rnd.uniform(10), 7);
    assert_eq!(rnd.skewed(2), 1);
  }
}
