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

use std::sync::atomic::Ordering;
use std::sync::atomic::compiler_fence;

// -------------------------------------------------------------------
// Atomic types implemented using compile fences in Rust

pub struct AtomicPtr<T> {
  rep: *mut T
}

impl<T> AtomicPtr<T> {
  pub fn new(r: *mut T) -> Self { Self { rep: r } }

  #[inline(always)]
  pub fn no_barrier_load(&self) -> *mut T {
    self.rep
  }

  #[inline(always)]
  pub fn no_barrier_store(&mut self, v: *mut T) {
    self.rep = v;
  }

  #[inline(always)]
  pub fn acquire_load(&self) -> *mut T {
    let result = self.rep;
    compiler_fence(Ordering::Acquire);
    result
  }

  #[inline(always)]
  pub fn release_store(&mut self, v: *mut T) {
    compiler_fence(Ordering::Release);
    self.rep = v;
  }
}


pub struct AtomicI64 {
  rep: i64
}

impl AtomicI64 {
  pub fn new(r: i64) -> Self { Self { rep: r } }

  #[inline(always)]
  pub fn no_barrier_load(&self) -> i64 {
    self.rep
  }

  #[inline(always)]
  pub fn no_barrier_store(&mut self, v: i64) {
    self.rep = v;
  }

  #[inline(always)]
  pub fn acquire_load(&self) -> i64 {
    let result = self.rep;
    compiler_fence(Ordering::Acquire);
    result
  }

  #[inline(always)]
  pub fn release_store(&mut self, v: i64) {
    compiler_fence(Ordering::Release);
    self.rep = v;
  }
}
