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

use std::cell::Cell;
use std::sync::atomic::Ordering;
use std::sync::atomic::compiler_fence;

/// An atomic cell implemented using compiler fences.
pub struct AtomicCell<T: Copy> {
  rep: Cell<T>
}

impl<T: Copy> AtomicCell<T> {
  pub fn new(r: T) -> Self { Self { rep: Cell::new(r) } }

  #[inline]
  pub fn no_barrier_load(&self) -> T {
    self.rep.get()
  }

  #[inline]
  pub fn no_barrier_store(&self, v: T) {
    self.rep.set(v);
  }

  #[inline]
  pub fn acquire_load(&self) -> T {
    let result = self.rep.get();
    compiler_fence(Ordering::Acquire);
    result
  }

  #[inline]
  pub fn release_store(&self, v: T) {
    compiler_fence(Ordering::Release);
    self.rep.set(v);
  }
}
