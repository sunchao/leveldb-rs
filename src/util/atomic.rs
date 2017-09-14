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

use std::cell::UnsafeCell;
use std::sync::atomic::Ordering;
use std::sync::atomic::compiler_fence;

// -------------------------------------------------------------------
// Atomic types implemented using compile fences in Rust

pub struct AtomicPointer<T> {
  rep: UnsafeCell<*mut T>
}

impl<T> AtomicPointer<T> {
  pub fn new(r: *mut T) -> Self { Self { rep: UnsafeCell::new(r) } }

  #[inline(always)]
  pub fn no_barrier_load(&self) -> *mut T {
    unsafe { *self.rep.get() }
  }

  #[inline(always)]
  pub fn no_barrier_store(&self, v: *mut T) {
    unsafe { *self.rep.get() = v; }
  }

  #[inline(always)]
  pub fn acquire_load(&self) -> *mut T {
    unsafe {
      let result = self.rep.get();
      compiler_fence(Ordering::Acquire);
      *result
    }
  }

  #[inline(always)]
  pub fn release_store(&mut self, v: *mut T) {
    compiler_fence(Ordering::Release);
    unsafe { *self.rep.get() = v; }
  }
}

unsafe impl<T> Sync for AtomicPointer<T> {}
unsafe impl<T> Send for AtomicPointer<T> {}


macro_rules! define_scalar_atomic {
  ($type_name:ident, $type:ty) => {
    pub struct $type_name {
      rep: UnsafeCell<$type>
    }

    impl $type_name {
      pub fn new(r: $type) -> Self {
        Self {
          rep: UnsafeCell::new(r)
        }
      }

      #[inline(always)]
      pub fn no_barrier_load(&self) -> $type {
        unsafe { *self.rep.get() }
      }

      #[inline(always)]
      pub fn no_barrier_store(&self, v: $type) {
        unsafe { *self.rep.get() = v; }
      }

      #[inline(always)]
      pub fn acquire_load(&self) -> $type {
        unsafe {
          let result = self.rep.get();
          compiler_fence(Ordering::Acquire);
          *result
        }
      }

      #[inline(always)]
      pub fn release_store(&self, v: $type) {
        compiler_fence(Ordering::Release);
        unsafe { *self.rep.get() = v; }
      }
    }

    unsafe impl Send for $type_name {}
    unsafe impl Sync for $type_name {}
  }
}

define_scalar_atomic!(AtomicBool, bool);
define_scalar_atomic!(AtomicI8, i8);
define_scalar_atomic!(AtomicI16, i16);
define_scalar_atomic!(AtomicI32, i32);
define_scalar_atomic!(AtomicI64, i64);
define_scalar_atomic!(AtomicIsize, isize);
define_scalar_atomic!(AtomicU8, u8);
define_scalar_atomic!(AtomicU16, u16);
define_scalar_atomic!(AtomicU32, u32);
define_scalar_atomic!(AtomicU64, u64);
define_scalar_atomic!(AtomicUsize, usize);
