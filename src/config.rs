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

pub const NUM_LEVELS: i32 = 7;

/// Level-0 compaction is triggered when we hit this many files.
pub const L0_COMPACTION_TRIGGER: i32 = 4;

/// Soft limit on number of level-0 files. We slow down writes at this point.
pub const L0_SLOWDOWN_WRITES_TRIGGER: i32 = 8;

/// Maximum number of level-0 files. We stop writes at this point.
pub const L0_STOP_WRITES_TRIGGER: i32 = 12;
