// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{ExprId, StmtId};
use std::sync::atomic::{AtomicUsize, Ordering};

pub static ID_GEN: IdGen = IdGen {
    id: AtomicUsize::new(1),
};

pub struct IdGen {
    id: AtomicUsize,
}

impl IdGen {
    pub fn next_expr_id(&self) -> ExprId {
        ExprId(self.id.fetch_add(1, Ordering::Relaxed))
    }

    pub fn next_stmt_id(&self) -> StmtId {
        StmtId(self.id.fetch_add(1, Ordering::Relaxed))
    }
}
