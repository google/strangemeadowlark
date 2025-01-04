// Copyright 2023 Google LLC
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

#![allow(unused_variables)]
#![allow(dead_code)]

mod binding;
mod mir;
mod parse;
mod print;
mod quote;
mod resolve;
mod scan;
mod syntax;
mod token;
mod value;
mod walk;

pub use mir::{Lowered, MirBuilder};
pub use parse::{parse, parse_expr, parse_with_mode, Mode, ParseError};
pub use print::Printer;
pub use resolve::resolve_file;
pub use syntax::*;
pub use token::*;
pub use value::{StarlarkType, Value};
pub use walk::{Node, NodeIterator};
