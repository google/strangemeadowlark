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

use anyhow::{anyhow, Result};
use std::{env, fs::read_to_string};
use strangemeadowlark::{parse_with_mode, resolve_file, Arena, Mode, Printer};

// E.g. cargo run --example test_parse third_party/mangle/BUILD
fn main() -> Result<()> {
    if env::args().len() != 2 {
        return Err(anyhow!("need exactly one arg"));
    }

    let path = env::args().into_iter().nth(1).unwrap();
    let src = read_to_string(&path)?;
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &path, &src, Mode::RetainComments)?;
    let _fm = resolve_file(unit, &arena, |_| false, |_| false).map_err(|e| anyhow!("{e:?}"))?;

    for stmt in unit.stmts {
        println!("{}", stmt.data);
    }
    let mut buf = String::new();
    let mut printer = Printer::new(unit, &mut buf);
    printer.print_file_unit()?;
    println!("{}", buf);

    Ok(())
}
