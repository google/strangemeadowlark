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
use bumpalo::Bump;
use std::{env, fs::read_to_string};
use strangemeadowlark::{parse, resolve_file, Mode, Printer};

// E.g. cargo run --example test_parse third_party/mangle/BUILD
fn main() -> Result<()> {
    if env::args().len() != 2 {
        return Err(anyhow!("need exactly one arg"));
    }

    let path = env::args().into_iter().nth(1).unwrap();

    let src = read_to_string(&path)?;
    let bump = Bump::new();
    let unit = parse(&bump, &path, &src, Mode::RetainComments)?;
    _ = resolve_file(unit, &bump, |_| false, |_| false)?;
    for stmt in unit.stmts {
        println!("{}", stmt.data);
    }

    let mut buf = String::new();
    let mut printer = Printer::new(unit, &mut buf);
    printer.print_file_unit()?;
    println!("{}", buf);

    Ok(())
}
