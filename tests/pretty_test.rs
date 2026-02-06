// Copyright 2024 Google LLC
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

use strangemeadowlark::{Arena, Mode, parse_with_mode, pretty::pretty};

#[test]
fn test_pretty_basic() -> googletest::prelude::Result<()> {
    let src = "load(\"//foo:bar.bzl\", \"a\", \"b\")\nx = 1\ndef f(x):\n    return x + 1\nf(x)\n";
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &"<test>", src, Mode::RetainComments).unwrap();
    let output = pretty(&unit);
    println!("--- test_pretty_basic ---");
    println!("{output}");
    Ok(())
}

#[test]
fn test_pretty_indent() -> googletest::prelude::Result<()> {
    let src = "def f():\n    if True:\n        pass\n    else:\n        return 42\n";
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &"<test>", src, Mode::RetainComments).unwrap();
    let output = pretty(&unit);
    println!("--- test_pretty_indent ---");
    println!("{output}");
    Ok(())
}

#[test]
fn test_pretty_load_sorting() -> googletest::prelude::Result<()> {
    let src = "x = 1\nload(\"//foo:bar.bzl\", \"b\", \"a\")\nload(\"//aaa:bbb.bzl\", \"c\")\n";
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &"<test>", src, Mode::RetainComments).unwrap();
    let output = pretty(&unit);
    println!("--- test_pretty_load_sorting ---");
    println!("{output}");
    Ok(())
}

#[test]
fn test_pretty_comments() -> googletest::prelude::Result<()> {
    let src = "\
# Leading comment
load(\"//foo:bar.bzl\", \"a\") # suffix comment

# Comment before x
x = 1

def f():
    # Comment inside def
    pass # suffix inside def

# Trailing comment
";
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &"<test>", src, Mode::RetainComments).unwrap();
    let output = pretty(&unit);
    println!("--- test_pretty_comments ---");
    println!("{output}");
    Ok(())
}
