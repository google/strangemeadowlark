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

use googletest::prelude::*;
use std::io::Write;
use std::process::{Command, Stdio};
use strangemeadowlark::{Arena, Mode, parse_with_mode, pretty::pretty};

fn buildify(input: &str) -> Option<String> {
    let mut child = match Command::new("buildifier")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return None,
        Err(e) => panic!("Failed to spawn buildifier: {e}"),
    };

    let mut stdin = child.stdin.take().expect("Failed to open stdin");
    stdin
        .write_all(input.as_bytes())
        .expect("Failed to write to stdin");
    drop(stdin);

    let output = child.wait_with_output().expect("Failed to read stdout");
    Some(String::from_utf8(output.stdout).expect("Invalid UTF-8 from buildifier"))
}

fn assert_parity(src: &str) {
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &"<test>", src, Mode::RetainComments).unwrap();
    let my_output = pretty(&unit);
    let buildifier_output = match buildify(src) {
        Some(output) => output,
        None => {
            println!("Skipping buildifier parity check: buildifier not found");
            return;
        }
    };

    assert_that!(my_output, eq(&buildifier_output));
}

#[test]
fn test_parity_simple() -> googletest::prelude::Result<()> {
    assert_parity("x = 1\ny = 2\n");
    Ok(())
}

#[test]
fn test_parity_def() -> googletest::prelude::Result<()> {
    assert_parity("def f(x):\n    return x + 1\n");
    Ok(())
}

#[test]
fn test_parity_load() -> googletest::prelude::Result<()> {
    assert_parity("load(\"//foo:bar.bzl\", \"b\", \"a\")\nx = 1\n");
    Ok(())
}

#[test]
fn test_parity_dict_list() -> googletest::prelude::Result<()> {
    assert_parity("l = [1, 2, 3]\nd = {\"a\": 1, \"b\": 2}\n");
    Ok(())
}

#[test]
fn test_parity_comprehensions() -> googletest::prelude::Result<()> {
    assert_parity("[x for x in y if cond]\n");
    assert_parity("{k: v for k, v in items}\n");
    Ok(())
}

#[test]
fn test_parity_various_exprs() -> googletest::prelude::Result<()> {
    assert_parity("x = a.b\ny = a[i]\nz = a[1:2:3]\n");
    assert_parity("x = (1 + 2) * 3\ny = -1\nz = not True\n");
    assert_parity("lambda x: x + 1\n");
    assert_parity("a if b else c\n");
    Ok(())
}

#[test]
fn test_parity_nested() -> googletest::prelude::Result<()> {
    assert_parity("def f():\n    for x in l:\n        if cond:\n            print(x)\n");
    Ok(())
}

#[test]
fn test_parity_comments() -> googletest::prelude::Result<()> {
    assert_parity("# Leading\nx = 1 # suffix\n");
    Ok(())
}

#[test]
fn test_parity_complex_def() -> googletest::prelude::Result<()> {
    assert_parity("def f(a, b = 1, *args, c, d = 2, **kwargs):\n    pass\n");
    Ok(())
}

#[test]
fn test_parity_mixed_comments() -> googletest::prelude::Result<()> {
    let src = "\
# Group 1
x = 1

# Group 2
# Multi-line
def f():
    pass # suffix
";
    assert_parity(src);
    Ok(())
}

#[test]
fn test_parity_long_args() -> googletest::prelude::Result<()> {
    // This string is long enough that it might wrap.
    // Buildifier wraps args if they don't fit.
    // We'll see if our pretty printer matches.
    // We intentionally use a long line that *should* fit in 100 chars (if small indent)
    // or definitely NOT fit if we make it super long.
    // Let's try one that is clearly single line for now to ensure no regression,
    // and one that forces wrap.

    // Simple fit
    assert_parity("f(1, 2, 3, 4, 5, 6)\n");

    // Long line that should wrap
    // Buildifier wraps lists of arguments if they are too long.
    // We use many arguments to exceed the limit.
    let args = (0..30)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let src = format!("f({args})\n");
    assert_parity(&src);

    Ok(())
}
