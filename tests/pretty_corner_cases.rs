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
use strangemeadowlark::{Arena, Mode, parse_with_mode, pretty::pretty};

fn check_roundtrip(src: &str) {
    let arena = Arena::new();
    let unit = parse_with_mode(&arena, &"<test>", src, Mode::RetainComments).unwrap();
    let output = pretty(&unit);
    assert_that!(output, eq(src));
}

#[test]
fn test_suffix_comment_comma_placement_list() {
    let src = r#"
l = [
    1,  # comment
    2,
]
"#;
    // Remove first newline for comparison if pretty prints trim it?
    // No, pretty prints usually start at line 1.
    // My input has leading newline.
    // pretty() adds a newline at the end if missing.
    // The parser handles leading newlines as empty statements? No, it ignores them.
    // So "l = ..." is the first statement.
    // But pretty printer will print "l = ..." at start.
    // So I should trim the leading newline from my test string.
    check_roundtrip(src.trim_start());
}

#[test]
fn test_suffix_comment_comma_placement_call() {
    let src = r#"
f(
    1,  # comment
    2,
)
"#;
    check_roundtrip(src.trim_start());
}

#[test]
fn test_single_element_tuple_comma() {
    let src = "(1,)\n";
    check_roundtrip(src);
}

#[test]
fn test_multiline_list_preserved() {
    let src = r#"
l = [
    "short",
    "list",
]
"#;
    check_roundtrip(src.trim_start());
}

#[test]
fn test_single_line_list_compact() {
    let src = r#"l = ["short"]
"#;
    check_roundtrip(src);
}

#[test]
fn test_single_line_list_compact_multiple() {
    let src = "l = [1, 2, 3]\n";
    check_roundtrip(src);
}

#[test]
fn test_load_suffix_comment() {
    let src = r#"load("//foo:bar.bzl", "a", "b")  # suffix
"#;
    check_roundtrip(src);
}

#[test]
fn test_load_multiline_preserved() {
    let src = r#"
load(
    "//foo:bar.bzl",
    "a",
    "b",
)
"#;
    check_roundtrip(src.trim_start());
}

#[test]
fn test_def_params_suffix_comment() {
    let src = r#"
def f(
    a,  # comment
    b,
):
    pass
"#;
    check_roundtrip(src.trim_start());
}

#[test]
fn test_def_multiline_preserved() {
    let src = r#"
def f(
    a,
    b,
):
    pass
"#;
    check_roundtrip(src.trim_start());
}

#[test]
fn test_dict_suffix_comment() {
    let src = r#"
d = {
    "k": v,  # comment
    "k2": v2,
}
"#;
    check_roundtrip(src.trim_start());
}
