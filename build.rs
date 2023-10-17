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

use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

fn main() {
    let path = Path::new(&env::var("OUT_DIR").unwrap()).join("keyword_token_codegen.rs");
    let mut file = BufWriter::new(File::create(&path).unwrap());

    write!(
        &mut file,
        "// keywordToken records the special tokens for
// strings that should not be treated as ordinary identifiers.
pub static KEYWORD_TOKEN: phf::Map<&'static str, Token> = {}",
        phf_codegen::Map::new()
            .entry("and", "Token::And")
            .entry("break", "Token::Break")
            .entry("continue", "Token::Continue")
            .entry("def", "Token::Def")
            .entry("elif", "Token::Elif")
            .entry("else", "Token::Else")
            .entry("for", "Token::For")
            .entry("if", "Token::If")
            .entry("in", "Token::In")
            .entry("lambda", "Token::Lambda")
            .entry("load", "Token::Load")
            .entry("not", "Token::Not")
            .entry("or", "Token::Or")
            .entry("pass", "Token::Pass")
            .entry("return", "Token::Return")
            .entry("while", "Token::While")
            // reserved words
            .entry("as", "Token::Illegal")
            // "assert", "Token::Illegal, // heavily used by our tests
            .entry("async", "Token::Illegal")
            .entry("await", "Token::Illegal")
            .entry("class", "Token::Illegal")
            .entry("del", "Token::Illegal")
            .entry("except", "Token::Illegal")
            .entry("finally", "Token::Illegal")
            .entry("from", "Token::Illegal")
            .entry("global", "Token::Illegal")
            .entry("import", "Token::Illegal")
            .entry("is", "Token::Illegal")
            .entry("nonlocal", "Token::Illegal")
            .entry("raise", "Token::Illegal")
            .entry("try", "Token::Illegal")
            .entry("with", "Token::Illegal")
            .entry("yield", "Token::Illegal")
            .build()
    )
    .unwrap();
    write!(&mut file, ";\n").unwrap();
}
