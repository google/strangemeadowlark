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

use crate::token::{keyword, IntValue, Token};
use crate::Literal;
use anyhow::anyhow;
use bumpalo::Bump;
use std::fmt::Display;
use std::path::Path;

// A Position describes the location of a rune of input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    pub line: u32, // 1-based line number; 0 if line unknown
    pub col: u32,  // 1-based column (rune) number; 0 if column unknown
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}",
            //self.path.to_string_lossy(),
            self.line,
            self.col
        )
    }
}

impl Position {
    pub fn new() -> Position {
        Position { line: 1, col: 1 }
    }
}

#[derive(Clone, Debug, PartialEq)]
// A Comment represents a single # comment.
pub struct Comment<'a> {
    pub start: Position,
    pub text: &'a str, // without trailing newline
}

pub struct Scanner<'a, 'b> {
    bump: &'b Bump,
    path: &'a Path,
    rest: &'a str,
    pub token: &'a str,                        //  slice with current token
    pub pos: Position,                         // current input position
    depth: usize,                              // nesting of [ ] { } ( )
    indentstk: Vec<usize>,                     // stack of indentation levels
    dents: i8,           // number of saved INDENT (>0) or OUTDENT (<0) tokens to return
    line_start: bool,    // after NEWLINE; convert spaces to indentation tokens
    keep_comments: bool, // accumulate comments in slice
    pub line_comments: Vec<&'b Comment<'b>>, // list of full line comments (if keepComments)
    pub suffix_comments: Vec<&'b Comment<'b>>, // list of suffix comments (if keepComments)
    token_buf: TokenValue,
}

#[derive(Clone, Debug)]
pub struct TokenValue {
    pub kind: Token,
    pub pos: Position, // start position of token
}

const TRIPLE_QUOTE: &str = "'''";
const TRIPLE_DOUBLE_QUOTE: &str = "\"\"\"";

impl<'a, 'b> Scanner<'a, 'b>
where
    'b: 'a,
{
    // The scanner operates on &str, advancing one char at a time.
    // path is only used in error messages.
    pub fn new<P: AsRef<Path>>(
        bump: &'b Bump,
        path: &'a P,
        data: &'a str,
        keep_comments: bool,
    ) -> anyhow::Result<Scanner<'a, 'b>> {
        //let pos = Position::new();//path.as_ref());
        Ok(Scanner {
            bump,
            path: path.as_ref(),
            pos: Position::new(),
            indentstk: vec![0],
            line_start: true,
            keep_comments,
            rest: data,
            token: data,
            depth: 0,
            dents: 0,
            line_comments: vec![],
            suffix_comments: vec![],
            token_buf: TokenValue {
                kind: Token::Illegal,
                pos: Position::new(),
            },
        })
    }

    // peek returns the next char in the input without consuming it.
    // Newlines in Unix, DOS, or Mac format are treated as one rune, '\n'.
    fn peek(&self) -> char {
        if self.rest.is_empty() {
            return '\0';
        }
        let c = self.rest.chars().next().unwrap();

        if c == '\r' {
            return '\n';
        }
        c
    }

    fn read(&mut self) -> char {
        if self.rest.is_empty() {
            return '\0';
        }
        let mut c = self.rest.chars().next().unwrap();
        self.rest = &self.rest[c.len_utf8()..];

        if c == '\r' {
            if !self.rest.is_empty() && self.rest.starts_with('\n') {
                self.rest = &self.rest[1..];
            }
            c = '\n';
        }
        if c == '\n' {
            self.pos.line += 1;
            self.pos.col = 1;
            return c;
        }
        self.pos.col += 1;
        c
    }

    fn mark_start_token(&mut self) {
        self.token = self.rest;
        self.token_buf.pos = self.pos;
    }

    fn mark_end_token(&mut self) {
        let len = self.token.len() - self.rest.len();
        self.token = &self.token[..len];
    }

    // nextToken is called by the parser to obtain the next input token.
    // It returns the token value and sets val to the data associated with
    // the token.
    //'
    // For all our input tokens, the associated data is token_buf.pos (the
    // position where the token begins), token (the input string
    // corresponding to the token).  For string and int tokens, the decoded
    // field additionally contains the token's interpreted value.
    pub fn next_token(&mut self) -> anyhow::Result<TokenValue> {
        self.next_token_internal().map(|()| self.token_buf.clone())
    }

    pub fn literal_from_token(&self, token: Token) -> &'b Literal<'b> {
        self.bump.alloc(match token {
            Token::String { decoded } => Literal::String(self.bump.alloc_str(&decoded)),
            Token::Int {
                decoded: IntValue::Int(n),
            } => Literal::Int(n),
            Token::Int {
                decoded: IntValue::BigInt(n),
            } => Literal::BigInt(n),
            Token::Float { float_value } => Literal::Float(float_value),
            _ => Literal::Int(-1), // cannot happen
        })
    }

    pub fn next_token_internal(&mut self) -> anyhow::Result<()> {
        #[allow(clippy::never_loop)] // clippy is wrong here.
        loop {
            self.token_buf.kind = Token::Illegal;
            'start: loop {
                let mut c: char;

                // Deal with leading spaces and indentation.
                let mut blank = false;
                let saved_line_start = self.line_start;
                if self.line_start {
                    self.line_start = false;
                    let mut col = 0;
                    loop {
                        c = self.peek();
                        if c == ' ' {
                            col += 1;
                            self.read();
                        } else if c == '\t' {
                            let tab = 8;
                            col += (tab - (self.pos.col - 1) % tab) as usize;
                            self.read();
                        } else {
                            break;
                        }
                    }

                    // The third clause matches eof.
                    if c == '#' || c == '\n' || c == '\0' {
                        blank = true
                    }

                    // Compute indentation level for non-blank lines not
                    // inside an expression.  This is not the common case.
                    if !blank && self.depth == 0 {
                        let cur = self.indentstk.last().copied().unwrap();
                        match col.cmp(&cur) {
                            std::cmp::Ordering::Less => {
                                // outdent(s)
                                while !self.indentstk.is_empty()
                                    && col < *self.indentstk.last().unwrap()
                                {
                                    self.dents -= 1;
                                    self.indentstk.pop();
                                }
                                if col != *self.indentstk.last().unwrap() {
                                    return Err(anyhow!(
                                        "{}{:?} unindent does not match any outer indentation level",
                                        self.path.to_string_lossy(),
                                        self.pos
                                    ));
                                }
                            }
                            std::cmp::Ordering::Equal => {}
                            std::cmp::Ordering::Greater => {
                                // indent
                                self.dents += 1;
                                self.indentstk.push(col)
                            }
                        }
                    }
                } // if self.line_start

                // Return saved indentation tokens.
                if self.dents != 0 {
                    if self.dents < 0 {
                        self.dents += 1;
                        self.token_buf.kind = Token::Outdent;
                        self.token_buf.pos = self.pos;
                        return Ok(());
                    } else {
                        self.dents -= 1;
                        self.token_buf.kind = Token::Indent;
                        self.token_buf.pos = self.pos;
                        return Ok(());
                    }
                }

                // start of line proper
                c = self.peek();

                // Skip spaces.
                while c == ' ' || c == '\t' {
                    self.read();
                    c = self.peek()
                }

                // comment
                if c == '#' {
                    if self.keep_comments {
                        self.mark_start_token();
                    }
                    let comment_pos = self.pos;
                    // Consume up to newline (included).
                    while c != '\0' && c != '\n' {
                        self.read();
                        c = self.peek()
                    }
                    if self.keep_comments {
                        self.mark_end_token();
                        if blank {
                            self.line_comments.push(self.bump.alloc(Comment {
                                start: comment_pos,
                                text: self.bump.alloc_str(self.token),
                            }))
                        } else {
                            self.suffix_comments.push(self.bump.alloc(Comment {
                                start: comment_pos,
                                text: self.bump.alloc_str(self.token),
                            }))
                        }
                    }
                }

                // newline
                if c == '\n' {
                    let newline_pos = self.pos;
                    self.line_start = true;

                    // Ignore newlines within expressions (common case).
                    if self.depth > 0 {
                        self.read();
                        break 'start;
                    }

                    // Ignore blank lines.
                    if blank {
                        self.read();
                        break 'start;
                    }
                    // At top-level (not in an expression).
                    self.mark_start_token();
                    self.read();
                    self.token_buf.kind = Token::Newline;
                    self.token_buf.pos = newline_pos;
                    self.token = "\n";
                    return Ok(());
                }

                // end of file
                if c == '\0' {
                    // Emit OUTDENTs for unfinished indentation,
                    // preceded by a NEWLINE if we haven't just emitted one.
                    if self.indentstk.len() > 1 {
                        if saved_line_start {
                            self.dents = 1 - self.indentstk.len() as i8;
                            self.indentstk.pop();
                            break 'start;
                        } else {
                            self.line_start = true;
                            self.mark_start_token();
                            self.token_buf.kind = Token::Newline;
                            self.token = "\n";
                            return Ok(());
                        }
                    }

                    self.mark_start_token();
                    self.mark_end_token();
                    self.token_buf.kind = Token::Eof;
                    return Ok(());
                }

                // line continuation
                if c == '\\' {
                    self.read();
                    if self.peek() != '\n' {
                        return Err(anyhow!(
                            "{}{} stray backslash in program",
                            self.path.to_string_lossy(),
                            self.pos
                        ));
                    }
                    self.read();
                    break 'start;
                }

                // start of the next token
                self.mark_start_token();

                // comma (common case)
                if c == ',' {
                    self.read();
                    self.mark_end_token();
                    self.token_buf.kind = Token::Comma;
                    self.token_buf.pos = self.pos;
                    return Ok(());
                }

                // string literal
                if c == '"' || c == '\'' {
                    return self.scan_string(c);
                }

                // identifier or keyword
                if is_ident_start(c) {
                    if (c == 'r' || c == 'b')
                        && self.rest.len() > 1
                        && ({
                            let next = self.rest.chars().nth(1).unwrap();
                            next == '"' || next == '\''
                        })
                    {
                        //  r"..."
                        //  b"..."
                        self.read();
                        c = self.peek();
                        return self.scan_string(c);
                    } else if c == 'r'
                        && self.rest.len() > 2
                        && ({
                            let prefix = &self.rest[..2];
                            prefix == "b\"" || prefix == "b'"
                        })
                    {
                        // rb"..."
                        self.read();
                        self.read();
                        c = self.peek();
                        return self.scan_string(c);
                    }

                    while is_ident(c) {
                        self.read();
                        c = self.peek()
                    }
                    self.mark_end_token();
                    match keyword(self.token) {
                        Some(k) => self.token_buf.kind = k.clone(),
                        _ => {
                            self.token_buf.kind = Token::Ident {
                                name: self.token.to_owned(),
                            }
                        }
                    }
                    return Ok(());
                }

                // brackets
                match c {
                    '[' | '(' | '{' => {
                        self.depth += 1;
                        self.read();
                        self.mark_end_token();

                        match c {
                            '[' => {
                                self.token_buf.kind = Token::LBrack;
                                return Ok(());
                            }
                            '(' => {
                                self.token_buf.kind = Token::LParen;
                                return Ok(());
                            }
                            '{' => {
                                self.token_buf.kind = Token::LBrace;
                                return Ok(());
                            }
                            _ => unreachable!(),
                        }
                    }
                    ']' | ')' | '}' => {
                        if self.depth == 0 {
                            return Err(anyhow!(
                                "{}:{} unexpected '{}'",
                                self.path.to_string_lossy(),
                                self.pos,
                                c
                            ));
                        } else {
                            self.depth -= 1
                        }
                        self.read();
                        self.mark_end_token();
                        match c {
                            ']' => {
                                self.token_buf.kind = Token::RBrack;
                                return Ok(());
                            }
                            ')' => {
                                self.token_buf.kind = Token::RParen;
                                return Ok(());
                            }
                            '}' => {
                                self.token_buf.kind = Token::RBrace;
                                return Ok(());
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => {}
                }

                // int or float literal, or period
                if c.is_ascii_digit() || c == '.' {
                    return self.scan_number(c);
                }

                // other punctuation
                match c {
                    '=' | '<' | '>' | '!' | '+' | '-' | '%' | '/' | '&' | '|' | '^' => {
                        // possibly followed by '='
                        let start = self.pos;
                        self.read();
                        if self.peek() == '=' {
                            self.read();
                            match c {
                                '<' => {
                                    self.token_buf.kind = Token::Le;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '>' => {
                                    self.token_buf.kind = Token::Ge;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '=' => {
                                    self.token_buf.kind = Token::EqEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '!' => {
                                    self.token_buf.kind = Token::Neq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '+' => {
                                    self.token_buf.kind = Token::PlusEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '-' => {
                                    self.token_buf.kind = Token::MinusEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '/' => {
                                    self.token_buf.kind = Token::SlashEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '%' => {
                                    self.token_buf.kind = Token::PercentEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '&' => {
                                    self.token_buf.kind = Token::AmpersandEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '|' => {
                                    self.token_buf.kind = Token::PipeEq;
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                '^' => {
                                    self.mark_end_token();
                                    self.token_buf.kind = Token::CaretEq;
                                    return Ok(());
                                }
                                _ => unreachable!(),
                            }
                        } // if '='
                        match c {
                            '=' => {
                                self.token_buf.kind = Token::Eq;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '<' => {
                                if self.peek() == '<' {
                                    self.read();
                                    if self.peek() == '=' {
                                        self.read();
                                        self.token_buf.kind = Token::LtLtEq;
                                    } else {
                                        self.token_buf.kind = Token::LtLt;
                                    }
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                self.mark_end_token();
                                self.token_buf.kind = Token::Lt;
                                return Ok(());
                            }
                            '>' => {
                                if self.peek() == '>' {
                                    self.read();
                                    if self.peek() == '=' {
                                        self.read();
                                        self.token_buf.kind = Token::GtGtEq;
                                    } else {
                                        self.token_buf.kind = Token::GtGt;
                                    }
                                    self.mark_end_token();
                                    return Ok(());
                                }
                                self.token_buf.kind = Token::Gt;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '!' => {
                                return Err(anyhow!(
                                    "{}{} unexpected input character '!'",
                                    self.path.to_string_lossy(),
                                    start
                                ))
                            }
                            '+' => {
                                self.token_buf.kind = Token::Plus;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '-' => {
                                self.token_buf.kind = Token::Minus;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '/' => {
                                if self.peek() == '/' {
                                    self.read();
                                    if self.peek() == '=' {
                                        self.read();
                                        self.token_buf.kind = Token::SlashSlashEq;
                                    } else {
                                        self.token_buf.kind = Token::SlashSlash;
                                    }
                                    return Ok(());
                                }
                                self.token_buf.kind = Token::Slash;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '%' => {
                                self.token_buf.kind = Token::Percent;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '&' => {
                                self.token_buf.kind = Token::Ampersand;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '|' => {
                                self.token_buf.kind = Token::Pipe;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '^' => {
                                self.token_buf.kind = Token::Caret;
                                self.mark_end_token();
                                return Ok(());
                            }
                            _ => unreachable!(),
                        } // match c
                    }
                    ':' | ';' | '~' => {
                        // single-char tokens (except comma)
                        self.read();
                        match c {
                            ':' => {
                                self.token_buf.kind = Token::Colon;
                                self.mark_end_token();
                                return Ok(());
                            }
                            ';' => {
                                self.token_buf.kind = Token::Semi;
                                self.mark_end_token();
                                return Ok(());
                            }
                            '~' => {
                                self.token_buf.kind = Token::Tilde;
                                self.mark_end_token();
                                return Ok(());
                            }
                            _ => unreachable!(),
                        } // match c
                    }

                    '*' => {
                        // possibly followed by '*' or '='
                        self.read();
                        match self.peek() {
                            '*' => {
                                self.read();
                                self.token_buf.kind = Token::StarStar;
                                return Ok(());
                            }
                            '=' => {
                                self.read();
                                self.token_buf.kind = Token::StarEq;
                                return Ok(());
                            }
                            _ => {
                                self.token_buf.kind = Token::Star;
                                return Ok(());
                            }
                        }
                    }
                    _ => {
                        return Err(anyhow!(
                            "{}:{} unexpected input character {}",
                            self.path.to_string_lossy(),
                            self.pos,
                            c
                        ))
                    }
                }
            }
        }
    }

    fn scan_string(&mut self, quote: char) -> anyhow::Result<()> {
        let triple = self.rest.starts_with(if quote == '\'' {
            TRIPLE_QUOTE
        } else {
            TRIPLE_DOUBLE_QUOTE
        });
        self.read();

        // String literals may contain escaped or unescaped newlines,
        // causing them to span multiple lines (gulps) of REPL input;
        // they are the only such token. Thus we cannot call endToken,
        // as it assumes self.rest is unchanged since startToken.
        // Instead, buffer the token here.
        let len = self.token.len() - self.rest.len();
        // Copy the prefix, e.g. r' or " (see mark_start_token).
        let mut raw: String = self.token[..len].to_string();
        if !triple {
            // single-quoted string literal
            loop {
                if self.rest.is_empty() {
                    return Err(anyhow!(
                        "{}:{:?} unexpected eof in string",
                        self.path.to_string_lossy(),
                        self.pos
                    ));
                }
                let mut c = self.read();
                raw.push(c);
                if c == quote {
                    break;
                }
                if c == '\n' {
                    return Err(anyhow!(
                        "{}:{:?} unexpected newline in string",
                        self.path.to_string_lossy(),
                        self.pos
                    ));
                }
                if c == '\\' {
                    if self.rest.is_empty() {
                        return Err(anyhow!(
                            "{}:{:?} unexpected eof in string",
                            self.path.to_string_lossy(),
                            self.pos
                        ));
                    }
                    c = self.read();
                    raw.push(c)
                }
            }
        } else {
            // triple-quoted string literal
            self.read();
            raw.push(quote);
            self.read();
            raw.push(quote);

            let mut quote_count = 0;
            loop {
                if self.rest.is_empty() {
                    return Err(anyhow!(
                        "{}:{:?} unexpected eof in string",
                        self.path.to_string_lossy(),
                        self.pos
                    ));
                }
                let mut c = self.read();
                raw.push(c);

                if c == quote {
                    quote_count += 1;
                    if quote_count == 3 {
                        break;
                    }
                } else {
                    quote_count = 0
                }
                if c == '\\' {
                    if self.rest.is_empty() {
                        return Err(anyhow!("{:?} unexpected eof in string", self.pos));
                    }
                    c = self.read();
                    raw.push(c)
                }
            }
        }
        self.token = "<literal>";
        match crate::quote::unquote(&raw) {
            Ok(crate::quote::DecodedSequence::String(decoded)) => {
                self.token_buf.kind = Token::String { decoded }
            }
            Ok(crate::quote::DecodedSequence::Bytes(decoded)) => {
                self.token_buf.kind = Token::Bytes { decoded }
            }
            Err(e) => {
                return Err(anyhow!(
                    "{}:{} error unquoting: {}",
                    self.path.to_string_lossy(),
                    self.pos,
                    e
                ))
            }
        }
        Ok(())
    }

    fn scan_number(&mut self, ch: char) -> anyhow::Result<()> {
        let mut c = ch;
        // https://github.com/google/starlark-go/blob/master/doc/spec.md#lexical-elements
        //
        // Python features not supported:
        // - integer literals of >64 bits of precision
        // - 123L or 123l long suffix
        // - traditional octal: 0755
        // https://docs.python.org/2/reference/lexical_analysis.html#integer-and-long-integer-literals

        let start = self.pos;
        let mut fraction = false;
        let mut exponent = false;
        if c == '.' {
            // dot or start of fraction
            self.read();
            c = self.peek();
            if !c.is_ascii_digit() {
                self.mark_end_token();
                self.token_buf.kind = Token::Dot;
                return Ok(());
            }
            fraction = true
        } else if c == '0' {
            // hex, octal, binary or float
            self.read();
            c = self.peek();

            if c == '.' {
                fraction = true
            } else if c == 'x' || c == 'X' {
                // hex
                self.read();
                c = self.peek();
                if !c.is_ascii_hexdigit() {
                    return Err(anyhow!("{} invalid hex literal", start));
                }
                while c.is_ascii_hexdigit() {
                    self.read();
                    c = self.peek();
                }
            } else if c == 'o' || c == 'O' {
                // octal
                self.read();
                c = self.peek();
                if !c.is_digit(8) {
                    return Err(anyhow!("{} invalid octal literal", start));
                }
                while c.is_digit(8) {
                    self.read();
                    c = self.peek();
                }
            } else if c == 'b' || c == 'B' {
                // binary
                self.read();
                c = self.peek();
                if !c.is_digit(2) {
                    return Err(anyhow!("{} invalid binary literal ", start));
                }
                while c.is_digit(2) {
                    self.read();
                    c = self.peek();
                }
            } else {
                // float (or obsolete octal "0755")
                let mut allzeros = true;
                let mut octal = true;
                while c.is_ascii_digit() {
                    if c != '0' {
                        allzeros = false
                    }
                    if c > '7' {
                        octal = false
                    }
                    self.read();
                    c = self.peek();
                }
                if c == '.' {
                    fraction = true
                } else if c == 'e' || c == 'E' {
                    exponent = true
                } else if octal && !allzeros {
                    self.mark_end_token();
                    return Err(anyhow!(
                        "{}:{} obsolete form of octal literal; use 0o...",
                        self.path.to_string_lossy(),
                        self.pos,
                    ));
                }
            }
        } else {
            // decimal
            while c.is_ascii_digit() {
                self.read();
                c = self.peek();
            }

            if c == '.' {
                fraction = true
            } else if c == 'e' || c == 'E' {
                exponent = true
            }
        }

        if fraction {
            self.read(); // consume '.'
            c = self.peek();
            while c.is_ascii_digit() {
                self.read();
                c = self.peek();
            }

            if c == 'e' || c == 'E' {
                exponent = true
            }
        }

        if exponent {
            self.read(); // consume [eE]
            c = self.peek();
            if c == '+' || c == '-' {
                self.read();
                c = self.peek();
                if !c.is_ascii_digit() {
                    return Err(anyhow!(
                        "{}:{} invalid float literal",
                        self.path.to_string_lossy(),
                        start
                    ));
                }
            }
            while c.is_ascii_digit() {
                self.read();
                c = self.peek();
            }
        }

        self.mark_end_token();
        if fraction || exponent {
            let float_value = self.token.parse::<f64>()?;
            self.token_buf.kind = Token::Float { float_value };
            return Ok(());
        }
        let s = self.token;
        if s.len() > 2 {
            match &s[..2] {
                "0o" | "0O" => {
                    let int_value = i64::from_str_radix(&s[2..], 8)?;
                    self.token_buf.kind = Token::Int {
                        decoded: IntValue::Int(int_value),
                    };
                    return Ok(());
                }
                "0b" | "0B" => {
                    let int_value = i64::from_str_radix(&s[2..], 2)?;
                    self.token_buf.kind = Token::Int {
                        decoded: IntValue::Int(int_value),
                    };
                    return Ok(());
                }
                "0x" | "0X" => match i64::from_str_radix(&s[2..], 16) {
                    Ok(int_value) => {
                        self.token_buf.kind = Token::Int {
                            decoded: IntValue::Int(int_value),
                        };
                        return Ok(());
                    }
                    _ => {
                        let bigint_value = num_bigint::BigInt::parse_bytes(s[2..].as_bytes(), 16)
                            .ok_or(anyhow!(
                            "{}:{} could not parse hex big int",
                            self.path.to_string_lossy(),
                            start
                        ))?;
                        self.token_buf.kind = Token::Int {
                            decoded: IntValue::BigInt(bigint_value),
                        };
                        return Ok(());
                    }
                },

                _ => { /* decimal handled below */ }
            }
        }
        match s.parse::<i64>() {
            Ok(int_value) => {
                self.token_buf.kind = Token::Int {
                    decoded: IntValue::Int(int_value),
                };
            }
            _ => {
                let bigint_value =
                    num_bigint::BigInt::parse_bytes(s.as_bytes(), 10).ok_or(anyhow!(
                        "{}:{} could not parse big int",
                        self.path.to_string_lossy(),
                        start
                    ))?;
                self.token_buf.kind = Token::Int {
                    decoded: IntValue::BigInt(bigint_value),
                };
            }
        }
        Ok(())
    }
}

fn is_ident_start(c: char) -> bool {
    use unicode_categories::UnicodeCategories;
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c == '_' || c.is_letter()
}

fn is_ident(c: char) -> bool {
    c.is_ascii_digit() || is_ident_start(c)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_basic_seq() -> anyhow::Result<()> {
        use Token::*;
        let expected: Vec<Token> = vec![LBrace, LParen, LBrack, RBrack, RParen, RBrace, Eof];
        let mut tokens: Vec<Token> = vec![];
        let bump = Bump::new();
        let mut sc = Scanner::new(&bump, &"test", "{ ( [ ] ) }", false)?;
        while sc.token_buf.kind != Token::Eof {
            tokens.push(sc.next_token()?.kind)
        }
        assert_eq!(tokens, expected);
        Ok(())
    }

    #[test]
    fn test_inputs() {
        let test_cases: Vec<(&str, &str)> = vec![
            ("", "eof"),
            ("", "eof"),
		("123", "123 eof"),
        ("0", "0 eof"),
        ("1", "1 eof"),
        ("0x0a", "10 eof"),
        ("9223372036854775808", "9223372036854775808 eof"),
        ("1.23", "1.23 eof"),
		("x.y", "x . y eof"),
		("chocolate.éclair", "chocolate . éclair eof"),
		("123 \"foo\" hello x.y", "123 \"foo\" hello x . y eof"),
		("print(x)", "print ( x ) eof"),
		("print(x); print(y)", "print ( x ) ; print ( y ) eof"),
        ("/ // /= //= ///=", "/ // /= //= // /= eof"),
		("# hello
print(x)", "print ( x ) eof"),
		("\nprint(\n1\n)\n", "print ( 1 ) newline eof"), // final \n is at toplevel on non-blank line => token
            ("# hello
print(1)
cc_binary(name=\"foo\")
def f(x):
    return x+1
print(1)
", "print ( 1 ) newline cc_binary ( name = \"foo\" ) newline def f ( x ) : newline indent return x + 1 newline outdent print ( 1 ) newline eof"),
("def f(): pass",
    "def f ( ) : pass eof"),
("def f():
    pass
",
    "def f ( ) : newline indent pass newline outdent eof"),
("def f():
    pass
# oops",
    "def f ( ) : newline indent pass newline outdent eof"),
("def f():
    pass \
",
    "def f ( ) : newline indent pass newline outdent eof"),
("def f():
    pass
",
    "def f ( ) : newline indent pass newline outdent eof"),
("pass


pass", "pass newline pass eof"), // consecutive newlines are consolidated
("def f():
    pass
", "def f ( ) : newline indent pass newline outdent eof"),
("def f():
    pass

", "def f ( ) : newline indent pass newline outdent eof"),
("pass", "pass eof"),
		("pass\n", "pass newline eof"),
		("pass\n ", "pass newline eof"),
		("pass\n \n", "pass newline eof"),
		("if x:\n  pass\n ", "if x : newline indent pass newline outdent eof"),
		("x = 1 + \
2", "x = 1 + 2 eof"),
		(r#"x = 'a\nb'"#, r#"x = "a\nb" eof"#),
		(r#"x = r'a\nb'"#, r#"x = "a\\nb" eof"#),
		("x = 'a\\\nb'", r#"x = "ab" eof"#),
		(r#"x = '\''"#, r#"x = "'" eof"#),
		(r#"x = "\"""#, r#"x = "\"" eof"#),
		(r#"x = r'\''"#, r#"x = "\\'" eof"#),
		(r#"x = '''\''''"#, r#"x = "'" eof"#),
		(r#"x = r'''\''''"#, r#"x = "\\'" eof"#),
		(r#"x = ''''a'b'c'''"#, r#"x = "'a'b'c" eof"#),
		("x = '''a\nb'''", r#"x = "a\nb" eof"#),
		("x = '''a\rb'''", r#"x = "a\nb" eof"#),
		("x = '''a\r\nb'''", r#"x = "a\nb" eof"#),
		("x = '''a\n\rb'''", r#"x = "a\n\nb" eof"#),
		("x = r'a\\\nb'", r#"x = "a\\\nb" eof"#),
		("x = r'a\\\rb'", r#"x = "a\\\nb" eof"#),
		("x = r'a\\\r\nb'", r#"x = "a\\\nb" eof"#),
		("a\rb", r#"a newline b eof"#),
		("a\nb", r#"a newline b eof"#),
		("a\r\nb", r#"a newline b eof"#),
		("a\n\nb", r#"a newline b eof"#),
            ];
        for (input, want) in test_cases {
            let mut tokens = "".to_string();
            let bump = Bump::new();
            let sc = Scanner::new(&bump, &"test", input, false);
            assert!(sc.is_ok());
            let mut sc = sc.expect("...");
            while sc.token_buf.kind != Token::Eof {
                if !tokens.is_empty() {
                    tokens.push(' ');
                }
                match sc.next_token() {
                    Ok(tok) => tokens.push_str(&format!("{}", tok.kind)),
                    Err(msg) => assert!(false, "{} {}", msg, input),
                }
            }
            assert_eq!(tokens, want, "{}", input);
        }
    }
}
