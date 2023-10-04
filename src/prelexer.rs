#[allow(dead_code)]
use anyhow::anyhow;
use phf::phf_map;
use std::{fmt::Display, path::Path};
//use std::fs::read_to_string;

// A Position describes the location of a rune of input.
#[derive(Clone, Debug)]
pub struct Position<'a> {
    pub path: &'a Path, // filename (indirect for compactness)
    pub line: u32,      // 1-based line number; 0 if line unknown
    pub col: u32,       // 1-based column (rune) number; 0 if column unknown
}

impl<'a> Display for Position<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.path.to_string_lossy(),
            self.line,
            self.col
        )
    }
}

impl<'a> Position<'a> {
    pub fn new(path: &'a Path) -> Position<'a> {
        Position {
            path,
            line: 1,
            col: 1,
        }
    }
}

// A Comment represents a single # comment.
pub struct Comment<'a> {
    pub start: Position<'a>,
    pub text: &'a str, // without trailing newline
}

// The pre-lexer only operates on &str and advances index.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Illegal,
    Eof,

    Newline,
    Indent,
    Outdent,

    // Tokens with values
    Ident,  // x
    Int,    // 123
    Float,  // 1.23e45
    String, // "foo" or 'foo' or '''foo''' or r'foo' or r"foo"
    Bytes,  // b"foo", etc

    // Punctuation
    Plus,         // +
    Minus,        // -
    Star,         // *
    Slash,        // /
    SlashSlash,   // //
    Percent,      // %
    Ampersand,    // &
    Pipe,         // |
    Caret,        // ^
    LtLt,         // <<
    GtGt,         // >>
    Tilde,        // ~
    Dot,          // .
    Comma,        // ,
    Eq,           // =
    Semi,         // ;
    Colon,        // :
    LParen,       // (
    RParen,       // )
    LBrack,       // [
    RBrack,       // ]
    LBrace,       // {
    RBrace,       // }
    Lt,           // <
    Gt,           // >
    Ge,           // >=
    Le,           // <=
    EqEq,         // ==
    Neq,          // !=
    PlusEq,       // +=    (keep order consistent with PLUS..GTGT)
    MinusEq,      // -=
    StarEq,       // *=
    SlashEq,      // /=
    SlashSlashEq, // //=
    PercentEq,    // %=
    AmpersandEq,  // &=
    PipeEq,       // |=
    CaretEq,      // ^=
    LtLtEq,       // <<=
    GtGtE,        // >>=
    StarStar,     // **

    // Keywords
    And,
    Break,
    Continue,
    Def,
    Elif,
    Else,
    For,
    If,
    In,
    Lambda,
    Load,
    Not,
    NotIn, // synthesized by parser from NOT IN
    Or,
    Pass,
    Return,
    While,
}

// keywordToken records the special tokens for
// strings that should not be treated as ordinary identifiers.
pub const KEYWORD_TOKEN: phf::Map<&'static str, TokenKind> = phf_map! {
    "and" => TokenKind::And,
    "break" => TokenKind::Break,
    "continue" => TokenKind::Continue,
    "def" => TokenKind::Def,
    "elif" => TokenKind::Elif,
    "else" => TokenKind::Else,
    "for" => TokenKind::For,
    "if" => TokenKind::If,
    "in" => TokenKind::In,
    "lambda" => TokenKind::Lambda,
    "load" => TokenKind::Load,
    "not" => TokenKind::Not,
    "or" => TokenKind::Or,
    "pass" => TokenKind::Pass,
    "return" => TokenKind::Return,
    "while" => TokenKind::While,
    // reserved words,
    "as" => TokenKind::Illegal,
    // "assert" => TokenKind::Illegal, // heavily used by our tests
    "async" => TokenKind::Illegal,
    "await" => TokenKind::Illegal,
    "class" => TokenKind::Illegal,
    "del" => TokenKind::Illegal,
    "except" => TokenKind::Illegal,
    "finally" => TokenKind::Illegal,
    "from" => TokenKind::Illegal,
    "global" => TokenKind::Illegal,
    "import" => TokenKind::Illegal,
    "is" => TokenKind::Illegal,
    "nonlocal" => TokenKind::Illegal,
    "raise" => TokenKind::Illegal,
    "try" => TokenKind::Illegal,
    "with" => TokenKind::Illegal,
    "yield" => TokenKind::Illegal,
};

pub struct Scanner<'a> {
    rest: &'a str,
    token: &'a str,                    //  slice with current token
    pos: Position<'a>,                 // current input position
    depth: usize,                      // nesting of [ ] { } ( )
    indentstk: Vec<usize>,             // stack of indentation levels
    dents: i8,           // number of saved INDENT (>0) or OUTDENT (<0) tokens to return
    line_start: bool,    // after NEWLINE; convert spaces to indentation tokens
    keep_comments: bool, // accumulate comments in slice
    line_comments: Vec<Comment<'a>>, // list of full line comments (if keepComments)
    suffix_comments: Vec<Comment<'a>>, // list of suffix comments (if keepComments)
    token_buf: TokenValue<'a>,
}

#[derive(Clone, Debug)]
pub struct TokenValue<'a> {
    kind: TokenKind,
    pos: Position<'a>, // start position of token
    raw: String,       // raw text of token
    decoded: Option<DecodedValue>,
}

#[derive(Clone, Debug, PartialEq)]
enum DecodedValue {
    Int(i64),                   // decoded int
    BigInt(num_bigint::BigInt), // decoded integers > int64
    Float(f64),                 // decoded float
    String(String),             // decoded string or bytes
}

const UTF8_CHAR_SELF: u8 = 0x80;

const TRIPLE_QUOTE: &'static str = "'''";
const TRIPLE_DOUBLE_QUOTE: &'static str = "\"\"\"";

impl<'a> Scanner<'a> {
    pub fn new<P: AsRef<Path>>(
        path: &'a P,
        data: &'a str,
        keep_comments: bool,
    ) -> anyhow::Result<Scanner<'a>> {
        //let data = read_to_string(path)?;

        //fn new<P: AsRef<Path>>(path: P, keep_comments: bool) -> anyhow::Result<(Box<Scanner<'a>>, String)> {
        //  let data = read_to_string(path)?;
        let pos = Position::new(path.clone().as_ref());
        Ok(Scanner {
            pos: pos.clone(),
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
                kind: TokenKind::Illegal,
                raw: "".to_string(),
                pos: pos.clone(),
                decoded: None,
            },
        })
    }

    // peek returns the next char in the input without consuming it.
    // Newlines in Unix, DOS, or Mac format are treated as one rune, '\n'.
    fn peek(&self) -> char {
        if self.rest.len() == 0 {
            return '\0';
        }
        let c = self.rest.chars().next().unwrap();

        if c == '\r' {
            return '\n';
        }
        c
    }

    fn read(&mut self) -> char {
        if self.rest.len() == 0 {
            return '\0';
        }
        let mut c = self.rest.chars().nth(0).unwrap();
        self.rest = &self.rest[1..];

        if c == '\r' {
            if self.rest.len() > 0 && self.rest.chars().nth(0).unwrap() == '\n' {
                self.rest = &self.rest[1..];
            }
            c = '\n';
        }
        if c == '\n' {
            self.pos.line = self.pos.line + 1;
            self.pos.col = 1;
            return c;
        }
        self.pos.col = self.pos.col + 1;
        c
    }

    fn mark_start_token(&mut self) {
        self.token = self.rest;
        self.token_buf.pos = self.pos.clone();
    }

    fn mark_end_token(&mut self) {
        let len = self.token.len() - self.rest.len();
        self.token = &self.token[..len];
        // TODO: only create the string when necessary.
        self.token_buf.raw = self.token.to_string()
    }

    // nextToken is called by the parser to obtain the next input token.
    // It returns the token value and sets val to the data associated with
    // the token.
    //'
    // For all our input tokens, the associated data is token_buf.pos (the
    // position where the token begins), token_buf.raw (the input string
    // corresponding to the token).  For string and int tokens, the decoded
    // field additionally contains the token's interpreted value.
    pub fn next_token(&mut self) -> anyhow::Result<TokenValue<'a>> {
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
                        col = col + 1;
                        self.read();
                    } else if c == '\t' {
                        let tab = 8;
                        col += (tab - (self.pos.col - 1) % tab) as usize;
                        self.read();
                    } else {
                        break;
                    }
                }

                // The third clause matches EOF.
                if c == '#' || c == '\n' || c == '\0' {
                    blank = true
                }

                // Compute indentation level for non-blank lines not
                // inside an expression.  This is not the common case.
                if !blank && self.depth == 0 {
                    let cur = self.indentstk.last().copied().unwrap();
                    if col > cur {
                        // indent
                        self.dents = self.dents + 1;
                        self.indentstk.push(col)
                    } else if col < cur {
                        // outdent(s)
                        while self.indentstk.len() > 0 && col < *self.indentstk.last().unwrap() {
                            self.dents = self.dents - 1;
                            self.indentstk.pop();
                        }
                        if col != *self.indentstk.last().unwrap() {
                            return Err(anyhow!(
                                "{:?} unindent does not match any outer indentation level",
                                self.pos
                            ));
                        }
                    }
                }
            } // if self.line_start

            // Return saved indentation tokens.
            if self.dents != 0 {
                if self.dents < 0 {
                    self.dents = self.dents + 1;
                    self.token_buf.kind = TokenKind::Outdent;
                    self.token_buf.pos = self.pos.clone();
                    return Ok(self.token_buf.clone());
                } else {
                    self.dents = self.dents - 1;
                    self.token_buf.kind = TokenKind::Indent;
                    self.token_buf.pos = self.pos.clone();
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
                let comment_pos = self.pos.clone();

                // Consume up to newline (included).
                while c != '\0' && c != '\n' {
                    self.read();
                    c = self.peek()
                }
                if self.keep_comments {
                    self.mark_end_token();
                    if blank {
                        self.line_comments.push(Comment {
                            start: comment_pos,
                            text: &"(comment)", // TODO
                        })
                    } else {
                        self.suffix_comments.push(Comment {
                            start: comment_pos,
                            text: &"(comment)", // TODO
                        })
                    }
                }
            }

            // newline
            if c == '\n' {
                let newline_pos = self.pos.clone();
                self.line_start = true;

                // Ignore newlines within expressions (common case).
                if self.depth > 0 {
                    self.read();
                    break 'start;
                }

                // Ignore blank lines.
                if blank && self.indentstk.len() > 1 {
                    self.dents = 1 - self.indentstk.len() as i8;
                    self.indentstk.pop();
                    break 'start;
                }

                // At top-level (not in an expression).
                self.mark_start_token();
                self.read();
                self.token_buf.kind = TokenKind::Newline;
                self.token_buf.pos = newline_pos;
                self.token_buf.raw = "\n".to_string();
                return Ok(self.token_buf.clone());
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
                        self.token_buf.kind = TokenKind::Newline;
                        self.token_buf.pos = self.pos.clone();
                        self.token_buf.raw = "\n".to_string();
                        return Ok(self.token_buf.clone());
                    }
                }

                self.mark_start_token();
                self.mark_end_token();
                self.token_buf.kind = TokenKind::Eof;
                self.token_buf.pos = self.pos.clone();
                return Ok(self.token_buf.clone());
            }

            // line continuation
            if c == '\\' {
                self.read();
                if self.peek() != '\n' {
                    // self.errorf(self.pos, "stray backslash in program")
                    // TODO
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
                self.token_buf.kind = TokenKind::Comma;
                self.token_buf.pos = self.pos.clone();
                return Ok(self.token_buf.clone());
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
                match KEYWORD_TOKEN.get(&self.token_buf.raw) {
                    Some(k) => self.token_buf.kind = *k,
                    _ => self.token_buf.kind = TokenKind::Ident,
                }
                return Ok(self.token_buf.clone());
            }

            // brackets
            match c {
                '[' | '(' | '{' => {
                    self.depth = self.depth + 1;
                    self.read();
                    self.mark_end_token();

                    match c {
                        '[' => {
                            self.token_buf.kind = TokenKind::LBrack;
                            return Ok(self.token_buf.clone());
                        }
                        '(' => {
                            self.token_buf.kind = TokenKind::LParen;
                            return Ok(self.token_buf.clone());
                        }
                        '{' => {
                            self.token_buf.kind = TokenKind::LBrace;
                            return Ok(self.token_buf.clone());
                        }
                        _ => unreachable!(),
                    }
                }
                ']' | ')' | '}' => {
                    if self.depth == 0 {
                        return Err(anyhow!("{} unexpected '{}'", self.pos, c));
                    } else {
                        self.depth = self.depth - 1
                    }
                    self.read();
                    self.mark_end_token();
                    match c {
                        ']' => {
                            self.token_buf.kind = TokenKind::RBrack;
                            return Ok(self.token_buf.clone());
                        }
                        ')' => {
                            self.token_buf.kind = TokenKind::RParen;
                            return Ok(self.token_buf.clone());
                        }
                        '}' => {
                            self.token_buf.kind = TokenKind::RBrace;
                            return Ok(self.token_buf.clone());
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

            break;
        }
        return Ok(self.token_buf.clone());
    }

    pub fn scan_string(&mut self, quote: char) -> anyhow::Result<TokenValue<'a>> {
        //let start = self.pos.clone();
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
                if self.rest.len() == 0 {
                    return Err(anyhow!("{:?} unexpected EOF in string", self.pos));
                }
                let mut c = self.read();
                //raw.WriteRune(c)
                if c == quote {
                    break;
                }
                if c == '\n' {
                    return Err(anyhow!("{:?} unexpected newline in string", self.pos));
                }
                if c == '\\' {
                    if self.rest.len() == 0 {
                        return Err(anyhow!("{:?} unexpected EOF in string", self.pos));
                    }
                    c = self.read();
                    raw.push(c)
                }
            }
        } else {
            // triple-quoted string literal
            self.read();
            raw.push('\'');
            self.read();
            raw.push('\'');

            let mut quote_count = 0;
            loop {
                if self.rest.len() == 0 {
                    return Err(anyhow!("{:?} unexpected EOF in string", self.pos));
                }
                let mut c = self.read();
                raw.push(c);
                if c == '\'' {
                    quote_count = quote_count + 1;
                    if quote_count == 3 {
                        break;
                    }
                } else {
                    quote_count = 0
                }
                if c == '\\' {
                    if self.rest.len() == 0 {
                        return Err(anyhow!("{:?} unexpected EOF in string", self.pos));
                    }
                    c = self.read();
                    raw.push(c)
                }
            }
        }
        self.token_buf.raw = raw.to_string();
        let (s, is_byte) = crate::quote::unquote(&raw)?;
        self.token_buf.decoded = Some(DecodedValue::String(s.to_string()));
        self.token_buf.kind = if is_byte {
            TokenKind::Bytes
        } else {
            TokenKind::String
        };
        return Ok(self.token_buf.clone());
    }

    pub fn scan_number(&mut self, ch: char) -> anyhow::Result<TokenValue<'a>> {
        let mut c = ch;
        // https://github.com/google/starlark-go/blob/master/doc/spec.md#lexical-elements
        //
        // Python features not supported:
        // - integer literals of >64 bits of precision
        // - 123L or 123l long suffix
        // - traditional octal: 0755
        // https://docs.python.org/2/reference/lexical_analysis.html#integer-and-long-integer-literals

        let start = self.pos.clone();
        let mut fraction = false;
        let mut exponent = false;
        if c == '.' {
            // dot or start of fraction
            self.read();
            c = self.peek();
            if !c.is_ascii_digit() {
                self.mark_end_token();
                self.token_buf.kind = TokenKind::Dot;
                return Ok(self.token_buf.clone());
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
                if !c.is_digit(16) {
                    return Err(anyhow!("{} invalid hex literal", start));
                }
                while c.is_digit(16) {
                    self.read();
                    c = self.peek();
                }
            } else if c == 'o' || c == 'O' {
                // octal
                self.read();
                c = self.peek();
                if !c.is_digit(8) {
                    return Err(anyhow!("{} invalid octal literal", self.pos));
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
                    return Err(anyhow!("{} invalid binary literal ", self.pos));
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
                        "{} obsolete form of octal literal; use 0o{}",
                        self.pos,
                        &self.token_buf.raw[1..]
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
                    return Err(anyhow!("{} invalid float literal", self.pos));
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
            self.token_buf.kind = TokenKind::Float;
            self.token_buf.decoded = Some(DecodedValue::Float(float_value));
            return Ok(self.token_buf.clone());
        } else {
            let s = self.token;
            'ints: {
                if s.len() > 2 {
                    let prefix = &s[..2];
                    if prefix == "0o" || prefix == "0O" {
                        let int_value = i64::from_str_radix(&s[2..], 8)?;
                        self.token_buf.decoded = Some(DecodedValue::Int(int_value));
                        break 'ints;
                    } else if prefix == "0b" || prefix == "0B" {
                        let int_value = i64::from_str_radix(&s[2..], 2)?;
                        self.token_buf.decoded = Some(DecodedValue::Int(int_value));
                        break 'ints;
                    }
                }
                match s.parse::<i64>() {
                    Ok(int_value) => {
                        self.token_buf.decoded = Some(DecodedValue::Int(int_value));
                    }
                    Err(_) => {
                        let bigint_value = num_bigint::BigInt::parse_bytes(&s.as_bytes(), 10)
                            .ok_or(anyhow!("could not parse big int"))?;
                        self.token_buf.decoded = Some(DecodedValue::BigInt(bigint_value));
                    }
                }
            }
            self.token_buf.kind = TokenKind::Int;
            return Ok(self.token_buf.clone());
        }
    }
}

fn is_ident_start(c: char) -> bool {
    use unicode_categories::UnicodeCategories;
    'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_' || c.is_letter()
}

fn is_ident(c: char) -> bool {
    c.is_ascii_digit() || is_ident_start(c)
}

#[cfg(test)]
mod tests {

    use super::*;
    use float_cmp::approx_eq;
    use num_bigint::BigInt;

    fn approx_float(tok: &TokenValue, expected: f64) -> bool {
        match tok.decoded {
            Some(DecodedValue::Float(float_val)) => {
                approx_eq!(f64, float_val, expected, ulps = 2)
            }
            _ => false,
        }
    }

    fn eq_bigint(tok: &TokenValue, expected: &str) -> bool {
        match &tok.decoded {
            Some(DecodedValue::BigInt(bigint_val)) => {
                *bigint_val == BigInt::parse_bytes(expected.as_bytes(), 10).unwrap()
            }
            _ => false,
        }
    }

    #[test]
    fn test_basic_scan() -> anyhow::Result<()> {
        let cases: phf::Map<&'static str, (TokenKind, fn(TokenValue) -> bool)> = phf_map! [
        "a" => (TokenKind::Ident, (|tok| {tok.raw == "a"}) ),
        "abc" => (TokenKind::Ident, (|tok| {tok.raw == "abc"}) ),
        "0" => (TokenKind::Int, (|tok| {tok.decoded == Some(DecodedValue::Int(0))}) ),
        "1" => (TokenKind::Int, (|tok| {tok.decoded == Some(DecodedValue::Int(1))}) ),
        "9223372036854775808" => (TokenKind::Int, (|tok| {eq_bigint(&tok, "9223372036854775808")})),
        "1.23" => (TokenKind::Float, (|tok| {approx_float(&tok, 1.23)})),
        ];
        for (k, v) in cases.into_iter() {
            let mut sc = Scanner::new(&"test", k, false)?;
            match sc.next_token() {
                Ok(tok) => {
                    assert_eq!(tok.kind, v.0);
                    assert!(v.1(tok));
                }
                _ => assert!(false),
            };
        }
        Ok(())
    }
}
