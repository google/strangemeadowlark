use crate::token::{IntValue, Token, KEYWORD_TOKEN};
#[allow(dead_code)]
use anyhow::anyhow;
use std::{fmt::Display, path::Path, rc::Rc};

// A Position describes the location of a rune of input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Position {
    pub path: Rc<String>,
    //pub path: &'a Path, // path to file (only for error messages)
    pub line: u32, // 1-based line number; 0 if line unknown
    pub col: u32,  // 1-based column (rune) number; 0 if column unknown
}

impl<'a> Display for Position {
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
    pub fn new(path: &Rc<String>) -> Position {
        Position {
            path: Rc::clone(path),
            line: 1,
            col: 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
// A Comment represents a single # comment.
pub struct Comment {
    pub start: Position,
    pub text: String, // without trailing newline
}

pub struct Scanner<'a> {
    rest: &'a str,
    token: &'a str,                //  slice with current token
    pub pos: Position,             // current input position
    depth: usize,                  // nesting of [ ] { } ( )
    indentstk: Vec<usize>,         // stack of indentation levels
    dents: i8,                     // number of saved INDENT (>0) or OUTDENT (<0) tokens to return
    line_start: bool,              // after NEWLINE; convert spaces to indentation tokens
    keep_comments: bool,           // accumulate comments in slice
    pub line_comments: Vec<Comment>,   // list of full line comments (if keepComments)
    pub suffix_comments: Vec<Comment>, // list of suffix comments (if keepComments)
    pub token_buf: TokenValue,
}

#[derive(Clone, Debug)]
pub struct TokenValue {
    pub kind: Token,
    pub pos: Position, // start position of token
    pub raw: String,   // raw text of token
}

const TRIPLE_QUOTE: &'static str = "'''";
const TRIPLE_DOUBLE_QUOTE: &'static str = "\"\"\"";

impl<'a> Scanner<'a> {
    // The scanner operates on &str, advancing one char at a time.
    // path is only used in error messages.
    #[allow(dead_code)]
    pub fn new<P: AsRef<Path>>(
        path: &'a P,
        data: &'a str,
        keep_comments: bool,
    ) -> anyhow::Result<Scanner<'a>> {
        let path_str = path
            .as_ref()
            .to_str()
            .ok_or(anyhow!("not utf"))?
            .to_string();
        let path = Rc::new(path_str);
        //let pos = Position::new();//path.as_ref());
        Ok(Scanner {
            pos: Position::new(&path),
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
                raw: "".to_string(),
                pos: Position::new(&path),
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
        self.rest = &self.rest[c.len_utf8()..];

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
    #[allow(dead_code)]
    pub fn next_token(&mut self) -> anyhow::Result<TokenValue> {
        self.next_token_internal().map(|()| self.token_buf.clone())
    }

    pub fn next_token_internal(&mut self) -> anyhow::Result<()> {
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

                    // The third clause matches eof.
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
                            while self.indentstk.len() > 0 && col < *self.indentstk.last().unwrap()
                            {
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
                        self.token_buf.kind = Token::Outdent;
                        self.token_buf.pos = self.pos.clone();
                        return Ok(());
                    } else {
                        self.dents = self.dents - 1;
                        self.token_buf.kind = Token::Indent;
                        self.token_buf.pos = self.pos.clone();
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
                                text: self.token_buf.raw.clone(),
                            })
                        } else {
                            self.suffix_comments.push(Comment {
                                start: comment_pos,
                                text: self.token_buf.raw.clone(),
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
                    if blank {
                        self.read();
                        break 'start;
                    }
                    // At top-level (not in an expression).
                    self.mark_start_token();
                    self.read();
                    self.token_buf.kind = Token::Newline;
                    self.token_buf.pos = newline_pos;
                    self.token_buf.raw = "\n".to_string();
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
                            self.token_buf.raw = "\n".to_string();
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
                        return Err(anyhow!("{} stray backslash in program", self.pos));
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
                    self.token_buf.pos = self.pos.clone();
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
                    match KEYWORD_TOKEN.get(&self.token_buf.raw) {
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
                        self.depth = self.depth + 1;
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
                            return Err(anyhow!("{} unexpected '{}'", self.pos, c));
                        } else {
                            self.depth = self.depth - 1
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
                        let start = self.pos.clone();
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
                            '!' => return Err(anyhow!("{} unexpected input character '!'", start)),
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
                    _ => return Err(anyhow!("{} unexpected input character {}", self.pos, c)),
                }
            }
        }
    }

    fn scan_string(&mut self, quote: char) -> anyhow::Result<()> {
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
                    return Err(anyhow!("{:?} unexpected eof in string", self.pos));
                }
                let mut c = self.read();
                raw.push(c);
                if c == quote {
                    break;
                }
                if c == '\n' {
                    return Err(anyhow!("{:?} unexpected newline in string", self.pos));
                }
                if c == '\\' {
                    if self.rest.len() == 0 {
                        return Err(anyhow!("{:?} unexpected eof in string", self.pos));
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
                    return Err(anyhow!("{:?} unexpected eof in string", self.pos));
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
                        return Err(anyhow!("{:?} unexpected eof in string", self.pos));
                    }
                    c = self.read();
                    raw.push(c)
                }
            }
        }
        self.token_buf.raw = raw.to_string();
        match crate::quote::unquote(&raw) {
            Ok(crate::quote::DecodedSequence::String(decoded)) => {
                self.token_buf.kind = Token::String { decoded }
            }
            Ok(crate::quote::DecodedSequence::Bytes(decoded)) => {
                self.token_buf.kind = Token::Bytes { decoded }
            }
            Err(e) => return Err(anyhow!("error unquoting: {}", e)),
        }

        //self.token_buf.decoded = Some(DecodedValue::String(s.to_string()));
        //self.token_buf.kind = if is_byte {  } else { Token::String{decoded: s} };
        return Ok(());
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

        let start = self.pos.clone();
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
                    return Err(anyhow!("{} invalid float literal", start));
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
        } else {
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
                            let bigint_value =
                                num_bigint::BigInt::parse_bytes(&s[2..].as_bytes(), 16)
                                    .ok_or(anyhow!("{} could not parse hex big int", start))?;
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
                    let bigint_value = num_bigint::BigInt::parse_bytes(&s.as_bytes(), 10)
                        .ok_or(anyhow!("{} could not parse big int", start))?;
                    self.token_buf.kind = Token::Int {
                        decoded: IntValue::BigInt(bigint_value),
                    };
                }
            }
            return Ok(());
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

    #[test]
    fn test_basic_seq() -> anyhow::Result<()> {
        use Token::*;
        let expected: Vec<Token> = vec![LBrace, LParen, LBrack, RBrack, RParen, RBrace, Eof];
        let mut tokens: Vec<Token> = vec![];
        let mut sc = Scanner::new(&"test", "{ ( [ ] ) }", false)?;
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
            let sc = Scanner::new(&"test", input, false);
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
