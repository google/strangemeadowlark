#[allow(dead_code)]
use anyhow::anyhow;
use phf::phf_map;
use std::{fmt::Display, path::Path, rc::Rc};
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
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Illegal,
    Eof,

    Newline,
    Indent,
    Outdent,

    // Tokens with values
    Ident { name: String },        // x
    Int { decoded: DecodedValue }, // 123
    Float { float_value: f64 },    // 1.23e45
    String { decoded: String },    // "foo" or 'foo' or '''foo''' or r'foo' or r"foo"
    Bytes { decoded: Vec<u8> },    // b"foo", etc

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
    GtGtEq,       // >>=
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

impl Eq for Token {}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        macro_rules! token_text {
            ( $fstr:expr ) => {
                write!(f, $fstr)
            };
            ( $fstr:expr, $( $x:expr ),* ) => {
                write!(f, $fstr, ($($x),+))
            };
        }

        match self {
            Token::Illegal => token_text!["illegal"],
            Token::Eof => token_text!["eof"],
            Token::Newline => token_text!["newline"],
            Token::Indent => token_text!["indent"],
            Token::Outdent => token_text!["outdent"],
            Token::Ident { name } => token_text!["{}", name],
            Token::Int {
                decoded: DecodedValue::Int(int_value),
            } => token_text!["{}", int_value],
            Token::Int {
                decoded: DecodedValue::BigInt(bigint_value),
            } => token_text!["{}", bigint_value],
            Token::Float { float_value } => token_text!["{}", float_value],
            Token::String { decoded } => token_text!["{}", crate::quote::quote(decoded)],
            Token::Bytes { decoded } => token_text!["{:?}", decoded],
            Token::Plus => token_text!["+"],
            Token::Minus => token_text!["-"],
            Token::Star => token_text!["*"],
            Token::Slash => token_text!["/"],
            Token::SlashSlash => token_text!["//"],
            Token::Percent => token_text!["%"],
            Token::Ampersand => token_text!["&"],
            Token::Pipe => token_text!["|"],
            Token::Caret => token_text!["^"],
            Token::LtLt => token_text!["<<"],
            Token::GtGt => token_text![">>"],
            Token::Tilde => token_text!["~"],
            Token::Dot => token_text!["."],
            Token::Comma => token_text![","],
            Token::Eq => token_text!["="],
            Token::Semi => token_text![";"],
            Token::Colon => token_text![":"],
            Token::LParen => token_text!["("],
            Token::RParen => token_text![")"],
            Token::LBrack => token_text!["["],
            Token::RBrack => token_text!["]"],
            Token::LBrace => token_text!["{{"],
            Token::RBrace => token_text!["}}"],
            Token::Lt => token_text!["<"],
            Token::Gt => token_text![">"],
            Token::Ge => token_text![">="],
            Token::Le => token_text!["<="],
            Token::EqEq => token_text!["=="],
            Token::Neq => token_text!["!="],
            Token::PlusEq => token_text!["+="],
            Token::MinusEq => token_text!["-="],
            Token::StarEq => token_text!["*="],
            Token::SlashEq => token_text!["/="],
            Token::SlashSlashEq => token_text!["//="],
            Token::PercentEq => token_text!["%="],
            Token::AmpersandEq => token_text!["&="],
            Token::PipeEq => token_text!["|="],
            Token::CaretEq => token_text!["^="],
            Token::LtLtEq => token_text!["<<="],
            Token::GtGtEq => token_text![">>="],
            Token::StarStar => token_text!["**"],
            Token::And => token_text!["and"],
            Token::Break => token_text!["break"],
            Token::Continue => token_text!["continue"],
            Token::Def => token_text!["def"],
            Token::Elif => token_text!["elif"],
            Token::Else => token_text!["else"],
            Token::For => token_text!["for"],
            Token::If => token_text!["if"],
            Token::In => token_text!["in"],
            Token::Lambda => token_text!["lambda"],
            Token::Load => token_text!["load"],
            Token::Not => token_text!["not"],
            Token::NotIn => token_text!["not in"],
            Token::Or => token_text!["or"],
            Token::Pass => token_text!["pass"],
            Token::Return => token_text!["return"],
            Token::While => token_text!["while"],
        }
    }
}

// keywordToken records the special tokens for
// strings that should not be treated as ordinary identifiers.
pub const KEYWORD_TOKEN: phf::Map<&'static str, Token> = phf_map! {
    "and" => Token::And,
    "break" => Token::Break,
    "continue" => Token::Continue,
    "def" => Token::Def,
    "elif" => Token::Elif,
    "else" => Token::Else,
    "for" => Token::For,
    "if" => Token::If,
    "in" => Token::In,
    "lambda" => Token::Lambda,
    "load" => Token::Load,
    "not" => Token::Not,
    "or" => Token::Or,
    "pass" => Token::Pass,
    "return" => Token::Return,
    "while" => Token::While,
    // reserved words,
    "as" => Token::Illegal,
    // "assert" => Token::Illegal, // heavily used by our tests
    "async" => Token::Illegal,
    "await" => Token::Illegal,
    "class" => Token::Illegal,
    "del" => Token::Illegal,
    "except" => Token::Illegal,
    "finally" => Token::Illegal,
    "from" => Token::Illegal,
    "global" => Token::Illegal,
    "import" => Token::Illegal,
    "is" => Token::Illegal,
    "nonlocal" => Token::Illegal,
    "raise" => Token::Illegal,
    "try" => Token::Illegal,
    "with" => Token::Illegal,
    "yield" => Token::Illegal,
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
    kind: Token,
    pos: Position<'a>, // start position of token
    raw: String,       // raw text of token
    decoded: Option<DecodedValue>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DecodedValue {
    Int(i64),                   // decoded int
    BigInt(num_bigint::BigInt), // decoded integers > int64
}

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
                kind: Token::Illegal,
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
    #[allow(dead_code)]
    pub fn next_token(&mut self) -> anyhow::Result<TokenValue<'a>> {
        self.next_token_internal().map(|()| self.token_buf.clone())
    }

    fn next_token_internal(&mut self) -> anyhow::Result<()> {
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
                    println!["hello comment"];
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
                    println!["goodbye comment --{}--", &self.token[..(self.token.len() as usize-self.rest.len() as usize) as usize]];
                    println!["char '{}'", c.escape_default()];
                }

                // newline
                if c == '\n' {
                    println!["hello newline"];
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
        println!("raw --{}--", raw);
        if !triple {
            // single-quoted string literal
            loop {
                if self.rest.len() == 0 {
                    return Err(anyhow!("{:?} unexpected EOF in string", self.pos));
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
            self.token_buf.kind = Token::Float { float_value };
            return Ok(());
        } else {
            let s = self.token;
            'ints: {
                if s.len() > 2 {
                    let prefix = &s[..2];
                    if prefix == "0o" || prefix == "0O" {
                        let int_value = i64::from_str_radix(&s[2..], 8)?;
                        self.token_buf.kind = Token::Int {
                            decoded: DecodedValue::Int(int_value),
                        };
                        break 'ints;
                    } else if prefix == "0b" || prefix == "0B" {
                        let int_value = i64::from_str_radix(&s[2..], 2)?;
                        self.token_buf.kind = Token::Int {
                            decoded: DecodedValue::Int(int_value),
                        };
                        break 'ints;
                    }
                }
                match s.parse::<i64>() {
                    Ok(int_value) => {
                        self.token_buf.kind = Token::Int {
                            decoded: DecodedValue::Int(int_value),
                        };
                    }
                    Err(_) => {
                        let bigint_value = num_bigint::BigInt::parse_bytes(&s.as_bytes(), 10)
                            .ok_or(anyhow!("could not parse big int"))?;
                        self.token_buf.kind = Token::Int {
                            decoded: DecodedValue::BigInt(bigint_value),
                        };
                    }
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
    use float_cmp::approx_eq;
    use num_bigint::BigInt;
    /*
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
           use Token::*;
           let cases: phf::Map<&'static str, (Token, fn(TokenValue) -> bool)> = phf_map! [
           //"a" => (Ident, (|tok| {tok.raw == "a"}) ),
           //"abc" => (Ident, (|tok| {tok.raw == "abc"}) ),
           //"_C4FE" => (Ident, (|tok| {tok.raw == "_C4FE"}) ),
           "0" => (Int, (|tok| {tok.decoded == Some(DecodedValue::Int(0))}) ),
           "1" => (Int, (|tok| {tok.decoded == Some(DecodedValue::Int(1))}) ),
           "9223372036854775808" => (Int, (|tok| {eq_bigint(&tok, "9223372036854775808")})),
           "1.23" => (Float, (|tok| {approx_float(&tok, 1.23)})),
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
    */

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
    fn test_indent_outdent() {
        //let expected: Vec<Token> = vec![
        //    Newline, Indent, LBrace, LParen, RParen, RBrace, Newline, Outdent, Eof,
        //];
        let expected = "print ( 1 ) newline cc_binary ( name = \"foo\" ) newline def f ( x ) : newline indent return x + 1 newline outdent print ( 1 ) newline eof";
        let mut tokens = String::new();
        let sc = Scanner::new(
            &"test",
            "# hello
print(1)
cc_binary(name=\"foo\")
def f(x):
    return x+1
print(1)
",
            false,
        );
        assert!(sc.is_ok());
        let mut sc = sc.expect("...");
        while sc.token_buf.kind != Token::Eof {
            if !tokens.is_empty() {
                tokens.push(' ');
            }
            match sc.next_token() {
                Ok(tok) => tokens.push_str(&format!("{}", tok.kind)),
                Err(msg) => assert!(false, "{}", msg),
            }
        }
        println!("tokens {:?}", tokens);
        assert_eq!(tokens, expected);
    }
}
