use phf::phf_map;

// A Position describes the location of a rune of input.
#[derive(Clone, Debug)]
pub struct Position {
    pub file: Option<String>, // filename (indirect for compactness)
    pub line: usize,          // 1-based line number; 0 if line unknown
    pub col: usize,           // 1-based column (rune) number; 0 if column unknown
}

impl Position {
    pub fn is_valid(&self) -> bool {
        self.file.is_some()
    }
    pub fn filename(&self) -> String {
        self.file.clone().unwrap_or("<invalid>".to_string())
    }
}

// A Comment represents a single # comment.
pub struct Comment {
    pub start: Position,
    pub text: String, // without trailing newline
}

// The pre-lexer only operates on &str and advances index.
#[derive(Copy, Clone, Debug)]
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

struct Scanner<'a> {
    rest: &'a str,
    token: &'a str,
    pos: Position,                 // current input position
    depth: usize,                  // nesting of [ ] { } ( )
    indentstk: Vec<usize>,         // stack of indentation levels
    dents: i8,                     // number of saved INDENT (>0) or OUTDENT (<0) tokens to return
    line_start: bool,              // after NEWLINE; convert spaces to indentation tokens
    keep_comments: bool,           // accumulate comments in slice
    line_comments: Vec<Comment>,   // list of full line comments (if keepComments)
    suffix_comments: Vec<Comment>, // list of suffix comments (if keepComments)
}

struct TokenBuf {
    pos: Position,
    raw: str,
}

const UTF8_CHAR_SELF: u8 = 0x80;

const TRIPLE_QUOTE: &'static str = "'''";
const TRIPLE_DOUBLE_QUOTE: &'static str = "\"\"\"";

impl<'a> Scanner<'a> {
    fn mark_start_token(&mut self, token_buf: &mut TokenBuf) {
        self.token = self.rest;
        self.token_buf.pos = self.pos.clone();
    }

    fn mark_end_token(&mut self, token_buf: &mut TokenBuf) {
        let len = self.rest.len() - self.token.len();
        token_buf.raw = self.token[..len];
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

    fn next_token(&mut self) -> (TokenKind, Position) {
        let mut token_buf = TokenBuf {
            raw: "",
            pos: Position {
                file: None,
                line: 1,
                col: 1,
            },
        }; // TODO
        'start: loop {
            let mut c: char;

            // Deal with leading spaces and indentation.
            let mut blank = false;
            let mut saved_line_start = self.line_start;
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
                            // TODO: ERROR
                            //sc.error(sc.pos, "unindent does not match any outer indentation level")
                        }
                    }
                }
            } // if self.line_start

            // Return saved indentation tokens.
            if self.dents != 0 {
                if self.dents < 0 {
                    self.dents = self.dents + 1;
                    return (TokenKind::Outdent, self.pos.clone());
                } else {
                    self.dents = self.dents - 1;
                    return (TokenKind::Indent, self.pos.clone());
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
                    //sc.endToken(val)
                    if blank {
                        self.line_comments.push(Comment {
                            start: comment_pos,
                            text: "(comment)".to_string(), // TODO
                        })
                    } else {
                        self.suffix_comments.push(Comment {
                            start: comment_pos,
                            text: "(comment)".to_string(), // TODO
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
                self.mark_start_token(&mut token_buf);
                self.read();
                //val.raw = "\n"
                return (TokenKind::Newline, newline_pos);
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
                        self.mark_start_token(&mut token_buf);
                        //val.raw = "\n"
                        return (TokenKind::Newline, self.pos.clone());
                    }
                }

                self.mark_start_token(&mut token_buf);
                self.mark_end_token(&mut token_buf);
                return (TokenKind::Eof, self.pos.clone());
            }

            // line continuation
            if c == '\\' {
                self.read();
                if self.peek() != '\n' {
                    // sc.errorf(sc.pos, "stray backslash in program")
                    // TODO
                }
                self.read();
                break 'start;
            }

            // start of the next token
            self.mark_start_token(&mut token_buf);

            // comma (common case)
            if c == ',' {
                self.read();
                self.mark_end_token(&mut token_buf);
                return (TokenKind::Comma, self.pos.clone());
            }

            // string literal
            if c == '"' || c == '\'' {
                return self.scan_string(c);
            }
        }
        (
            TokenKind::Illegal,
            Position {
                file: None,
                line: 0,
                col: 0,
            },
        )
    }

    pub fn scan_string(&mut self, quote: char, prefix: &str) -> Result<(TokenKind, Position), Error> {
        let start = self.pos;
        let triple = sc.rest.starts_with(if quote == '\'' {
            TRIPLE_QUOTE
        } else {
            TRIPLE_DOUBLE_QUOTE
        });
        sc.read();

        // String literals may contain escaped or unescaped newlines,
        // causing them to span multiple lines (gulps) of REPL input;
        // they are the only such token. Thus we cannot call endToken,
        // as it assumes sc.rest is unchanged since startToken.
        // Instead, buffer the token here.
        let raw: String = "".to_string();

        raw.push_str(prefix);
        // Copy the prefix, e.g. r' or " (see startToken).
        // TODO
        // raw.Write(sc.token[:len(sc.token)-len(sc.rest)])

        if !triple {
            // single-quoted string literal
            loop {
                if self.rest.len() == 0 {
                    return Error(/*val.pos, */"unexpected EOF in string")
                }
                let mut c = self.read();
                //raw.WriteRune(c)
                if c == quote {
                    break;
                }
                if c == '\n' {
                    self.error(val.pos, "unexpected newline in string")
                }
                if c == '\\' {
                    if self.eof() {
                        self.error(val.pos, "unexpected EOF in string")
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

            let mut quoteCount = 0;
            loop {
                if self.eof() {
                    self.error(val.pos, "unexpected EOF in string")
                }
                let mut c = self.read();
                //raw.WriteRune(c)
                if c == '\'' {
                    quoteCount = quoteCount + 1;
                    if quoteCount == 3 {
                        break;
                    }
                } else {
                    quoteCount = 0
                }
                if c == '\\' {
                    if self.eof() {
                        self.error(val.pos, "unexpected EOF in string")
                    }
                    c = self.read();
                    raw.push(c)
                }
            }
        }
        //val.raw = raw.String()

        //s, _, isByte, err := unquote(val.raw)
        //if err != nil {
        //	sc.error(start, err.Error())
        //}
        //val.string = s
        if isByte {
            return TokenKind::Bytes;
        } else {
            return TokenKind::String;
        }
    }
}
