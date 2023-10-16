use phf::phf_map;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntValue {
    Int(i64),                   // decoded int
    BigInt(num_bigint::BigInt), // decoded integers > int64
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Illegal,
    Eof,

    Newline,
    Indent,
    Outdent,

    // Tokens with values
    Ident { name: String },     // x
    Int { decoded: IntValue },  // 123
    Float { float_value: f64 }, // 1.23e45
    String { decoded: String }, // "foo" or 'foo' or '''foo''' or r'foo' or r"foo"
    Bytes { decoded: Vec<u8> }, // b"foo", etc

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

pub const SUP_PREC: usize = 10;

impl Token {
    // precedence maps each operator to its precedence (0-7), or -1 for other tokens.
    // preclevels groups operators of equal precedence.
    // Comparisons are nonassociative; other binary operators associate to the left.
    // Unary MINUS, unary PLUS, and TILDE have higher precedence so are handled in parsePrimary.
    // See https://github.com/google/starlark-go/blob/master/doc/spec.md#binary-operators
    pub fn precedence(&self) -> Option<usize> {
        let prec = match self {
            Token::Or => 0,
            Token::And => 1,
            Token::Not => 2,
            Token::EqEq => 3,
            Token::Neq => 3,
            Token::Lt => 3,
            Token::Gt => 3,
            Token::Le => 3,
            Token::Ge => 3,
            Token::In => 3,
            Token::NotIn => 3,
            Token::Pipe => 4,
            Token::Caret => 5,
            Token::Ampersand => 6,
            Token::LtLt => 7,
            Token::GtGt => 7,
            Token::Minus => 8,
            Token::Plus => 8,
            Token::Star => 9,
            Token::Percent => 9,
            Token::Slash => 9,
            Token::SlashSlash => 9,
            _ => return None,
        };
        return Some(prec);
    }

    fn phf_hash<H: std::hash::Hasher>(&self, state: &mut H) {
        use std::hash::Hash;
        std::mem::discriminant(self).hash(state);
    }
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
                decoded: IntValue::Int(int_value),
            } => token_text!["{}", int_value],
            Token::Int {
                decoded: IntValue::BigInt(bigint_value),
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
