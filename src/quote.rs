#[allow(dead_code)]
use anyhow::anyhow;
use phf::phf_map;

// unesc maps single-letter chars following \ to their actual values.
static UNESC: phf::Map<char, char> = phf_map! {
    'a' =>  '\x07',
    'b' =>  '\x08',
    'f' =>  '\x0C',
    'n' =>  '\x0A',
    'r' =>  '\x0D',
    't' =>  '\x09',
    'v' =>  '\x0B',
    '\\' => '\\',
    '\'' => '\'',
    '"' =>  '"',
};

/*
// esc maps escape-worthy bytes to the char that should follow \.
static esc: phf::Map<char, char> = phf_map! {
    '\x07' => 'a',
    '\x08' => 'b',
    '\x0C' => 'f',
    '\x0A' => 'n',
    '\x0D' => 'r',
    '\x09' => 't',
    '\x0B' => 'v',
    '\\' => '\\',
    '\'' => '\'',
    '"' =>  '"',
};
 */

// unquote unquotes the quoted string, returning the actual
// string value, whether the original was triple-quoted,
// whether it was a byte string, and an error describing invalid input.
pub fn unquote(quoted_str: &str) -> anyhow::Result<(String, bool)> {
    let mut quoted = quoted_str;
    let mut is_byte = false;
    // Check for raw prefix: means don't interpret the inner \.
    let mut raw = false;
    if quoted.starts_with("r") {
        raw = true;
        quoted = &quoted[1..]
    }
    // Check for bytes prefix.
    if quoted.starts_with("b") {
        is_byte = true;
        quoted = &quoted[1..]
    }

    if quoted.len() < 2 {
        return Err(anyhow!("string literal too short"));
    }

    let first = quoted.chars().nth(0).unwrap();
    if first != '"' && first != '\'' || first != quoted.chars().last().unwrap() {
        return Err(anyhow!("string literal has invalid quotes"));
    }

    // Check for triple quoted string.
    let quote = quoted.chars().nth(0).unwrap();
    if quoted.len() >= 6
        && quoted.chars().nth(1).unwrap() == quote
        && quoted.chars().nth(2).unwrap() == quote
        && quoted[..3] == quoted[quoted.len() - 3..]
    {
        quoted = &quoted[3..quoted.len() - 3]
    } else {
        quoted = &quoted[1..quoted.len() - 1]
    }

    // Now quoted is the quoted data, but no quotes.
    // If we're in raw mode or there are no escapes or
    // carriage returns, we're done.
    let unquote_chars = if raw { "\r" } else { "\\\r" };
    if !quoted.chars().any(|x| unquote_chars.contains(x)) {
        return Ok((quoted.to_string(), false));
    }

    // Otherwise process quoted string.
    // Each iteration processes one escape sequence along with the
    // plain text leading up to it.
    let mut buf = "".to_string();
    loop {
        // Remove prefix before escape sequence.
        match quoted.chars().position(|c| unquote_chars.contains(c)) {
            Some(i) => {
                buf.push_str(&quoted[..i]);
                quoted = &quoted[i..];
            }
            _ => {
                buf.push_str(quoted);
                break;
            }
        }

        // Process carriage return.
        if quoted.chars().nth(0).unwrap() == '\r' {
            buf.push('\n');
            quoted = if quoted.len() > 1 && quoted.chars().nth(1).unwrap() == '\n' {
                &quoted[2..]
            } else {
                &quoted[1..]
            };
            continue;
        }

        // Process escape sequence.
        if quoted.len() == 1 {
            return Err(anyhow!("truncated escape sequence \\"));
        }

        match quoted.chars().nth(1) {
            Some('\n') =>
            // Ignore the escape and the line break.
            {
                quoted = &quoted[2..]
            }

            Some('a' | 'b' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '\'' | '"') => {
                // One-char escape.
                // Escapes are allowed for both kinds of quotation
                // mark, not just the kind in use.
                buf.push(UNESC[&quoted.chars().nth(1).unwrap()]);
                quoted = &quoted[2..]
            }

            Some('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7') => {
                // Octal escape, up to 3 digits, \OOO.
                let mut n = quoted.chars().nth(1).unwrap().to_digit(8).unwrap();
                quoted = &quoted[2..];
                for i in 1..3 {
                    if quoted.len() == 0
                        || quoted.chars().nth(i).unwrap() < '0'
                        || '7' < quoted.chars().nth(0).unwrap()
                    {
                        break;
                    }
                    n = n * 8 + quoted.chars().nth(0).unwrap().to_digit(8).unwrap();
                    quoted = &quoted[1..];
                }
                if !is_byte && n > 127 {
                    return Err(anyhow!("non-ASCII octal escape \\{:o} (use \\u{:04x} for the UTF-8 encoding of U+{:04x})", n, n, n));
                }
                if n >= 256 {
                    // NOTE: Python silently discards the high bit,
                    // so that '\541' == '\141' == 'a'.
                    // Let's see if we can avoid doing that in BUILD files.
                    return Err(anyhow!("invalid escape sequence \\{:03}o", n));
                }
                buf.push(char::from_u32(n).unwrap())
            }
            Some('x') => {
                // Hexadecimal escape, exactly 2 digits, \xXX. [0-127]
                if quoted.len() < 4 {
                    return Err(anyhow!("truncated escape sequence {}", quoted));
                }
                let n = 244; // TODO
                             //let n, err1 := strconv.ParseUint(quoted[2..4], 16, 0);
                             //if err1 != nil {
                             //		err = fmt.Errorf("invalid escape sequence {}", quoted[..4])
                             //	return
                             //}
                if !is_byte && n > 127 {
                    return Err(anyhow!("non-ASCII hex escape {} (use \\u{:04X} for the UTF-8 encoding of U+{:04x})",
					&quoted[..4], n, n));
                }
                buf.push(char::from_u32(n).unwrap());
                quoted = &quoted[4..]
            }
            Some('u' | 'U') => {
                // Unicode code point, 4 (\uXXXX) or 8 (\UXXXXXXXX) hex digits.
                let mut sz = 6;
                if quoted.chars().nth(1).unwrap() == 'U' {
                    sz = 10
                }
                if quoted.len() < sz {
                    return Err(anyhow!("truncated escape sequence {}", quoted));
                }
                let n = 255; // TODO
                             //n, err1 := strconv.ParseUint(quoted[2:sz], 16, 0)
                             //if err1 != nil {
                             //	err = fmt.Errorf(`invalid escape sequence %s`, quoted[:sz])
                             //	return
                             //}
                             // if n > unicode.MaxRune {
                             //	err = fmt.Errorf(`code point out of range: %s (max \U%08x)`,
                             //		quoted[:sz], n)
                             //	return
                             //}
                             // As in Go, surrogates are disallowed.
                if 0xD800 <= n && n < 0xE000u32 {
                    return Err(anyhow!("invalid Unicode code point U{:04x}", n));
                }
                buf.push(char::from_u32(n).unwrap());
                quoted = &quoted[sz..]
            }
            _ =>
            // In Starlark, like Go, a backslash must escape something.
            // (Python still treats unnecessary backslashes literally,
            // but since 3.6 has emitted a deprecation warning.)
            {
                return Err(anyhow!("invalid escape sequence \\{}", quoted))
            }
        }
    }

    return Ok((buf.to_string(), is_byte));
}

/*
// indexByte returns the index of the first instance of b in s, or else -1.
fn indexByte(s: string, b: byte) int {
    for i := 0; i < len(s); i++ {
        if s[i] == b {
            return i
        }
    }
    return -1
}

// Quote returns a Starlark literal that denotes s.
// If b, it returns a bytes literal.
fn Quote(s: string, b: bool) string {
    const hex = "0123456789abcdef"
    var runeTmp [utf8.UTFMax]byte

    buf := make([]byte, 0, 3*len(s)/2)
    if b {
        buf = append(buf, 'b')
    }
    buf = append(buf, '"')
    for width := 0; len(s) > 0; s = s[width:] {
        r := rune(s[0])
        width = 1
        if r >= utf8.RuneSelf {
            r, width = utf8.DecodeRuneInString(s)
        }
        if width == 1 && r == utf8.RuneError {
            // String (!b) literals accept \xXX escapes only for ASCII,
            // but we must use them here to represent invalid bytes.
            // The result is not a legal literal.
            buf = append(buf, `\x`...)
            buf = append(buf, hex[s[0]>>4])
            buf = append(buf, hex[s[0]&0xF])
            continue
        }
        if r == '"' || r == '\\' { // always backslashed
            buf = append(buf, '\\')
            buf = append(buf, byte(r))
            continue
        }
        if strconv.IsPrint(r) {
            n := utf8.EncodeRune(runeTmp[:], r)
            buf = append(buf, runeTmp[:n]...)
            continue
        }
        switch r {
        case '\a':
            buf = append(buf, `\a`...)
        case '\b':
            buf = append(buf, `\b`...)
        case '\f':
            buf = append(buf, `\f`...)
        case '\n':
            buf = append(buf, `\n`...)
        case '\r':
            buf = append(buf, `\r`...)
        case '\t':
            buf = append(buf, `\t`...)
        case '\v':
            buf = append(buf, `\v`...)
        default:
            switch {
            case r < ' ' || r == 0x7f:
                buf = append(buf, `\x`...)
                buf = append(buf, hex[byte(r)>>4])
                buf = append(buf, hex[byte(r)&0xF])
            case r > utf8.MaxRune:
                r = 0xFFFD
                fallthrough
            case r < 0x10000:
                buf = append(buf, `\u`...)
                for s := 12; s >= 0; s -= 4 {
                    buf = append(buf, hex[r>>uint(s)&0xF])
                }
            default:
                buf = append(buf, `\U`...)
                for s := 28; s >= 0; s -= 4 {
                    buf = append(buf, hex[r>>uint(s)&0xF])
                }
            }
        }
    }
    buf = append(buf, '"')
    return string(buf)
}
 */
