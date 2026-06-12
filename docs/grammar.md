# Strangemeadowlark Grammar

Reference grammar extracted from the recursive-descent parser (`src/parse.rs`),
scanner (`src/scan.rs`), token definitions (`src/token.rs`), and AST types
(`src/syntax.rs`).

---

## Current Grammar

### Lexical Elements

```
IDENT      = identifier (Unicode letter / underscore, followed by letters / digits / underscores)
INT        = decimal | 0x hex | 0o octal | 0b binary
FLOAT      = digits? "." digits? ([eE] [+−] digits)?
STRING     = "'" ... "'" | '"' ... '"' | '''...''' | """..."""
             | r'...' | r"..." | b'...' | b"..." | rb'...' | rb"..."
BYTES      = b"..." | b'...'  (produces bytes, not string)

NEWLINE    = end of logical line
INDENT     = increase in indentation level
OUTDENT    = decrease in indentation level
EOF        = end of file
```

### Keywords

```
and    break   continue  def   elif   else   for
if     in      lambda    load  not    or     pass
return while
```

The following Python keywords are recognized and mapped to `ILLEGAL`:

```
async  await  class  try  raise  import  except  nonlocal
with   is     global as    from   del     finally  yield
```

### Operators and Punctuation

```
+    -    *    /    //   %    &    |    ^    <<   >>
+=   -=   *=   /=   //=  %=   &=   |=   ^=   <<=  >>=
**   ~    .    ,    =    ;    :    (    )    [    ]    {    }
<    >    <=   >=   ==   !=   not in
```

### Operator Precedence (low → high)

| Prec | Operators                          | Associativity |
|------|------------------------------------|---------------|
| 0    | `or`                               | left          |
| 1    | `and`                              | left          |
| 2    | `not`                              | (unary)       |
| 3    | `==  !=  <  >  <=  >=  in  not in` | non-associative |
| 4    | `|`                                | left          |
| 5    | `^`                                | left          |
| 6    | `&`                                | left          |
| 7    | `<<  >>`                           | left          |
| 8    | `+  -`                             | left          |
| 9    | `*  /  //  %`                      | left          |
| 10   | unary `-  +  ~`, suffix `. [] ()`  | —             |

### Productions

```
file_input     = ( NEWLINE | stmt )* EOF

stmt           = def_stmt
               | if_stmt
               | for_stmt
               | while_stmt
               | simple_stmt

def_stmt       = "def" IDENT "(" params ")" ":" suite

if_stmt        = "if" test ":" suite ("elif" test ":" suite)*
                 ("else" ":" suite)?

for_stmt       = "for" loop_vars "in" expr ":" suite

while_stmt     = "while" test ":" suite

simple_stmt    = small_stmt (";" small_stmt)* ";"? NEWLINE

small_stmt     = "return" expr?
               | "pass" | "break" | "continue"
               | load_stmt
               | expr assign_op expr                — assignment
               | expr                                — expression statement

assign_op      = "=" | "+=" | "-=" | "*=" | "/=" | "//=" | "%="
               | "&=" | "|=" | "^=" | "<<=" | ">>="

load_stmt      = "load" "(" STRING ("," load_arg)* ","? ")"

load_arg       = STRING                             — import "name"
               | IDENT "=" STRING                   — import localname="original"

params         = /* empty */
               | param ("," param)* ","?

param          = IDENT                              — positional
               | IDENT "=" test                     — default value
               | "*"                                 — keyword-only separator
               | "*" IDENT                           — *args
               | "**" IDENT                          — **kwargs

loop_vars      = primary_with_suffix ("," primary_with_suffix)* ","?

suite          = simple_stmt
               | NEWLINE INDENT stmt+ OUTDENT

expr           = test ("," test)* ","?               — tuple if commas present

test           = "lambda" params? ":" test           — lambda (allow_cond=true)
               | test_prec(0)                        — conditional or plain

               — conditional expression (parsed after test_prec(0)):
                 test_prec(0) "if" test_prec(0) "else" test

test_no_cond   = "lambda" params? ":" test_no_cond   — lambda (allow_cond=false)
               | test_prec(0)

test_prec(N)   = "not" test_prec(N)                  — when N == precedence(not) == 2
               | binop_expr(N)

binop_expr(N)  = test_prec(N+1) (OP test_prec(N+1))* — left-associative;
                                               comparisons are non-associative;
                                               "not" "in" is synthesized to NOT_IN

primary_with_suffix
               = primary suffix*

suffix         = "." IDENT                           — dot access
               | call_suffix                         — function call
               | slice_suffix                        — index or slice

primary        = IDENT
               | INT | FLOAT | STRING | BYTES
               | list
               | dict
               | "(" ")"                             — empty tuple
               | "(" expr ")"                        — tuple or parenthesized expr
               | ("-" | "+" | "~") primary_with_suffix — unary

list           = "[" "]"
               | "[" test comp_suffix "]"            — list comprehension
               | "[" test ("," test)* ","? "]"       — list literal

dict           = "{" "}"
               | "{" dict_entry comp_suffix "}"      — dict comprehension
               | "{" dict_entry ("," dict_entry)* ","? "}"  — dict literal

dict_entry     = test ":" test

call_suffix    = "(" arg_list? ")"

arg_list       = arg ("," arg)* ","?

arg            = test ("=" test)?                    — positional or keyword
               | "*" test                            — *args
               | "**" test                           — **kwargs

slice_suffix   = "[" expr "]"                        — index
               | "[" expr? ":" expr? (":" expr?)? "]" — slice

comp_suffix    = "for" loop_vars "in" test_prec(0) comp_suffix
               | "if" test_no_cond comp_suffix
               |                                     — end ("]" or "}")
```

---

## Proposed Changes: Type Annotations & Records

The following additions implement Phase 1 (type annotation parsing) and Phase 4
(record statements) from the evolution plan. **All new syntax is optional and
backward-compatible** — unannotated programs parse exactly as before.

### New Tokens

```
ARROW     = "->"                   (new: currently Minus Gt are separate)
RECORD    = "record"               (new keyword)
LABEL     = "label"                (new keyword — type name only)
```

### New Production: `type_expr`

```
type_expr      = "None"
               | "bool"
               | "int"
               | "float"
               | "str"
               | "label"                              — build target reference
               | "list" "[" type_expr "]"
               | "dict" "[" type_expr "," type_expr "]"
               | "(" type_expr ("," type_expr)* ","? ")"  — tuple type
               | "Any"
               | IDENT                                — named type (record name or forward ref)
```

> **Note:** The keywords `None`, `bool`, `int`, `float`, `str`, `list`, `dict`
> are not currently reserved words — they are ordinary identifiers in
> Starlark. Inside `type_expr`, they are recognized contextually as type
> keywords. `label` is a new hard keyword (like `def` or `for`) to avoid
> ambiguity with the common variable name.

### Changed Production: `param`

```
param          = IDENT (":" type_expr)?              — typed positional
               | IDENT ":" type_expr "=" test        — typed with default
               | IDENT "=" test                      — untyped with default (unchanged)
               | "*"                                  — keyword-only separator (unchanged)
               | "*" IDENT (":" type_expr)?          — typed *args
               | "**" IDENT (":" type_expr)?         — typed **kwargs
```

The `:` after an IDENT is currently not valid syntax, so there is no ambiguity.
The parser looks ahead after consuming the identifier:
- If `:` → parse `type_expr`, then optionally `=` for a default value.
- If `=` → parse default value (untyped, as before).
- Otherwise → plain parameter (as before).

### Changed Production: `def_stmt`

```
def_stmt       = "def" IDENT "(" params ")" ("->" type_expr)? ":" suite
```

After the `)` and before `:`, the parser checks for `->`. If present, parse
`type_expr` as the return type. The `:` that follows the optional return type
is the existing suite delimiter — no ambiguity since `->` cannot appear in
any other position.

### Changed Production: `lambda_expr`

```
lambda_expr    = "lambda" ("(" typed_params ")" | params)? ("->" type_expr)? ":" test
```

Lambda parameters support type annotations **only when enclosed in parentheses**.
This disambiguates `:` as a type separator from `:` as the lambda body separator:

- `lambda x: x + 1` — unparenthesized, no type annotations (backward compatible)
- `lambda (x: int): x + 1` — parenthesized, type annotations allowed
- `lambda (x: int) -> int: x + 1` — parenthesized with return type
- `lambda (x, y): x + y` — parenthesized, untyped params also OK
- `lambda x -> int: x + 1` — unparenthesized with return type (no param types)

The `(` signals that `:` inside is a type annotation, not the body separator.

```
typed_params   = typed_param ("," typed_param)* ","?

typed_param    = IDENT (":" type_expr) ("=" test)?
               | IDENT "=" test
               | "*"                                  — keyword-only separator
               | "*" IDENT (":" type_expr)?
               | "**" IDENT (":" type_expr)?
```

### New Production: `record_stmt`

```
record_stmt    = "record" IDENT "(" record_fields ")" NEWLINE

record_fields  = record_field ("," record_field)* ","?

record_field   = IDENT ":" type_expr ("=" test)?     — field with optional default
```

`record` is a new top-level keyword. A record statement defines an immutable
struct-like type. It is a statement (not an expression) and does not have a
body — the fields and their types are the complete definition.

### Changed Production: `stmt`

```
stmt           = def_stmt
               | if_stmt
               | for_stmt
               | while_stmt
               | record_stmt                          — NEW
               | simple_stmt
```

### Summary of All Changes

| Production | Change | Backward-compatible? |
|---|---|---|
| `type_expr` | **New** — type annotation syntax | Yes (new nonterminal) |
| `param` | Add optional `":" type_expr` after IDENT | Yes (`:` is currently invalid after param name) |
| `def_stmt` | Add optional `"->" type_expr` before `":"` | Yes (`->` is currently two separate tokens) |
| `lambda_expr` | Add optional `"->" type_expr` and typed params | Yes (same lookahead logic) |
| `record_stmt` | **New** — `record Name(field: Type, ...)` | Yes (new keyword) |
| `stmt` | Add `record_stmt` alternative | Yes |
| Scanner | Recognize `->` as `ARROW` token | Yes (currently `MINUS GT` never valid in that position) |
| Scanner | Recognize `record` as `RECORD` keyword | **Potentially breaking** if `record` is used as a variable name |
| Scanner | Recognize `label` as `LABEL` keyword | **Potentially breaking** if `label` is used as a variable name |

### Breaking Change Mitigation

`record` and `label` as hard keywords would break code that uses them as
variable names. Two options:

1. **Hard keywords** (simplest): Accept the breakage. `record` is rare as a
   variable name in Starlark; `label` is more common but the type annotation
   use case makes it worth claiming.

2. **Soft keywords** (safe): Only treat `record` and `label` as keywords in
   syntactic positions where they are expected (start of statement for
   `record`, inside `type_expr` for `label`). Elsewhere they remain ordinary
   identifiers. This requires parser context tracking but preserves full
   backward compatibility.

**Recommendation:** Use soft keywords. `label` is a common variable name in
Bazel/Starlark code (`label = "//..."`). The parser can distinguish `record`
at statement start from `record` as an identifier with one token of lookahead,
and `label` inside `type_expr` from `label` elsewhere with the `:` or `[`
context.

### Examples

```python
# Simple typed function
def add(x: int, y: int) -> int:
    return x + y

# Mix of typed and untyped params
def greet(name: str, greeting = "Hello") -> str:
    return greeting + " " + name

# Label-typed parameter
def rust_binary(name: label, srcs: list[label], deps: list[label]) -> label:
    return name

# Record definition
record Dep(target: label, deps: list[label])

record Point(x: int, y: int)

# Record with defaults
record Config(opt_level: int = 0, debug: bool = True)

# Typed lambda with parenthesized params (type annotations allowed)
square = lambda (x: int) -> int: x * x

# Typed lambda with unparenthesized params (return type only, no param types)
square = lambda x -> int: x * x

# Untyped code still works exactly as before
def f(x, y):
    return x + y
```
