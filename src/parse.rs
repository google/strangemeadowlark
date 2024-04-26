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

use std::path::Path;

use crate::scan::*;
use crate::syntax::{StmtData::*, *};
use crate::token::*;
use anyhow::{anyhow, Result};
use bumpalo::Bump;

// This file defines a recursive-descent parser for Starlark.
// The LL(1) grammar of Starlark and the names of many productions follow Python 2.7.
//
// TODO: use syntax.Error more systematically throughout the
// package.  Verify that error positions are correct using the
// chunkedfile mechanism.

// Enable this flag to print the token stream and log.Fatal on the first error.
const DEBUG: bool = false;

// Mode controls optional parser functionality.
#[derive(PartialEq, Eq)]
pub enum Mode {
    Plain,
    RetainComments,
}

// Parse parses the input data and returns the corresponding parse tree.
//
// If src != nil, Parse parses the source from src and the filename
// is only used when recording position information.
// The type of the argument for the src parameter must be string,
// []byte, io.Reader, or FilePortion.
// If src == nil, Parse parses the file specified by filename.
pub fn parse<'b, P: AsRef<Path>>(
    bump: &'b Bump,
    path: &'b P,
    src: &'b str,
    mode: Mode,
) -> Result<&'b FileUnit<'b>> {
    let mut p = Parser::new(bump, path, src, mode)?;
    p.parse_file(path.as_ref())
}

pub fn parse_expr<'b, P: AsRef<Path>>(
    bump: &'b Bump,
    path: &'b P,
    src: &'b str,
    mode: Mode,
) -> Result<ExprRef<'b>> {
    let mut p = Parser::new(bump, path, src, mode)?;
    p.parse_expr(false)
}

struct Parser<'a, 'b>
where
    'b: 'a,
{
    sc: Scanner<'a>,
    tok: TokenValue,
    pos: Position,
    bump: &'b Bump,
}

impl<'a, 'b> Parser<'a, 'b> {
    fn new<P: AsRef<Path>>(bump: &'b Bump, path: &'b P, src: &'b str, mode: Mode) -> Result<Self> {
        let mut sc = Scanner::new(path, src, mode == Mode::RetainComments)?;
        // Read first lookahead token.
        let tok = sc.next_token()?;
        let pos = sc.pos.clone();
        Ok(Parser { sc, tok, pos, bump })
    }

    fn line_comments(&self) -> Vec<Comment> {
        self.sc.line_comments.clone()
    }

    fn suffix_comments(&self) -> Vec<Comment> {
        self.sc.suffix_comments.clone()
    }

    // next_token advances the scanner and returns the position of the
    // previous token.
    fn next_token(&mut self) -> Result<Position> {
        let old_pos = self.sc.pos.clone();
        self.tok = self.sc.next_token()?;
        self.pos = old_pos;
        // enable to see the token stream
        if DEBUG {
            println!("next_token: {} {}", self.tok.kind, self.pos);
        }
        Ok(self.pos.clone())
    }

    fn consume(&mut self, expected: Token) -> Result<Position> {
        if self.tok.kind != expected {
            return Err(anyhow!(
                "{} got {}, want {}",
                self.tok.pos,
                self.tok.kind,
                expected
            ));
        }
        self.next_token()
    }

    // file_input = (NEWLINE | stmt)* EOF
    fn parse_file(&mut self, path: &'b Path) -> Result<&'b FileUnit<'b>>
    where
        'b: 'a,
    {
        let mut stmts: Vec<StmtRef<'b>> = vec![];
        while self.tok.kind != Token::Eof {
            if self.tok.kind == Token::Newline {
                self.next_token()?;
                continue;
            }
            self.parse_stmt(&mut stmts)?;
        }
        let f = self.bump.alloc(FileUnit {
            path,
            stmts: self.bump.alloc_slice_copy(&stmts.into_boxed_slice()),
            line_comments: self.line_comments(),
            suffix_comments: self.suffix_comments(),
        });
        Ok(f)
    }

    fn parse_stmt(&mut self, stmts: &mut Vec<StmtRef<'b>>) -> Result<()> {
        match self.tok.kind {
            Token::Def => stmts.push(self.parse_def_stmt()?),
            Token::If => stmts.push(self.parse_if_stmt()?),
            Token::For => stmts.push(self.parse_for_stmt()?),
            Token::While => stmts.push(self.parse_while_stmt()?),
            _ => return self.parse_simple_stmt(stmts, true),
        }
        Ok(())
    }

    fn parse_def_stmt(&mut self) -> Result<StmtRef<'b>> {
        self.next_token()?; // consume DEF
        let def_pos = self.pos.clone();
        let id = self.parse_ident()?;
        self.consume(Token::LParen)?;
        let lparen: Position = self.pos.clone();
        let params = self.parse_params()?;
        self.consume(Token::RParen)?;
        let rparen = self.pos.clone();
        self.consume(Token::Colon)?;
        let body = self.parse_suite()?;
        let stmt: &'b mut Stmt<'b> = self.bump.alloc(Stmt {
            span: Span {
                start: def_pos.clone(),
                end: def_pos.clone(),
            },
            data: DefStmt {
                def_pos,
                name: id,
                lparen,
                params,
                rparen,
                body,
            },
        });
        Ok(stmt)
    }

    fn parse_if_stmt(&mut self) -> Result<StmtRef<'b>> {
        self.next_token()?;
        let if_pos = self.pos.clone(); // consume IF
        let cond = self.parse_test()?;
        self.consume(Token::Colon)?;
        let body = self.parse_suite()?;
        let if_stmt = self.bump.alloc(Stmt {
            span: Span {
                start: if_pos.clone(),
                end: if_pos.clone(),
            },
            data: IfStmt {
                if_pos,
                cond,
                then_arm: body,
                else_pos: None,
                else_arm: &[],
            },
        });
        // Collect "elif" statements and connect them later.
        let mut elifs = vec![];
        while self.tok.kind == Token::Elif {
            let elif_pos = self.next_token()?;
            // = self.pos.clone(); // consume ELIF
            let cond = self.parse_test()?;
            self.consume(Token::Colon)?;
            let body = self.parse_suite()?;
            elifs.push(self.bump.alloc(Stmt {
                span: Span {
                    start: elif_pos.clone(),
                    end: elif_pos.clone(),
                },
                data: IfStmt {
                    if_pos: elif_pos.clone(),
                    cond,
                    then_arm: body,
                    else_pos: None,
                    else_arm: &[],
                },
            }));
        }
        let mut else_arm = None;
        if self.tok.kind == Token::Else {
            let else_pos = Some(self.next_token()?); // consume ELSE
            self.consume(Token::Colon)?;
            else_arm = Some((else_pos, self.parse_suite()?));
            //else_arm =s.push(else_arm);
        }
        if !elifs.is_empty() {
            let mut tmp = elifs.pop().unwrap();
            if let Some((last_else_pos, last_else_arm)) = else_arm {
                match tmp {
                    Stmt {
                        data:
                            IfStmt {
                                else_pos, else_arm, ..
                            },
                        ..
                    } => {
                        *else_pos = last_else_pos;
                        *else_arm = last_else_arm;
                    }
                    _ => unreachable!(),
                }
            }
            while let Some(next_last_if) = elifs.pop() {
                match next_last_if {
                    Stmt {
                        data:
                            IfStmt {
                                else_pos, else_arm, ..
                            },
                        ..
                    } => {
                        *else_pos = Some(tmp.span.start.clone());
                        *else_arm = self.bump.alloc_slice_copy(&[&*tmp]);
                        tmp = next_last_if;
                    }
                    _ => unreachable!(),
                }
            }
            match if_stmt {
                Stmt {
                    data:
                        IfStmt {
                            else_pos, else_arm, ..
                        },
                    ..
                } => {
                    *else_pos = Some(tmp.span.start.clone());
                    *else_arm = self.bump.alloc_slice_copy(&[&*tmp]);
                }
                _ => unreachable!(),
            }
        } else if let Some((last_else_pos, last_else_arm)) = else_arm {
            match if_stmt {
                Stmt {
                    data:
                        IfStmt {
                            else_pos, else_arm, ..
                        },
                    ..
                } => {
                    *else_pos = last_else_pos;
                    *else_arm = last_else_arm;
                }
                _ => unreachable!(),
            }
        }

        Ok(if_stmt)
    }

    fn parse_for_stmt(&mut self) -> Result<StmtRef<'b>> {
        let for_pos = self.next_token()?; // consume FOR
        let vars = self.parse_for_loop_vars()?;
        self.consume(Token::In)?;
        let x = self.parse_expr(false)?;
        self.consume(Token::Colon)?;
        let body = self.parse_suite()?;
        let for_stmt = self.bump.alloc(Stmt {
            span: Span {
                start: for_pos.clone(),
                end: for_pos.clone(),
            },
            data: ForStmt {
                for_pos,
                vars,
                x,
                body,
            },
        });
        Ok(for_stmt)
    }

    // Equivalent to 'exprlist' production in Python grammar.
    //
    // loop_variables = primary_with_suffix (COMMA primary_with_suffix)* COMMA?
    fn parse_for_loop_vars(&mut self) -> Result<ExprRef<'b>> {
        // Avoid parseExpr because it would consume the IN token
        // following x in "for x in y: ...".
        let v = self.parse_primary_with_suffix()?;
        if self.tok.kind != Token::Comma {
            return Ok(v);
        }

        let mut list = vec![v];
        while self.tok.kind == Token::Comma {
            self.next_token()?;
            if terminates_expr_list(&self.tok.kind) {
                break;
            }
            list.push(self.parse_primary_with_suffix()?);
        }
        let list = self.bump.alloc_slice_copy(&list.into_boxed_slice());
        let for_loop_vars = self.bump.alloc(Expr {
            span: Span {
                start: v.span.start.clone(),
                end: v.span.start.clone(), /* todo */
            },
            data: ExprData::TupleExpr {
                lparen: None,
                list,
                rparen: None,
            },
        });
        Ok(&*for_loop_vars)
    }

    fn parse_while_stmt(&mut self) -> Result<StmtRef<'b>> {
        let while_pos = self.next_token()?; // consume WHILE
        let cond = self.parse_test()?;
        self.consume(Token::Colon)?;
        let body = self.parse_suite()?;
        let while_stmt = self.bump.alloc(Stmt {
            span: Span {
                start: while_pos.clone(),
                end: while_pos.clone(),
            },
            data: StmtData::WhileStmt {
                while_pos,
                cond,
                body,
            },
        });
        Ok(while_stmt)
    }

    // stmt = LOAD '(' STRING {',' (IDENT '=')? STRING} [','] ')'
    fn parse_load_stmt(&mut self) -> Result<StmtRef<'b>> {
        let load_pos = self.next_token()?; // consume LOAD
        self.consume(Token::LParen)?;

        if !matches!(self.tok.kind, Token::String { .. }) {
            return Err(anyhow!(
                "{} first operand of load statement must be a string literal",
                self.pos.clone()
            ));
        }
        let module = self.parse_primary()?; // .(*Literal)

        let mut from: Vec<&Ident> = vec![];
        let mut to: Vec<&Ident> = vec![]; // var from, to []*Ident
        while self.tok.kind != Token::RParen && self.tok.kind != Token::Eof {
            self.consume(Token::Comma)?;
            if self.tok.kind == Token::RParen {
                break; // allow trailing comma
            }
            //let pos = self.pos.clone();
            match self.tok.kind.clone() {
                Token::String { decoded } => {
                    // load("module", "id")
                    // To name is same as original.
                    let lit = self.parse_primary()?; //.(*Literal)
                    let id = self.bump.alloc(Ident {
                        name_pos: lit.span.start.clone(),
                        name: decoded,
                    });
                    to.push(id);
                    from.push(id);
                }
                Token::Ident { name } => {
                    // load("module", to="from")
                    let id = self.parse_ident()?;
                    //let name_pos = self.pos.clone();
                    to.push(id);
                    if self.tok.kind != Token::Eq {
                        return Err(anyhow!(
                            "{} load operand must be {} or {}=\"originalname\" (want '=' after {})",
                            self.pos,
                            name,
                            name,
                            name
                        ));
                    }
                    self.consume(Token::Eq)?;
                    if !matches!(self.tok.kind, Token::String { .. }) {
                        return Err(anyhow!(
                            "{} original name of loaded symbol must be quoted: {}=\"originalname\"",
                            self.pos,
                            name
                        ));
                    }
                    let lit = self.parse_primary()?; // .(*Literal)
                    match &lit.data {
                        ExprData::Literal {
                            token: Token::String { decoded },
                            token_pos,
                            ..
                        } => from.push(self.bump.alloc(Ident {
                            name_pos: token_pos.clone(),
                            name: decoded.clone(),
                        })),
                        _ => unreachable!(),
                    }
                }
                Token::RParen => {
                    return Err(anyhow!("{} trailing comma in load statement", self.pos))
                }

                _ => {
                    return Err(anyhow!(
                        "{} load operand must be \"name\" or localname=\"name\" (got {})",
                        self.pos,
                        self.tok.kind
                    ))
                }
            }
        }
        let rparen = self.consume(Token::RParen)?;

        if to.is_empty() {
            return Err(anyhow!(
                "{} load statement must import at least 1 symbol",
                self.pos
            ));
        }
        let to = self.bump.alloc_slice_copy(&to.into_boxed_slice());
        let from = self.bump.alloc_slice_copy(&from.into_boxed_slice());
        let load_stmt = self.bump.alloc(Stmt {
            span: Span {
                start: load_pos.clone(),
                end: load_pos.clone(),
            },
            data: StmtData::LoadStmt {
                load_pos,
                module,
                to,
                from,
                rparen_pos: rparen,
            },
        });
        Ok(load_stmt)
    }

    // simple_stmt = small_stmt (SEMI small_stmt)* SEMI? NEWLINE
    // In REPL mode, it does not consume the NEWLINE.
    fn parse_simple_stmt(&mut self, stmts: &mut Vec<StmtRef<'b>>, consume_nl: bool) -> Result<()> {
        loop {
            stmts.push(self.parse_small_stmt()?);
            if self.tok.kind != Token::Semi {
                break;
            }
            self.next_token()?; // consume SEMI
            if self.tok.kind == Token::Newline || self.tok.kind == Token::Eof {
                break;
            }
        }
        // EOF without NEWLINE occurs in `if x: pass", for example.
        if self.tok.kind != Token::Eof && consume_nl {
            self.consume(Token::Newline)?;
        }

        Ok(())
    }

    // small_stmt = RETURN expr?
    //
    //	| PASS | BREAK | CONTINUE
    //	| LOAD ...
    //	| expr ('=' | '+=' | '-=' | '*=' | '/=' | '%=' | '&=' | '|=' | '^=' | '<<=' | '>>=') expr   // assign
    //	| expr
    fn parse_small_stmt(&mut self) -> Result<StmtRef<'b>> {
        match self.tok.kind {
            Token::Return => {
                let pos = self.next_token()?; // consume RETURN
                let mut result = None;
                if self.tok.kind != Token::Eof
                    && self.tok.kind != Token::Newline
                    && self.tok.kind != Token::Semi
                {
                    result = Some(self.parse_expr(false)?);
                }
                let return_stmt = self.bump.alloc(Stmt {
                    span: Span {
                        start: pos.clone(),
                        end: pos.clone(),
                    },
                    data: StmtData::ReturnStmt {
                        return_pos: pos,
                        result,
                    },
                });
                return Ok(return_stmt);
            }
            Token::Break | Token::Continue | Token::Pass => {
                let tok = self.tok.kind.clone();
                let pos = self.next_token()?; // consume it
                let branch_stmt = self.bump.alloc(Stmt {
                    span: Span {
                        start: pos.clone(),
                        end: pos.clone(),
                    },
                    data: StmtData::BranchStmt {
                        token: tok,
                        token_pos: pos,
                    },
                });
                return Ok(branch_stmt);
            }
            Token::Load => return self.parse_load_stmt(),
            _ => {}
        }
        // Assignment
        let pos = self.pos.clone();
        let x = self.parse_expr(false)?;
        match self.tok.kind {
            Token::Eq
            | Token::PlusEq
            | Token::MinusEq
            | Token::StarEq
            | Token::SlashEq
            | Token::SlashSlashEq
            | Token::PercentEq
            | Token::AmpersandEq
            | Token::PipeEq
            | Token::CaretEq
            | Token::LtLtEq
            | Token::GtGtEq => {
                let op = self.tok.kind.clone();
                let pos = self.next_token()?; // consume op
                let rhs = self.parse_expr(false)?;
                let assign_stmt = self.bump.alloc(Stmt {
                    span: Span {
                        start: pos.clone(),
                        end: pos.clone(),
                    },
                    data: StmtData::AssignStmt {
                        op_pos: pos,
                        op,
                        lhs: x,
                        rhs,
                    },
                });
                return Ok(assign_stmt);
            }
            _ => {}
        }

        // Expression statement (e.g. function call, doc string).
        let expr_stmt = self.bump.alloc(Stmt {
            span: Span {
                start: pos.clone(),
                end: pos,
            },
            data: StmtData::ExprStmt { x },
        });
        Ok(expr_stmt)
    }

    // parse_test parses a 'test', a single-component expression.
    fn parse_test(&mut self) -> Result<ExprRef<'b>> {
        if self.tok.kind == Token::Lambda {
            return self.parse_lambda(true);
        }

        let x = self.parse_test_prec(0)?;

        // conditional expression (t IF cond ELSE f)
        if self.tok.kind == Token::If {
            let if_pos = self.next_token()?;
            let cond = self.parse_test_prec(0)?;
            if self.tok.kind != Token::Else {
                return Err(anyhow!(
                    "{} conditional expression without else clause",
                    if_pos
                ));
            }
            let else_pos = self.next_token()?;
            let else_ = self.parse_test()?;
            return Ok(self.bump.alloc(Expr {
                span: Span {
                    start: if_pos.clone(),
                    end: if_pos.clone(),
                },
                data: ExprData::CondExpr {
                    if_pos,
                    cond,
                    then_arm: x,
                    else_pos,
                    else_arm: else_,
                },
            }));
        }
        Ok(x)
    }

    fn parse_ident(&mut self) -> Result<&'b Ident> {
        match self.tok.kind.clone() {
            Token::Ident { name } => {
                let id = self.bump.alloc(Ident {
                    name_pos: self.tok.pos.clone(),
                    name,
                });
                self.next_token()?;
                Ok(id)
            }
            _ => Err(anyhow!("{} not an identifier", self.pos)),
        }
    }

    // params = (param COMMA)* param COMMA?
    //
    //	|
    //
    // param = IDENT
    //
    //	| IDENT EQ test
    //	| STAR
    //	| STAR IDENT
    //	| STARSTAR IDENT
    //
    // parseParams parses a parameter list.  The resulting expressions are of the form:
    //
    //	*Ident                                          x
    //	*Binary{Op: EQ, X: *Ident, Y: Expr}             x=y
    //	*Unary{Op: STAR}                                *
    //	*Unary{Op: STAR, X: *Ident}                     *args
    //	*Unary{Op: STARSTAR, X: *Ident}                 **kwargs
    fn parse_params(&mut self) -> Result<&'b [ExprRef<'b>]> {
        //fn  parseParams() []Expr {
        let mut params = vec![];
        while self.tok.kind != Token::RParen
            && self.tok.kind != Token::Colon
            && self.tok.kind != Token::Eof
        {
            if !params.is_empty() {
                self.consume(Token::Comma)?;
            }
            if self.tok.kind == Token::RParen {
                break;
            }

            // * or *args or **kwargs
            if self.tok.kind == Token::Star || self.tok.kind == Token::StarStar {
                let op = self.tok.kind.clone();
                let op_pos = self.next_token()?;
                let (x, end) =
                    if op == Token::StarStar || matches!(self.tok.kind, Token::Ident { .. }) {
                        let ident = self.parse_ident()?;
                        let ident = self.bump.alloc(ident.as_expr());
                        (Some(&*ident), self.pos.clone())
                    } else {
                        (None, op_pos.clone())
                    };
                let unary_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: op_pos.clone(),
                        end,
                    },
                    data: ExprData::UnaryExpr { op_pos, op, x },
                });
                params.push(&*unary_expr);
                continue;
            }

            // IDENT
            // IDENT = test
            let id = self.parse_ident()?;
            let id = self.bump.alloc(id.as_expr());
            if self.tok.kind == Token::Eq {
                // default value
                let eq = self.next_token()?;
                let dflt = self.parse_test()?;
                let binary_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: id.span.start.clone(),
                        end: dflt.span.end.clone(),
                    },
                    data: ExprData::BinaryExpr {
                        x: id,
                        op_pos: eq,
                        op: Token::Eq,
                        y: dflt,
                    },
                });
                params.push(binary_expr);
                continue;
            }

            params.push(&*id);
        }
        let params = self.bump.alloc_slice_copy(&params.into_boxed_slice());
        Ok(&*params)
    }

    // parseExpr parses an expression, possible consisting of a
    // comma-separated list of 'test' expressions.
    //
    // In many cases we must use parse_test to avoid ambiguity such as
    // f(x, y) vs. f((x, y)).
    fn parse_expr(&mut self, in_parens: bool) -> Result<ExprRef<'b>> {
        let x = self.parse_test()?;
        if self.tok.kind != Token::Comma {
            return Ok(x);
        }

        // tuple
        let mut exprs = vec![x];
        self.parse_exprs(&mut exprs, in_parens)?;
        let list = self.bump.alloc_slice_copy(&exprs.into_boxed_slice());
        let tuple_expr = self.bump.alloc(Expr {
            span: Span {
                start: x.span.start.clone(),
                end: self.pos.clone(),
            },
            data: ExprData::TupleExpr {
                lparen: None,
                list,
                rparen: None,
            },
        });
        Ok(tuple_expr)
    }

    // primary = IDENT
    //
    //	| INT | FLOAT | STRING | BYTES
    //	| '[' ...                    // list literal or comprehension
    //	| '{' ...                    // dict literal or comprehension
    //	| '(' ...                    // tuple or parenthesized expression
    //	| ('-'|'+'|'~') primary_with_suffix
    fn parse_primary(&mut self) -> Result<ExprRef<'b>> {
        match self.tok.kind {
            Token::Ident { .. } => {
                let ident = self.parse_ident()?;
                let ident_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: ident.name_pos.clone(),
                        end: ident.name_pos.clone(),
                    },
                    data: ExprData::Ident(ident),
                });
                Ok(ident_expr)
            }

            Token::Int { .. }
            | Token::Float { .. }
            | Token::String { .. }
            | Token::Bytes { .. } => {
                let token = self.tok.kind.clone();
                let token_pos = self.pos.clone();
                let raw = self.tok.raw.clone();
                let pos = self.next_token()?;
                let literal = self.bump.alloc(Expr {
                    span: Span {
                        start: pos.clone(),
                        end: pos,
                    },
                    data: ExprData::Literal {
                        token,
                        token_pos,
                        raw,
                    },
                });
                Ok(literal)
            }
            Token::LBrack => self.parse_list(),

            Token::LBrace => self.parse_dict(),

            Token::LParen => {
                let lparen = self.next_token()?;
                if self.tok.kind == Token::RParen {
                    // empty tuple
                    let rparen = self.next_token()?;
                    let tuple_expr = self.bump.alloc(Expr {
                        span: Span {
                            start: lparen.clone(),
                            end: rparen.clone(),
                        },
                        data: ExprData::TupleExpr {
                            lparen: Some(lparen),
                            list: &[],
                            rparen: Some(rparen),
                        },
                    });
                    return Ok(tuple_expr);
                }
                let e = self.parse_expr(true)?; // allow trailing comma
                let rparen = self.consume(Token::RParen)?;
                let paren_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: lparen.clone(),
                        end: rparen.clone(),
                    },
                    data: ExprData::ParenExpr {
                        lparen,
                        x: e,
                        rparen,
                    },
                });
                Ok(paren_expr)
            }
            Token::Minus | Token::Plus | Token::Tilde => {
                // unary
                let tok = self.tok.kind.clone();
                let pos = self.next_token()?;
                let x = self.parse_primary_with_suffix()?;
                let unary_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: pos.clone(),
                        end: pos.clone(),
                    },
                    data: ExprData::UnaryExpr {
                        op_pos: pos,
                        op: tok,
                        x: Some(x),
                    },
                });
                Ok(unary_expr)
            }
            _ => Err(anyhow!(
                "{} got {}, want primary expression",
                self.pos,
                self.tok.kind
            )),
        }
    }

    // list = '[' ']'
    //
    //	| '[' expr ']'
    //	| '[' expr expr_list ']'
    //	| '[' expr (FOR loop_variables IN expr)+ ']'
    fn parse_list(&mut self) -> Result<ExprRef<'b>> {
        let lbrack = self.next_token()?;
        if self.tok.kind == Token::RBrack {
            // empty List
            let rbrack = self.next_token()?;
            let list_expr = self.bump.alloc(Expr {
                span: Span {
                    start: lbrack.clone(),
                    end: rbrack.clone(),
                },
                data: ExprData::ListExpr {
                    lbrack,
                    list: &[],
                    rbrack,
                },
            });
            return Ok(list_expr);
        }

        let x = self.parse_test()?;

        if self.tok.kind == Token::For {
            // list comprehension
            return self.parse_comprehension_suffix(lbrack, x, Token::RBrack);
        }

        let mut exprs = vec![x];
        if self.tok.kind == Token::Comma {
            // multi-item list literal
            self.parse_exprs(&mut exprs, true)? // allow trailing comma
        }

        let rbrack = self.consume(Token::RBrack)?;
        let list = self.bump.alloc_slice_copy(&exprs.into_boxed_slice());
        let list_expr = self.bump.alloc(Expr {
            span: Span {
                start: lbrack.clone(),
                end: rbrack.clone(),
            },
            data: ExprData::ListExpr {
                lbrack,
                list,
                rbrack,
            },
        });
        Ok(list_expr)
    }

    // dict = '{' '}'
    //
    //	| '{' dict_entry_list '}'
    //	| '{' dict_entry FOR loop_variables IN expr '}'
    fn parse_dict(&mut self) -> Result<ExprRef<'b>> {
        let lbrace = self.next_token()?;
        if self.tok.kind == Token::RBrace {
            // empty dict
            let rbrace = self.next_token()?;
            let dict_expr = self.bump.alloc(Expr {
                span: Span {
                    start: lbrace.clone(),
                    end: rbrace.clone(),
                },
                data: ExprData::DictExpr {
                    lbrace,
                    list: &[],
                    rbrace,
                },
            });
            return Ok(dict_expr);
        }

        let x = self.parse_dict_entry()?;

        if self.tok.kind == Token::For {
            // dict comprehension
            return self.parse_comprehension_suffix(lbrace, x, Token::RBrace);
        }

        let mut entries = vec![x];
        while self.tok.kind == Token::Comma {
            self.next_token()?;
            if self.tok.kind == Token::RBrace {
                break;
            }
            entries.push(self.parse_dict_entry()?);
        }

        let rbrace = self.consume(Token::RBrace)?;
        let list = self.bump.alloc_slice_copy(&entries.into_boxed_slice());
        let dict_expr = self.bump.alloc(Expr {
            span: Span {
                start: lbrace.clone(),
                end: rbrace.clone(),
            },
            data: ExprData::DictExpr {
                lbrace,
                list,
                rbrace,
            },
        });
        Ok(dict_expr)
    }

    // dict_entry = test ':' test
    fn parse_dict_entry(&mut self) -> Result<ExprRef<'b>> {
        let k = self.parse_test()?;
        let colon = self.consume(Token::Colon)?;
        let v = self.parse_test()?;
        let dict_entry = self.bump.alloc(Expr {
            span: Span {
                start: k.span.start.clone(),
                end: v.span.end.clone(),
            },
            data: ExprData::DictEntry {
                key: k,
                colon,
                value: v,
            },
        });
        Ok(dict_entry)
    }

    // parseExprs parses a comma-separated list of expressions, starting with the comma.
    // It is used to parse tuples and list elements.
    // expr_list = (',' expr)* ','?
    fn parse_exprs(
        &mut self,
        exprs: &mut Vec<ExprRef<'b>>,
        allow_trailing_comma: bool,
    ) -> Result<()> {
        while self.tok.kind == Token::Comma {
            let pos = self.next_token()?;
            if terminates_expr_list(&self.tok.kind) {
                if !allow_trailing_comma {
                    return Err(anyhow!("{} unparenthesized tuple with trailing comma", pos));
                }
                break;
            }
            exprs.push(self.parse_test()?);
        }
        Ok(())
    }

    // call_suffix = '(' arg_list? ')'
    fn parse_call_suffix(&mut self, func: ExprRef<'b>) -> Result<ExprRef<'b>> {
        let lparen = self.consume(Token::LParen)?;
        let mut args: &[&Expr] = &[];
        let rparen = if self.tok.kind == Token::RParen {
            self.next_token()?
        } else {
            args = self.parse_args()?;
            self.consume(Token::RParen)?
        };
        let call_expr = self.bump.alloc(Expr {
            span: Span {
                start: func.span.start.clone(),
                end: rparen.clone(),
            },
            data: ExprData::CallExpr {
                func,
                lparen,
                args,
                rparen,
            },
        });
        Ok(call_expr)
    }

    // parseLambda parses a lambda expression.
    // The allowCond flag allows the body to be an 'a if b else c' conditional.
    fn parse_lambda(&mut self, allow_cond: bool) -> Result<ExprRef<'b>> {
        let lambda_pos = self.next_token()?;
        let mut params: &[&Expr] = &[];
        if self.tok.kind != Token::Colon {
            params = self.parse_params()?
        }
        self.consume(Token::Colon)?;

        let body = if allow_cond {
            self.parse_test()?
        } else {
            self.parse_test_no_cond()?
        };

        let lambda_expr = self.bump.alloc(Expr {
            span: Span {
                start: lambda_pos.clone(),
                end: body.span.end.clone(),
            },
            data: ExprData::LambdaExpr {
                lambda_pos,
                params,
                body,
            },
        });
        Ok(lambda_expr)
    }

    // comp_suffix = FOR loopvars IN expr comp_suffix
    //
    //	| IF expr comp_suffix
    //	| ']'  or  ')'                              (end)
    //
    // There can be multiple FOR/IF clauses; the first is always a FOR.
    fn parse_comprehension_suffix(
        &mut self,
        lbrace: Position,
        body: ExprRef<'b>,
        end_brace: Token,
    ) -> Result<ExprRef<'b>> {
        let mut clauses = vec![]; // []Node
        while self.tok.kind != end_brace {
            if self.tok.kind == Token::For {
                let for_pos = self.next_token()?;
                let vars = self.parse_for_loop_vars()?;
                let in_pos = self.consume(Token::In)?;
                // Following Python 3, the operand of IN cannot be:
                // - a conditional expression ('x if y else z'),
                //   due to conflicts in Python grammar
                //  ('if' is used by the comprehension);
                // - a lambda expression
                // - an unparenthesized tuple.
                let x = self.parse_test_prec(0)?;
                let clause = self.bump.alloc(Clause::ForClause {
                    for_pos,
                    vars,
                    in_pos,
                    x,
                });
                clauses.push(&*clause);
            } else if self.tok.kind == Token::If {
                let if_pos = self.next_token()?;
                let cond = self.parse_test_no_cond()?;
                let clause = self.bump.alloc(Clause::IfClause { if_pos, cond });
                clauses.push(&*clause);
            } else {
                return Err(anyhow!(
                    "{} got {}, want '{}', for, or if",
                    self.pos,
                    self.tok.kind,
                    end_brace
                ));
            }
        }
        let rbrace = self.next_token()?;
        let clauses = self.bump.alloc_slice_copy(&clauses.into_boxed_slice());
        let comprehension = self.bump.alloc(Expr {
            span: Span {
                start: lbrace.clone(),
                end: rbrace.clone(),
            },
            data: ExprData::Comprehension {
                curly: end_brace == Token::RBrace,
                lbrack_pos: lbrace,
                body,
                clauses,
                rbrack_pos: rbrace,
            },
        });
        Ok(comprehension)
    }

    // parse_testNoCond parses a a single-component expression without
    // consuming a trailing 'if expr else expr'.
    fn parse_test_no_cond(&mut self) -> Result<ExprRef<'b>> {
        if self.tok.kind == Token::Lambda {
            self.parse_lambda(false)
        } else {
            self.parse_test_prec(0)
        }
    }

    fn parse_test_prec(&mut self, prec: usize) -> Result<ExprRef<'b>> {
        if prec >= SUP_PREC {
            return self.parse_primary_with_suffix();
        }

        // expr = NOT expr
        if self.tok.kind == Token::Not && prec == Token::Not.precedence().unwrap() {
            let op_pos = self.next_token()?;
            let x = self.parse_test_prec(prec)?;
            let unary_expr = self.bump.alloc(Expr {
                span: Span {
                    start: op_pos.clone(),
                    end: x.span.end.clone(),
                },
                data: ExprData::UnaryExpr {
                    op_pos,
                    op: Token::Not,
                    x: Some(x),
                },
            });
            return Ok(unary_expr);
        }

        self.parse_binop_expr(prec)
    }

    // parseArgs parses a list of actual parameter values (arguments).
    // It mirrors the structure of parseParams.
    // arg_list = ((arg COMMA)* arg COMMA?)?
    fn parse_args(&mut self) -> Result<&'b [ExprRef<'b>]> {
        let mut args = vec![];
        while self.tok.kind != Token::RParen && self.tok.kind != Token::Eof {
            if !args.is_empty() {
                self.consume(Token::Comma)?;
            }
            if self.tok.kind == Token::RParen {
                break;
            }

            // *args or **kwargs
            if self.tok.kind == Token::Star || self.tok.kind == Token::StarStar {
                let op = self.tok.kind.clone();
                let op_pos = self.next_token()?;
                let x = self.parse_test()?;
                let unary_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: op_pos.clone(),
                        end: x.span.end.clone(),
                    },
                    data: ExprData::UnaryExpr {
                        op_pos,
                        op,
                        x: Some(x),
                    },
                });
                args.push(&*unary_expr);
                continue;
            }

            // We use a different strategy from Bazel here to stay within LL(1).
            // Instead of looking ahead two tokens (IDENT, EQ) we parse
            // 'test = test' then check that the first was an IDENT.
            let mut x = self.parse_test()?;

            if self.tok.kind == Token::Eq {
                // name = value
                if !matches!(x.data, ExprData::Ident { .. }) {
                    return Err(anyhow!(
                        "{} keyword argument must have form name=expr",
                        self.pos
                    ));
                }
                let op_pos = self.next_token()?;
                let y = self.parse_test()?;
                x = self.bump.alloc(Expr {
                    span: Span {
                        start: x.span.start.clone(),
                        end: y.span.end.clone(),
                    },
                    data: ExprData::BinaryExpr {
                        x,
                        op_pos,
                        op: Token::Eq,
                        y,
                    },
                });
            }

            args.push(x);
        }
        let args = self.bump.alloc_slice_copy(&args.into_boxed_slice());
        Ok(args)
    }

    // suite is typically what follows a COLON (e.g. after DEF or FOR).
    // suite = simple_stmt | NEWLINE INDENT stmt+ OUTDENT
    fn parse_suite(&mut self) -> Result<&'b [StmtRef<'b>]> {
        let mut stmts = vec![]; // []Stmt
        if self.tok.kind == Token::Newline {
            self.next_token()?; // consume NEWLINE
            self.consume(Token::Indent)?;
            while self.tok.kind != Token::Outdent && self.tok.kind != Token::Eof {
                self.parse_stmt(&mut stmts)?;
            }
            self.consume(Token::Outdent)?;
        } else {
            self.parse_simple_stmt(&mut stmts, true)?;
        }
        let stmts = self.bump.alloc_slice_copy(&stmts.into_boxed_slice());
        Ok(&*stmts)
    }

    // expr = test (OP test)*
    // Uses precedence climbing; see http://www.engr.mun.ca/~theo/Misc/exp_parsing.htm#climbing.
    fn parse_binop_expr(&mut self, prec: usize) -> Result<ExprRef<'b>> {
        let mut x = self.parse_test_prec(prec + 1)?;
        let mut first = true;
        loop {
            if self.tok.kind == Token::Not {
                self.next_token()?; // consume NOT
                                    // In this context, NOT must be followed by IN.
                                    // Replace NOT IN by a single NOT_IN token.
                if self.tok.kind != Token::In {
                    return Err(anyhow!("{} got {}, want in", self.pos, self.tok.kind));
                }
                self.tok.kind = Token::NotIn;
            }

            // Binary operator of specified precedence?
            let op_prec = self.tok.kind.precedence();
            if op_prec.is_none() || op_prec.unwrap() < prec {
                let x = self.bump.alloc(x);
                return Ok(*x);
            }
            // Comparisons are non-associative.
            if !first && op_prec == Token::Eq.precedence() {
                match &x.data {
                    ExprData::BinaryExpr { op, .. } => {
                        return Err(anyhow!(
                            "{} {} does not associate with {} (use parens)",
                            self.pos,
                            op,
                            self.tok.kind
                        ))
                    }
                    _ => unreachable!(),
                }
            }
            let op_prec = op_prec.unwrap();

            let op = self.tok.kind.clone();
            let op_pos = self.next_token()?;
            let y = self.parse_test_prec(op_prec + 1)?;
            let binary_expr = self.bump.alloc(Expr {
                span: Span {
                    start: x.span.start.clone(),
                    end: y.span.end.clone(),
                },
                data: ExprData::BinaryExpr { op_pos, op, x, y },
            });
            x = &*binary_expr;
            first = false;
        }
    }

    // primary_with_suffix = primary
    //
    //	| primary '.' IDENT
    //	| primary slice_suffix
    //	| primary call_suffix
    fn parse_primary_with_suffix(&mut self) -> Result<ExprRef<'b>> {
        let mut x = self.parse_primary()?;
        loop {
            match self.tok.kind {
                Token::Dot => {
                    let dot = self.next_token()?;
                    let id = self.parse_ident()?;
                    let name_pos = self.pos.clone();
                    let dot_expr = self.bump.alloc(Expr {
                        span: Span {
                            start: x.span.start.clone(),
                            end: name_pos.clone(),
                        },
                        data: ExprData::DotExpr {
                            dot,
                            x,
                            name: id,
                            name_pos,
                        },
                    });
                    x = &*dot_expr;
                }
                Token::LBrack => x = self.parse_slice_suffix(x)?,
                Token::LParen => x = self.parse_call_suffix(x)?,
                _ => return Ok(x),
            }
        }
    }

    // slice_suffix = '[' expr? ':' expr?  ':' expr? ']'
    fn parse_slice_suffix(&mut self, x: ExprRef<'b>) -> Result<ExprRef<'b>> {
        let lbrack = self.next_token()?;
        let mut lo: Option<&Expr> = None;
        if self.tok.kind != Token::Colon {
            let y = self.parse_expr(false)?;

            // index x[y]
            if self.tok.kind == Token::RBrack {
                let rbrack = self.next_token()?;
                let index_expr = self.bump.alloc(Expr {
                    span: Span {
                        start: x.span.start.clone(),
                        end: rbrack.clone(),
                    },
                    data: ExprData::IndexExpr {
                        x,
                        lbrack,
                        y,
                        rbrack,
                    },
                });
                return Ok(index_expr);
            }

            lo = Some(y)
        }
        let mut hi: Option<&Expr> = None; //,
                                          // slice or substring x[lo:hi:step]
        if self.tok.kind == Token::Colon {
            self.next_token()?;
            if self.tok.kind != Token::Colon && self.tok.kind != Token::RBrack {
                hi = Some(self.parse_test()?);
            }
        }
        let mut step: Option<&Expr> = None;
        if self.tok.kind == Token::Colon {
            self.next_token()?;
            if self.tok.kind != Token::RBrack {
                step = Some(self.parse_test()?);
            }
        }
        let rbrack = self.consume(Token::RBrack)?;
        let slice_expr = self.bump.alloc(Expr {
            span: Span {
                start: lbrack.clone(),
                end: rbrack.clone(),
            },
            data: ExprData::SliceExpr {
                x,
                lbrack,
                lo,
                hi,
                step,
                rbrack,
            },
        });
        Ok(slice_expr)
    }
}

fn terminates_expr_list(tok: &Token) -> bool {
    use Token::*;
    matches!(tok, Eof | Newline | Eq | RBrace | RBrack | RParen | Semi)
}

#[cfg(test)]
mod test {

    use std::rc::Rc;

    use super::*;
    struct TestCase {
        input: &'static str,
        want: &'static str, //ExprRef<'b>,
    }

    #[test]
    pub fn test_expr_parse_trees() {
        let bump = super::Bump::new();
        let test_cases = vec![
            TestCase {
                input: "print(1)",
                want: "(CallExpr Fn=print Args=(1,))",
            },
            TestCase {
                input: "x + 1",
                want: "(BinaryExpr X=x Op=+ Y=1)",
            },
            TestCase {
                input: "[x for x in y]",
                want: "(Comprehension Body=x Clauses=((ForClause Vars=x X=y),))",
            },
            TestCase {
                input: "[x for x in (a if b else c)]",
                want: "(Comprehension Body=x Clauses=((ForClause Vars=x X=(ParenExpr X=(CondExpr Cond=b True=a False=c))),))",
            },
            TestCase{
                input:"x[i].f(42)",
                want: "(CallExpr Fn=(DotExpr X=(IndexExpr X=x Y=i) Name=f) Args=(42,))"
            },
            TestCase{
                input:"x.f()",
                want: "(CallExpr Fn=(DotExpr X=x Name=f) Args=())",
            },
            TestCase{
                input:"x+y*z",
                want: "(BinaryExpr X=x Op=+ Y=(BinaryExpr X=y Op=* Y=z))",
            },
            TestCase{
                input:"x%y-z",
                want: "(BinaryExpr X=(BinaryExpr X=x Op=% Y=y) Op=- Y=z)",
            },
            TestCase{
                input:"a + b not in c",
                want: "(BinaryExpr X=(BinaryExpr X=a Op=+ Y=b) Op=not in Y=c)",
            },
            TestCase{
                input:"lambda x, *args, **kwargs: None",
                want: "(LambdaExpr Params=(x,(UnaryExpr Op=* X=args),(UnaryExpr Op=** X=kwargs),) Body=None)",
            },
            TestCase{ input:r#"{"one": 1}"#,
                want: r#"(DictExpr List=((DictEntry Key="one" Value=1),))"#
            },
            TestCase{ input:"a[i]",
                want: "(IndexExpr X=a Y=i)"},
            TestCase{ input:"a[i:]",
                want: "(SliceExpr X=a Lo=i)"},
                TestCase{ input:"a[:j]",
                want: "(SliceExpr X=a Hi=j)"},
            TestCase{ input:"a[::]",
                want: "(SliceExpr X=a)"},
            TestCase{ input:"a[::k]",
                want: "(SliceExpr X=a Step=k)"},
                TestCase{ input:"[]",
                want: "(ListExpr List=())"},
            TestCase{ input:"[1]",
                want: "(ListExpr List=(1,))"},
            TestCase{ input:"[1,]",
                want: "(ListExpr List=(1,))"},
            TestCase{ input:"[1, 2]",
                want: "(ListExpr List=(1,2,))"},
                TestCase{ input:"()",
                want: "(TupleExpr List=())"},
            TestCase{ input:"(4,)",
                want: "(ParenExpr X=(TupleExpr List=(4,)))"},
            TestCase{ input:"(4)",
                want: "(ParenExpr X=4)"},
                TestCase{ input:"(4, 5)",
                want: "(ParenExpr X=(TupleExpr List=(4,5,)))"},
            TestCase{ input:"1, 2, 3",
                want: "(TupleExpr List=(1,2,3,))"},
            //TestCase{ input:"1, 2,",
            //    "unparenthesized tuple with trailing comma"},
            TestCase{
                input:"{}",
                want: "(DictExpr List=())"},
            TestCase{
                input:r#"{"a": 1}"#,
                want: r#"(DictExpr List=((DictEntry Key="a" Value=1),))"#},
            TestCase{
                input:r#"{"a": 1,}"#,
                want: r#"(DictExpr List=((DictEntry Key="a" Value=1),))"#},
            TestCase{
                input:r#"{"a": 1, "b": 2}"#,
                want: r#"(DictExpr List=((DictEntry Key="a" Value=1),(DictEntry Key="b" Value=2),))"#},
            TestCase{ input:"{x: y for (x, y) in z}",
                want: "(Comprehension Curly Body=(DictEntry Key=x Value=y) Clauses=((ForClause Vars=(ParenExpr X=(TupleExpr List=(x,y,))) X=z),))"},
            TestCase{ input:"{x: y for a in b if c}",
                want: "(Comprehension Curly Body=(DictEntry Key=x Value=y) Clauses=((ForClause Vars=a X=b),(IfClause Cond=c),))"},
                TestCase{ input:"-1 + +2",
                want: "(BinaryExpr X=(UnaryExpr Op=- X=1) Op=+ Y=(UnaryExpr Op=+ X=2))"},
                TestCase{ input:r#""foo" + "bar""#,
                want: r#"(BinaryExpr X="foo" Op=+ Y="bar")"#},
            TestCase{ input:"-1 * 2", // prec(unary -) > prec(binary *)
                want: "(BinaryExpr X=(UnaryExpr Op=- X=1) Op=* Y=2)"},
            TestCase{ input:"-x[i]", // prec(unary -) < prec(x[i])
                want: "(UnaryExpr Op=- X=(IndexExpr X=x Y=i))"},
                TestCase{ input:"a | b & c | d", // prec(|) < prec(&)
                want: "(BinaryExpr X=(BinaryExpr X=a Op=| Y=(BinaryExpr X=b Op=& Y=c)) Op=| Y=d)"},
            TestCase{ input:"a or b and c or d",
                want: "(BinaryExpr X=(BinaryExpr X=a Op=or Y=(BinaryExpr X=b Op=and Y=c)) Op=or Y=d)"},
            TestCase{ input:"a and b or c and d",
                want: "(BinaryExpr X=(BinaryExpr X=a Op=and Y=b) Op=or Y=(BinaryExpr X=c Op=and Y=d))"},
                TestCase{ input:"f(1, x=y)",
                want: "(CallExpr Fn=f Args=(1,(BinaryExpr X=x Op== Y=y),))"},
            TestCase{ input:"f(*args, **kwargs)",
                want: "(CallExpr Fn=f Args=((UnaryExpr Op=* X=args),(UnaryExpr Op=** X=kwargs),))"},
            TestCase{ input:"lambda *args, *, x=1, **kwargs: 0",
                want: "(LambdaExpr Params=((UnaryExpr Op=* X=args),(UnaryExpr Op=*),(BinaryExpr X=x Op== Y=1),(UnaryExpr Op=** X=kwargs),) Body=0)"},
                TestCase{ input:"lambda *, a, *b: 0",
                want: "(LambdaExpr Params=((UnaryExpr Op=*),a,(UnaryExpr Op=* X=b),) Body=0)"},
            TestCase{ input:"a if b else c",
                want: "(CondExpr Cond=b True=a False=c)"},
                TestCase{ input:"a and not b",
                want: "(BinaryExpr X=a Op=and Y=(UnaryExpr Op=not X=b))"},
                TestCase{ input:"[e for x in y if cond1 if cond2]",
                want: "(Comprehension Body=e Clauses=((ForClause Vars=x X=y),(IfClause Cond=cond1),(IfClause Cond=cond2),))"}, // github.com/google/skylark/issues/53
                ];
        for test_case in test_cases {
            match super::parse_expr(&bump, &"foo.star", test_case.input, Mode::Plain) {
                Ok(expr) => {
                    let s = format!("{}", expr.data);
                    assert_eq!(s, test_case.want)
                }
                Err(msg) => assert!(false, "{}", msg),
            }
        }
    }

    #[test]
    fn test_stmt_parse_trees() {
        let bump = super::Bump::new();
        let test_cases = vec![
            TestCase {
                input: "print(1)",
                want: "(ExprStmt X=(CallExpr Fn=print Args=(1,)))",
            },
            TestCase {
                input: "return 1, 2",
                want: "(ReturnStmt Result=(TupleExpr List=(1,2,)))",
            },
            TestCase {
                input: "return",
                want: "(ReturnStmt)",
            },
            TestCase {
                input: r#"for i in "abc": break"#,
                want: r#"(ForStmt Vars=i X="abc" Body=((BranchStmt Token=break),))"#,
            },
            TestCase {
                input: r#"for i in "abc": continue"#,
                want: r#"(ForStmt Vars=i X="abc" Body=((BranchStmt Token=continue),))"#,
            },
            TestCase {
                input: "for x, y in z: pass",
                want: "(ForStmt Vars=(TupleExpr List=(x,y,)) X=z Body=((BranchStmt Token=pass),))",
            },
            TestCase {
                input: "if True: pass",
                want: "(IfStmt Cond=True True=((BranchStmt Token=pass),) False=())",
            },
            TestCase {
                input: "if True: break",
                want: "(IfStmt Cond=True True=((BranchStmt Token=break),) False=())",
            },
            TestCase {
                input: "if True: continue",
                want: "(IfStmt Cond=True True=((BranchStmt Token=continue),) False=())",
            },
            TestCase{
                input: "if True: pass
else:
                  pass",
                          want: "(IfStmt Cond=True True=((BranchStmt Token=pass),) False=((BranchStmt Token=pass),))",
              },
              TestCase{
                  input:"if a: pass\nelif b: pass\nelse: pass",
                  want: "(IfStmt Cond=a True=((BranchStmt Token=pass),) False=((IfStmt Cond=b True=((BranchStmt Token=pass),) False=((BranchStmt Token=pass),)),))",
              },
              TestCase{
                input: "x, y = 1, 2",
                want: "(AssignStmt Op== LHS=(TupleExpr List=(x,y,)) RHS=(TupleExpr List=(1,2,)))",
              },
              TestCase{
                input: "x[i] = 1",
                want: "(AssignStmt Op== LHS=(IndexExpr X=x Y=i) RHS=1)",
              },
              TestCase{
                input: "x.f = 1",
                want: "(AssignStmt Op== LHS=(DotExpr X=x Name=f) RHS=1)",
              },
              TestCase{
                input: "(x, y) = 1",
                want: "(AssignStmt Op== LHS=(ParenExpr X=(TupleExpr List=(x,y,))) RHS=1)",
              },
              TestCase{
                input: r#"load("", "a", b="c")"#,
                want: r#"(LoadStmt From=(a,c,) To=(a,b,))"#,
              },
              TestCase{
                input: r#"if True: load("", "a", b="c")"#, // load needn't be at toplevel
                want: "(IfStmt Cond=True True=((LoadStmt From=(a,c,) To=(a,b,)),) False=())",
              },
              TestCase{
                input: "def f(x, *args, **kwargs):
  pass",
                want: "(DefStmt Name=f Params=(x,(UnaryExpr Op=* X=args),(UnaryExpr Op=** X=kwargs),) Body=((BranchStmt Token=pass),))",
              },
              TestCase{
                input: "def f(**kwargs, *args): pass",
                want: "(DefStmt Name=f Params=((UnaryExpr Op=** X=kwargs),(UnaryExpr Op=* X=args),) Body=((BranchStmt Token=pass),))",
              },
              TestCase{
                input: "def f(a, b, c=d): pass",
                want: "(DefStmt Name=f Params=(a,b,(BinaryExpr X=c Op== Y=d),) Body=((BranchStmt Token=pass),))",
              },
              TestCase{
                input: "def f(a, b=c, d): pass",
                want: "(DefStmt Name=f Params=(a,(BinaryExpr X=b Op== Y=c),d,) Body=((BranchStmt Token=pass),))",
              }, // TODO: fix this
              TestCase{
                input: r#"def f():
    def g():
        pass
    pass
def h():
    pass
"#,
                want: "(DefStmt Name=f Params=() Body=((DefStmt Name=g Params=() Body=((BranchStmt Token=pass),)),(BranchStmt Token=pass),))",
              },
              TestCase{
                input:"f();g()",
                want: "(ExprStmt X=(CallExpr Fn=f Args=()))",
              },
              TestCase{
                input:"f();",
                want: "(ExprStmt X=(CallExpr Fn=f Args=()))",
              },
              TestCase{
                input:"f();g()\n",
                want: "(ExprStmt X=(CallExpr Fn=f Args=()))",
              },
              TestCase{
                input:"f();\n",
                want: "(ExprStmt X=(CallExpr Fn=f Args=()))",
              },
        ];
        for test_case in test_cases {
            match super::parse(&bump, &"foo.star", test_case.input, Mode::Plain) {
                Ok(file_unit) if file_unit.stmts.len() >= 1 => {
                    let s = format!("{}", file_unit.stmts[0].data);
                    assert_eq!(s, test_case.want)
                }
                Ok(_) => assert!(false, "empty?"),
                Err(msg) => assert!(false, "{}", msg),
            }
        }
    }

    #[test]
    fn test_retain_comments() -> Result<()> {
        let bump = super::Bump::new();
        let input = "# Hello world
foo() #Suffix
# Goodbye world";
        let res = super::parse(&bump, &"foo.star", input, Mode::RetainComments)?;
        assert_eq!(
            res.line_comments,
            vec![
                Comment {
                    start: Position {
                        path: Rc::new("foo.star".to_string()),
                        line: 1,
                        col: 1
                    },
                    text: "# Hello world".to_string()
                },
                Comment {
                    start: Position {
                        path: Rc::new("foo.star".to_string()),
                        line: 3,
                        col: 1
                    },
                    text: "# Goodbye world".to_string()
                }
            ]
        );
        assert_eq!(
            res.suffix_comments,
            vec![Comment {
                start: Position {
                    path: Rc::new("foo.star".to_string()),
                    line: 2,
                    col: 7
                },
                text: "#Suffix".to_string()
            }]
        );
        Ok(())
    }
}
