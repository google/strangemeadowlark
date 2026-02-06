// Copyright 2024 Google LLC
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

use crate::{
    scan::Position, Clause, Expr, ExprData, FileUnit, Literal, Stmt, StmtData,
};
use pretty::RcDoc;

const INDENT: isize = 4;

struct PrinterState<'a> {
    file: &'a FileUnit<'a>,
    last_line_comment: usize,
    last_suffix_comment: usize,
}

impl<'a> PrinterState<'a> {
    fn new(file: &'a FileUnit<'a>) -> Self {
        Self {
            file,
            last_line_comment: 0,
            last_suffix_comment: 0,
        }
    }

    fn comments_before(&mut self, pos: Position) -> RcDoc<'a, ()> {
        let mut docs = Vec::new();
        while self.last_line_comment < self.file.line_comments.len() {
            let c = self.file.line_comments[self.last_line_comment];
            if c.start.is_before(&pos) {
                docs.push(RcDoc::text(c.text));
                docs.push(RcDoc::hardline());
                self.last_line_comment += 1;
            } else {
                break;
            }
        }
        RcDoc::concat(docs)
    }

    fn suffix_comment(&mut self, pos: Position) -> RcDoc<'a, ()> {
        while self.last_suffix_comment < self.file.suffix_comments.len() {
            let c = self.file.suffix_comments[self.last_suffix_comment];
            if c.start.line == pos.line {
                self.last_suffix_comment += 1;
                // Buildifier uses two spaces before suffix comment if it's on the same line as code.
                return RcDoc::space().append(RcDoc::space()).append(RcDoc::text(c.text));
            } else if c.start.is_before(&pos) {
                self.last_suffix_comment += 1;
            } else {
                break;
            }
        }
        RcDoc::nil()
    }
}

pub fn pretty<'ast>(file: &'ast FileUnit<'ast>) -> String {
    let mut w = Vec::new();
    let mut state = PrinterState::new(file);
    let doc = pretty_file(file, &mut state);
    doc.render(8000, &mut w).unwrap();
    let mut s = String::from_utf8(w).unwrap();
    if !s.is_empty() && !s.ends_with('\n') {
        s.push('\n');
    }
    s
}

fn pretty_file<'a>(file: &'a FileUnit<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    let mut loads = Vec::new();
    let mut others = Vec::new();
    for &stmt in file.stmts {
        if matches!(stmt.data, StmtData::LoadStmt { .. }) {
            loads.push(stmt);
        } else {
            others.push(stmt);
        }
    }

    loads.sort_by(|a, b| {
        let a_mod = get_load_module(a);
        let b_mod = get_load_module(b);
        a_mod.cmp(b_mod)
    });

    let mut docs = Vec::new();
    
    for l in loads {
        docs.push(pretty_stmt(l, state));
    }
    
    if !docs.is_empty() && !others.is_empty() {
        docs.push(RcDoc::nil());
    }

    for (i, &stmt) in others.iter().enumerate() {
        if i > 0 {
            if matches!(stmt.data, StmtData::DefStmt { .. }) {
                docs.push(RcDoc::nil());
            }
        }
        docs.push(pretty_stmt(stmt, state));
    }
    
    // Print remaining line comments.
    if state.last_line_comment < state.file.line_comments.len() && !docs.is_empty() {
        docs.push(RcDoc::nil());
    }
    while state.last_line_comment < state.file.line_comments.len() {
        docs.push(RcDoc::text(state.file.line_comments[state.last_line_comment].text));
        state.last_line_comment += 1;
    }

    RcDoc::intersperse(docs, RcDoc::hardline())
}

fn get_load_module<'a>(stmt: &'a Stmt<'a>) -> &'a str {
    if let StmtData::LoadStmt { module, .. } = &stmt.data {
        if let ExprData::Literal { token: Literal::String(s), .. } = &module.data {
            return s;
        }
    }
    ""
}

fn pretty_stmt<'a>(stmt: &'a Stmt<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    let mut doc = state.comments_before(stmt.span.start);
    
    let content = match &stmt.data {
        StmtData::AssignStmt { op, lhs, rhs, .. } => pretty_expr(lhs, state)
            .append(RcDoc::space())
            .append(RcDoc::as_string(op))
            .append(RcDoc::space())
            .append(pretty_expr(rhs, state)),
        StmtData::BranchStmt { token, .. } => RcDoc::as_string(token),
        StmtData::DefStmt {
            name, params, body, ..
        } => {
            let mut d = RcDoc::text("def ")
                .append(RcDoc::text(name.name))
                .append(RcDoc::text("("));
            if !params.is_empty() {
                d = d.append(
                    RcDoc::line_()
                        .append(RcDoc::intersperse(
                            params.iter().map(|p| pretty_expr(p, state)),
                            RcDoc::text(",").append(RcDoc::line()),
                        ))
                        .nest(INDENT)
                        .append(RcDoc::line_()),
                ).group();
            }
            d = d.append(RcDoc::text("):"));
            let body_docs = body.iter().map(|s| pretty_stmt(s, state));
            d.append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(body_docs, RcDoc::hardline()))
                    .nest(INDENT)
            )
        }
        StmtData::ExprStmt { x } => pretty_expr(x, state),
        StmtData::ForStmt { vars, x, body, .. } => {
            let d = RcDoc::text("for ")
                .append(pretty_expr_no_parens(vars, state))
                .append(RcDoc::text(" in "))
                .append(pretty_expr(x, state))
                .append(RcDoc::text(":"));
            let body_docs = body.iter().map(|s| pretty_stmt(s, state));
            d.append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(body_docs, RcDoc::hardline()))
                    .nest(INDENT)
            )
        }
        StmtData::WhileStmt { cond, body, .. } => {
            let d = RcDoc::text("while ")
                .append(pretty_expr(cond, state))
                .append(RcDoc::text(":"));
            let body_docs = body.iter().map(|s| pretty_stmt(s, state));
            d.append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(body_docs, RcDoc::hardline()))
                    .nest(INDENT)
            )
        }
        StmtData::IfStmt {
            cond,
            then_arm,
            else_arm,
            ..
        } => {
            let mut d = RcDoc::text("if ")
                .append(pretty_expr(cond, state))
                .append(RcDoc::text(":"));
            let then_docs = then_arm.iter().map(|s| pretty_stmt(s, state));
            d = d.append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(then_docs, RcDoc::hardline()))
                    .nest(INDENT)
            );
            if !else_arm.is_empty() {
                d = d.append(RcDoc::hardline()).append(RcDoc::text("else:"));
                let else_docs = else_arm.iter().map(|s| pretty_stmt(s, state));
                d = d.append(
                    RcDoc::hardline()
                        .append(RcDoc::intersperse(else_docs, RcDoc::hardline()))
                        .nest(INDENT)
                );
            }
            d
        }
        StmtData::LoadStmt {
            module, from, to, ..
        } => {
            let mut items: Vec<_> = from.iter().zip(to.iter()).collect();
            items.sort_by(|a, b| a.0.name.cmp(b.0.name));
            
            let mut d = RcDoc::text("load(").append(pretty_expr(module, state));
            for (f, t) in items {
                d = d.append(RcDoc::text(", "));
                if f.name == t.name {
                    d = d.append(RcDoc::text(format!("{:?}", f.name)));
                } else {
                    d = d.append(RcDoc::text(format!("{} = {:?}", t.name, f.name)));
                }
            }
            d.append(RcDoc::text(")"))
        }
        StmtData::ReturnStmt { result, .. } => {
            let mut d = RcDoc::text("return");
            if let Some(r) = result {
                d = d.append(RcDoc::space()).append(pretty_expr(r, state));
            }
            d
        }
    };
    
    doc = doc.append(content);
    doc.append(state.suffix_comment(stmt.span.start))
}

fn pretty_expr<'a>(expr: &'a Expr<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    match &expr.data {
        ExprData::TupleExpr { list, .. } => {
            let mut doc = RcDoc::text("(");
            if !list.is_empty() {
                doc = doc
                    .append(
                        RcDoc::line_()
                            .append(RcDoc::intersperse(
                                list.iter().map(|e| pretty_expr(e, state)),
                                RcDoc::text(",").append(RcDoc::line()),
                            ))
                            .nest(INDENT)
                            .append(RcDoc::line_()),
                    )
                    .group();
                if list.len() == 1 {
                    doc = doc.append(RcDoc::text(","));
                }
            }
            doc.append(RcDoc::text(")"))
        }
        _ => pretty_expr_internal(expr, state),
    }
}

fn pretty_expr_no_parens<'a>(expr: &'a Expr<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    match &expr.data {
        ExprData::TupleExpr { list, .. } => {
            if list.is_empty() {
                RcDoc::text("()")
            } else {
                RcDoc::intersperse(
                    list.iter().map(|e| pretty_expr(e, state)),
                    RcDoc::text(", "),
                )
            }
        }
        _ => pretty_expr_internal(expr, state),
    }
}

fn pretty_expr_internal<'a>(expr: &'a Expr<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    match &expr.data {
        ExprData::BinaryExpr { x, op, y, .. } => pretty_expr(x, state)
            .append(RcDoc::space())
            .append(RcDoc::as_string(op))
            .append(RcDoc::space())
            .append(pretty_expr(y, state)),
        ExprData::CallExpr { func, args, .. } => {
            let mut doc = pretty_expr(func, state).append(RcDoc::text("("));
            if !args.is_empty() {
                doc = doc
                    .append(
                        RcDoc::line_()
                            .append(RcDoc::intersperse(
                                args.iter().map(|a| pretty_expr(a, state)),
                                RcDoc::text(",").append(RcDoc::line()),
                            ))
                            .nest(INDENT)
                            .append(RcDoc::line_()),
                    )
                    .group();
            }
            doc.append(RcDoc::text(")"))
        }
        ExprData::Comprehension {
            curly,
            body,
            clauses,
            ..
        } => {
            let mut doc = RcDoc::text(if *curly { "{" } else { "[" }).append(pretty_expr(body, state));
            for clause in *clauses {
                doc = doc.append(pretty_clause(clause, state));
            }
            doc.append(RcDoc::text(if *curly { "}" } else { "]" }))
        }
        ExprData::CondExpr {
            cond,
            then_arm,
            else_arm,
            ..
        } => pretty_expr(then_arm, state)
            .append(RcDoc::text(" if "))
            .append(pretty_expr(cond, state))
            .append(RcDoc::text(" else "))
            .append(pretty_expr(else_arm, state)),
        ExprData::DictEntry { key, value, .. } => {
            pretty_expr(key, state).append(RcDoc::text(": ")).append(pretty_expr(value, state))
        }
        ExprData::DictExpr { list, .. } => {
            let mut doc = RcDoc::text("{");
            if !list.is_empty() {
                doc = doc
                    .append(
                        RcDoc::line_()
                            .append(RcDoc::intersperse(
                                list.iter().map(|e| pretty_expr(e, state)),
                                RcDoc::text(",").append(RcDoc::line()),
                            ))
                            .nest(INDENT)
                            .append(RcDoc::line_()),
                    )
                    .group();
            }
            doc.append(RcDoc::text("}"))
        }
        ExprData::DotExpr { x, name, .. } => pretty_expr(x, state).append(RcDoc::text(".")).append(RcDoc::text(name.name)),
        ExprData::Ident(ident) => RcDoc::text(ident.name),
        ExprData::IndexExpr { x, y, .. } => pretty_expr(x, state)
            .append(RcDoc::text("["))
            .append(pretty_expr(y, state))
            .append(RcDoc::text("]")),
        ExprData::LambdaExpr { params, body, .. } => {
            let mut doc = RcDoc::text("lambda");
            if !params.is_empty() {
                doc = doc.append(RcDoc::space()).append(RcDoc::intersperse(
                    params.iter().map(|p| pretty_expr(p, state)),
                    RcDoc::text(", "),
                ));
            }
            doc.append(RcDoc::text(": ")).append(pretty_expr(body, state))
        }
        ExprData::ListExpr { list, .. } => {
            let mut doc = RcDoc::text("[");
            if !list.is_empty() {
                doc = doc
                    .append(
                        RcDoc::line_()
                            .append(RcDoc::intersperse(
                                list.iter().map(|e| pretty_expr(e, state)),
                                RcDoc::text(",").append(RcDoc::line()),
                            ))
                            .nest(INDENT)
                            .append(RcDoc::line_()),
                    )
                    .group();
            }
            doc.append(RcDoc::text("]"))
        }
        ExprData::Literal { token, .. } => RcDoc::as_string(token),
        ExprData::ParenExpr { x, .. } => RcDoc::text("(").append(pretty_expr(x, state)).append(RcDoc::text(")")),
        ExprData::SliceExpr {
            x, lo, hi, step, ..
        } => {
            let mut doc = pretty_expr(x, state).append(RcDoc::text("["));
            if let Some(lo) = lo {
                doc = doc.append(pretty_expr(lo, state));
            }
            doc = doc.append(RcDoc::text(":"));
            if let Some(hi) = hi {
                doc = doc.append(pretty_expr(hi, state));
            }
            if let Some(step) = step {
                doc = doc.append(RcDoc::text(":")).append(pretty_expr(step, state));
            }
            doc.append(RcDoc::text("]"))
        }
        ExprData::TupleExpr { .. } => unreachable!("TupleExpr handled by pretty_expr / pretty_expr_no_parens"),
        ExprData::UnaryExpr { op, x, .. } => {
            let mut doc = RcDoc::as_string(op);
            if let Some(x) = x {
                if *op == crate::token::Token::Not {
                    doc = doc.append(RcDoc::space());
                }
                doc = doc.append(pretty_expr(x, state));
            }
            doc
        }
    }
}

fn pretty_clause<'a>(clause: &'a Clause<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    match clause {
        Clause::ForClause { vars, x, .. } => RcDoc::space()
            .append(RcDoc::text("for "))
            .append(pretty_expr_no_parens(vars, state))
            .append(RcDoc::text(" in "))
            .append(pretty_expr(x, state)),
        Clause::IfClause { cond, .. } => RcDoc::space()
            .append(RcDoc::text("if "))
            .append(pretty_expr(cond, state)),
    }
}
