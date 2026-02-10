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

use crate::{Clause, Expr, ExprData, FileUnit, Literal, Stmt, StmtData};
use pretty::RcDoc;

const INDENT: isize = 4;

struct PrinterState<'a> {
    file: &'a FileUnit<'a>,
}

impl<'a> PrinterState<'a> {
    fn new(file: &'a FileUnit<'a>) -> Self {
        Self { file }
    }

    fn comments_before(&self, id: usize, stmt_start_line: u32) -> RcDoc<'a, ()> {
        if let Some(indices) = self.file.comments_before.get(&id) {
            let mut docs = Vec::new();
            let mut last_line = 0;
            for &idx in indices {
                let comment = self.file.line_comments[idx];
                docs.push(RcDoc::text(comment.text));
                docs.push(RcDoc::hardline());
                last_line = comment.start.line;
            }
            // If there is a gap between the last comment and the statement, add a blank line.
            // But only if we actually printed comments.
            if !docs.is_empty() && stmt_start_line > last_line + 1 {
                docs.push(RcDoc::hardline());
            }
            RcDoc::concat(docs)
        } else {
            RcDoc::nil()
        }
    }

    fn has_suffix_comment(&self, id: usize) -> bool {
        self.file.comments_suffix.contains_key(&id)
    }

    fn suffix_comment(&self, id: usize) -> RcDoc<'a, ()> {
        if let Some(indices) = self.file.comments_suffix.get(&id) {
            let mut docs = Vec::new();
            for &idx in indices {
                // Buildifier uses two spaces before suffix comment if it's on the same line as code.
                docs.push(
                    RcDoc::space()
                        .append(RcDoc::space())
                        .append(RcDoc::text(self.file.suffix_comments[idx].text)),
                );
            }
            RcDoc::concat(docs)
        } else {
            RcDoc::nil()
        }
    }
}

pub fn pretty<'ast>(file: &'ast FileUnit<'ast>) -> String {
    let mut w = Vec::new();
    let mut state = PrinterState::new(file);
    let doc = pretty_file(file, &mut state);
    doc.render(80, &mut w).unwrap();
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

    // Sort loads by module name.
    loads.sort_by(|a, b| {
        let a_mod = get_load_module(a);
        let b_mod = get_load_module(b);
        a_mod.cmp(b_mod)
    });

    let mut docs = Vec::new();

    if file.stmts.is_empty() {
        for c in file.line_comments {
            docs.push(RcDoc::text(c.text));
            docs.push(RcDoc::hardline());
        }
    }

    for (i, l) in loads.iter().enumerate() {
        if i > 0
            && l.span.start.line > loads[i - 1].span.end.line + 1 {
                docs.push(RcDoc::nil());
            }
        docs.push(pretty_stmt(l, state));
    }

    if !loads.is_empty() && !others.is_empty() {
        docs.push(RcDoc::nil());
    }

    for (i, &stmt) in others.iter().enumerate() {
        if i > 0 {
            let prev = others[i - 1];
            if stmt.span.start.line > prev.span.end.line + 1 {
                docs.push(RcDoc::nil());
            } else if matches!(stmt.data, StmtData::DefStmt { .. }) {
                docs.push(RcDoc::nil());
            }
        }
        docs.push(pretty_stmt(stmt, state));
    }

    // Trailing comments.
    if let Some(&last_stmt) = others.last().or(loads.last())
        && let Some(indices) = file.comments_after.get(&last_stmt.id.0) {
            for &idx in indices {
                docs.push(RcDoc::nil());
                docs.push(RcDoc::text(file.line_comments[idx].text));
            }
        }

    RcDoc::intersperse(docs, RcDoc::hardline())
}

fn get_load_module<'a>(stmt: &'a Stmt<'a>) -> &'a str {
    if let StmtData::LoadStmt { module, .. } = &stmt.data
        && let ExprData::Literal {
            token: Literal::String(s),
            ..
        } = &module.data
    {
        return s;
    }
    ""
}

fn pretty_stmt<'a>(stmt: &'a Stmt<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    let doc_before = state.comments_before(stmt.id.0, stmt.span.start.line);

    let content = match &stmt.data {
        StmtData::AssignStmt { op, lhs, rhs, .. } => pretty_expr(lhs, state)
            .append(RcDoc::space())
            .append(RcDoc::as_string(op))
            .append(RcDoc::space())
            .append(pretty_expr(rhs, state)),
        StmtData::BranchStmt { token, .. } => RcDoc::as_string(token),
        StmtData::DefStmt {
            name,
            params,
            body,
            lparen,
            rparen,
            ..
        } => {
            let mut d = RcDoc::text("def ").append(RcDoc::text(name.name));

            if params.is_empty() {
                d = d.append(RcDoc::text("():"));
            } else {
                let items: Vec<_> = params
                    .iter()
                    .map(|p| {
                        let (content, comment) = pretty_expr_split(p, state);
                        (content, comment)
                    })
                    .collect();
                let any_comment = params.iter().any(|p| state.has_suffix_comment(p.id.0));
                let force_multiline = rparen.line > lparen.line;

                d = d.append(pretty_sequence(
                    items,
                    any_comment,
                    force_multiline,
                    false,
                    "(",
                    ")",
                ));
                d = d.append(RcDoc::text(":"));
            }

            let body_docs = body.iter().map(|s| pretty_stmt(s, state));
            d.append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(body_docs, RcDoc::hardline()))
                    .nest(INDENT),
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
                    .nest(INDENT),
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
                    .nest(INDENT),
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
                    .nest(INDENT),
            );
            if !else_arm.is_empty() {
                d = d.append(RcDoc::hardline()).append(RcDoc::text("else:"));
                let else_docs = else_arm.iter().map(|s| pretty_stmt(s, state));
                d = d.append(
                    RcDoc::hardline()
                        .append(RcDoc::intersperse(else_docs, RcDoc::hardline()))
                        .nest(INDENT),
                );
            }
            d
        }
        StmtData::LoadStmt {
            module, from, to, ..
        } => {
            let mut items: Vec<_> = from.iter().zip(to.iter()).collect();
            items.sort_by(|a, b| a.0.name.cmp(b.0.name));

            let mut args = Vec::new();
            let (mod_doc, mod_comment) = pretty_expr_split(module, state);
            args.push((mod_doc, mod_comment));

            for (f, t) in items {
                let mut item_doc = RcDoc::nil();
                if f.name == t.name {
                    item_doc = item_doc.append(RcDoc::text(format!("{:?}", f.name)));
                } else {
                    item_doc = item_doc.append(RcDoc::text(format!("{} = {:?}", t.name, f.name)));
                }
                args.push((item_doc, RcDoc::nil()));
            }

            let force_multiline = stmt.span.end.line > stmt.span.start.line;
            // any_comment check for module only, as others don't have IDs
            let any_comment = state.has_suffix_comment(module.id.0);

            RcDoc::text("load").append(pretty_sequence(
                args,
                any_comment,
                force_multiline,
                false,
                "(",
                ")",
            ))
        }
        StmtData::ReturnStmt { result, .. } => {
            let mut d = RcDoc::text("return");
            if let Some(r) = result {
                d = d.append(RcDoc::space()).append(pretty_expr(r, state));
            }
            d
        }
    };

    doc_before
        .append(content)
        .append(state.suffix_comment(stmt.id.0))
}

fn pretty_expr<'a>(expr: &'a Expr<'a>, state: &mut PrinterState<'a>) -> RcDoc<'a, ()> {
    let (content, suffix) = pretty_expr_split(expr, state);
    content.append(suffix)
}

fn pretty_expr_split<'a>(
    expr: &'a Expr<'a>,
    state: &mut PrinterState<'a>,
) -> (RcDoc<'a, ()>, RcDoc<'a, ()>) {
    let doc_before = state.comments_before(expr.id.0, expr.span.start.line);
    let doc_after = state.suffix_comment(expr.id.0);

    let content = match &expr.data {
        ExprData::TupleExpr { list, .. } => {
            let items: Vec<_> = list.iter().map(|e| pretty_expr_split(e, state)).collect();
            let any_comment = list.iter().any(|e| state.has_suffix_comment(e.id.0));
            let force_multiline = expr.span.end.line > expr.span.start.line;
            pretty_sequence(items, any_comment, force_multiline, true, "(", ")")
        }
        ExprData::CallExpr { func, args, .. } => {
            let doc = pretty_expr(func, state);
            let items: Vec<_> = args.iter().map(|e| pretty_expr_split(e, state)).collect();
            let any_comment = args.iter().any(|e| state.has_suffix_comment(e.id.0));
            let force_multiline = expr.span.end.line > expr.span.start.line;
            doc.append(pretty_sequence(
                items,
                any_comment,
                force_multiline,
                false,
                "(",
                ")",
            ))
        }
        ExprData::ListExpr { list, .. } => {
            let items: Vec<_> = list.iter().map(|e| pretty_expr_split(e, state)).collect();
            let any_comment = list.iter().any(|e| state.has_suffix_comment(e.id.0));
            let force_multiline = expr.span.end.line > expr.span.start.line;
            pretty_sequence(items, any_comment, force_multiline, false, "[", "]")
        }
        ExprData::DictExpr { list, .. } => {
            let items: Vec<_> = list.iter().map(|e| pretty_expr_split(e, state)).collect();
            let any_comment = list.iter().any(|e| state.has_suffix_comment(e.id.0));
            let force_multiline = expr.span.end.line > expr.span.start.line;
            pretty_sequence(items, any_comment, force_multiline, false, "{", "}")
        }
        _ => pretty_expr_internal(expr, state),
    };
    (doc_before.append(content), doc_after)
}

fn pretty_sequence<'a>(
    items: Vec<(RcDoc<'a, ()>, RcDoc<'a, ()>)>,
    any_comment: bool,
    force_multiline: bool,
    preserve_unary: bool,
    open: &'a str,
    close: &'a str,
) -> RcDoc<'a, ()> {
    let (surround_sep, between_sep) = if any_comment || force_multiline {
        (RcDoc::hardline(), RcDoc::hardline())
    } else {
        (
            RcDoc::flat_alt(RcDoc::hardline(), RcDoc::nil()),
            RcDoc::line(),
        )
    };

    let mut inner = RcDoc::nil();
    let len = items.len();

    for (i, (content, comment)) in items.into_iter().enumerate() {
        if i > 0 {
            inner = inner.append(between_sep.clone());
        }
        inner = inner.append(content);

        if i < len - 1 {
            inner = inner.append(RcDoc::text(","));
        } else {
            // Last item
            if preserve_unary && len == 1 {
                inner = inner.append(RcDoc::text(","));
            } else {
                inner = inner.append(RcDoc::flat_alt(RcDoc::text(","), RcDoc::nil()));
            }
        }
        inner = inner.append(comment);
    }

    RcDoc::text(open)
        .append(
            surround_sep
                .clone()
                .append(inner)
                .append(surround_sep)
                .nest(INDENT),
        )
        .append(RcDoc::text(close))
        .group()
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
        ExprData::BinaryExpr { x, op, y, .. } => {
            let mut doc = pretty_expr(x, state);
            if *op == crate::token::Token::Eq {
                doc = doc.append(RcDoc::text(" = ")).append(pretty_expr(y, state));
            } else {
                doc = doc
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(op))
                    .append(RcDoc::space())
                    .append(pretty_expr(y, state));
            }
            doc
        }
        ExprData::CallExpr { .. }
        | ExprData::ListExpr { .. }
        | ExprData::TupleExpr { .. }
        | ExprData::DictExpr { .. } => {
            unreachable!("Handled in pretty_expr_split")
        }
        ExprData::Comprehension {
            curly,
            body,
            clauses,
            ..
        } => {
            let mut doc =
                RcDoc::text(if *curly { "{" } else { "[" }).append(pretty_expr(body, state));
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
        ExprData::DictEntry { key, value, .. } => pretty_expr(key, state)
            .append(RcDoc::text(": "))
            .append(pretty_expr(value, state)),
        ExprData::DotExpr { x, name, .. } => pretty_expr(x, state)
            .append(RcDoc::text("."))
            .append(RcDoc::text(name.name)),
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
            doc.append(RcDoc::text(": "))
                .append(pretty_expr(body, state))
        }
        ExprData::Literal { token, .. } => RcDoc::as_string(token),
        ExprData::ParenExpr { x, .. } => {
            if let ExprData::TupleExpr { lparen: None, .. } = &x.data {
                pretty_expr(x, state)
            } else {
                RcDoc::text("(")
                    .append(pretty_expr(x, state))
                    .append(RcDoc::text(")"))
            }
        }
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
                doc = doc
                    .append(RcDoc::text(":"))
                    .append(pretty_expr(step, state));
            }
            doc.append(RcDoc::text("]"))
        }
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
