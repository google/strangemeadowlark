use crate::{Clause, Expr, ExprData, FileUnit, Span, Stmt};
use anyhow::Result;
use std::fmt;

static INDENT: u32 = 2;

pub struct Printer<'ast, 'w> {
    unit: &'ast FileUnit<'ast>,
    writer: &'w mut dyn fmt::Write,
    current_line: u32,
    last_comment_line: u32,
    indent: u32,
}

impl<'ast, 'w> Printer<'ast, 'w> {
    pub fn new(unit: &'ast FileUnit<'ast>, writer: &'w mut dyn fmt::Write) -> Self {
        Printer {
            unit,
            writer,
            current_line: 1,
            last_comment_line: 0,
            indent: 0,
        }
    }

    fn print_indent(&mut self) -> Result<()> {
        for _i in 0..self.indent {
            write!(self.writer, " ")?;
        }
        Ok(())
    }

    fn incr_indent(&mut self) {
        self.indent += INDENT;
    }

    fn decr_indent(&mut self) {
        self.indent -= INDENT;
    }

    // We infer what line number we are on based on `last`.
    // It might be completely wrong with respect to our output,
    // but it should be consistent with the line information
    // on the line comments.
    fn print_newline(&mut self, last: &Span) -> Result<()> {
        writeln!(self.writer)?;
        self.current_line = last.end.line + 1;
        Ok(())
    }

    fn print_suffix_newline(&mut self, current: &Span) -> Result<()> {
        for comment in &self.unit.suffix_comments {
            if comment.start.line == current.start.line {
                write!(self.writer, " {}", comment.text)?;
                break
            }
        }
        self.print_newline(current)
    }

    fn print_line_comments(&mut self, up_to: &Span) -> Result<()> {
        for comment in &self.unit.line_comments {
            if comment.start.line <= self.last_comment_line {
                continue;
            }
            if comment.start.line > up_to.start.line {
                break;
            }
            for _ in 0..(comment.start.line - self.current_line) {
                writeln!(self.writer)?;
                self.current_line += 1;
            }
            for _ in 1..comment.start.col {
                write!(self.writer, " ")?;
            }

            writeln!(self.writer, "{}", comment.text)?;
            self.last_comment_line = comment.start.line;
            self.current_line = comment.start.line + 1;
        }
        Ok(())
    }

    pub fn print_file_unit(&mut self) -> Result<()> {
        for &stmt in self.unit.stmts {
            self.print_line_comments(&stmt.span)?;
            self.print_stmt(stmt)?;
        }
        Ok(())
    }

    pub fn print_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        self.print_line_comments(&stmt.span)?;
        self.print_indent()?;
        match &stmt.data {
            crate::StmtData::AssignStmt {
                op,
                lhs,
                rhs,
                ..
            } => {
                self.print_expr(lhs)?;
                write!(self.writer, " {} ", op)?;
                self.print_expr(rhs)?;
            }
            crate::StmtData::BranchStmt { token, .. } => {
                write!(self.writer, "{}", token)?;
            }
            crate::StmtData::DefStmt {
                name,                
                params,
                body,
                ..
            } => {
                write!(self.writer, "def {}(", name.name)?;
                self.print_comma_separated(params.iter())?;
                write!(self.writer, "):")?;
                self.print_newline(&stmt.span)?;
                self.incr_indent();
                for stmt in body.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
            }
            crate::StmtData::ExprStmt { x } => {
                self.print_expr(x)?;
            }
            crate::StmtData::ForStmt { vars, x, body, .. } => {
                write!(self.writer, "for ")?;
                match &vars.data {
                    ExprData::TupleExpr { list, .. } => {
                        write!(
                            self.writer,
                            "{}",
                            list.iter()
                                .map(|ex| format!("{}", ex.data))
                                .collect::<Vec<_>>()
                                .join(",")
                        )?;
                    }
                    _ => {
                        self.print_expr(vars)?;
                    }
                };
                write!(self.writer, " in ")?;
                self.print_expr(x)?;
                write!(self.writer, ":")?;
                self.print_newline(&x.span)?;
                self.incr_indent();
                for stmt in body.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
            }
            crate::StmtData::WhileStmt { cond, body, .. } => {
                write!(self.writer, "while ")?;
                self.print_expr(cond)?;
                write!(self.writer, ":")?;
                self.print_newline(&cond.span)?;
                self.incr_indent();
                for stmt in body.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
            }
            crate::StmtData::IfStmt {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                write!(self.writer, "if ")?;
                self.print_expr(cond)?;
                write!(self.writer, ":")?;
                self.print_newline(&cond.span)?;
                self.incr_indent();
                for stmt in then_arm.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
                if !else_arm.is_empty() {
                    self.print_indent()?;
                    write!(self.writer, "else:")?;
                    self.incr_indent();
                    self.print_newline(&cond.span)?;
                    for stmt in then_arm.iter() {
                        self.print_stmt(stmt)?;
                    }
                    self.decr_indent();
                }
            }
            crate::StmtData::LoadStmt {
                module, from, to, ..
            } => {
                write!(self.writer, "load(")?;
                self.print_expr(module)?;
                for (f, t) in from.iter().zip(to.iter()) {
                    write!(self.writer, ", ")?;
                    if f == t {
                        write!(self.writer, "{:?}", f.name)?;
                    } else {
                        write!(self.writer, "{} = {:?}", f.name, t.name)?;
                    }
                }
                write!(self.writer, ")")?;
            }
            crate::StmtData::ReturnStmt { return_pos: _, result } => {
                write!(self.writer, "return")?;
                match result {
                    Some(res) => {
                        write!(self.writer, " ")?;
                        self.print_expr(res)?
                    }
                    _ => {}
                }
            }
        }
        self.print_suffix_newline(&stmt.span)?;
        Ok(())
    }

    pub fn print_clause(&mut self, clause: &Clause) -> Result<()> {
        match clause {
            Clause::ForClause { vars, x, .. } => {
                write!(self.writer, " for ")?;
                self.print_expr(vars)?;
                write!(self.writer, " in ")?;
                self.print_expr(x)?;
            }
            Clause::IfClause { cond, .. } => {
                write!(self.writer, "if ")?;
                self.print_expr(cond)?;
            }
        }
        Ok(())
    }

    pub fn print_comma_separated<'a>(
        &mut self,
        exprs: impl Iterator<Item = &'a &'a Expr<'a>>,
    ) -> Result<()> {
        let mut first = true;
        for expr in exprs {
            if first {
                first = false
            } else {
                write!(self.writer, ", ")?;
            }
            self.print_expr(expr)?;
        }
        Ok(())
    }

    pub fn print_expr(&mut self, expr: &Expr) -> Result<()> {
        match &expr.data {
            crate::ExprData::BinaryExpr { x, op, y , ..} => {
                self.print_expr(x)?;
                write!(self.writer, " {} ", op)?;
                self.print_expr(y)?;
            },
            crate::ExprData::CallExpr { func, args, .. } => {
                write!(self.writer, "{}(", func.data)?;
                self.print_comma_separated(args.iter())?;
                write!(self.writer, ")")?;
            }
            crate::ExprData::Comprehension {
                curly,
                body,
                clauses,
                ..
            } => {
                write!(self.writer, "{}", if *curly { "{" } else { "[" })?;
                self.print_expr(body)?;
                for clause in clauses.iter() {
                    self.print_clause(clause)?;
                }
                write!(self.writer, "{}", if *curly { "{" } else { "]" })?;
            }
            crate::ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                self.print_expr(then_arm)?;
                write!(self.writer, " if ")?;
                self.print_expr(cond)?;
                write!(self.writer, " else ")?;
                self.print_expr(else_arm)?;
            }
            crate::ExprData::DictEntry { key, colon: _, value } => {
                self.print_expr(key)?;
                write!(self.writer, ": ")?;
                self.print_expr(value)?;                
            },
            crate::ExprData::DictExpr { list, .. } => {
                write!(self.writer, "{{")?;
                self.print_comma_separated(list.iter())?;
                write!(self.writer, "}}")?;
            }
            crate::ExprData::DotExpr { x, name, .. } => {
                self.print_expr(x)?;
                write!(self.writer, ".{}", name.name)?;
            }
            crate::ExprData::Ident(ident) => {
                write!(self.writer, "{}", ident.name)?;
            }
            crate::ExprData::IndexExpr { x, y, .. } => {
                self.print_expr(x)?;
                write!(self.writer, "[")?;
                self.print_expr(y)?;
                write!(self.writer, "]")?;
            }
            crate::ExprData::LambdaExpr { params, body, .. } => {
                self.print_comma_separated(params.iter())?;
                write!(self.writer, ": ")?;
                self.print_expr(body)?;
            }
            crate::ExprData::ListExpr { list, .. } => {
                write!(self.writer, "[")?;
                self.print_comma_separated(list.iter())?;
                write!(self.writer, "]")?;
            }
            crate::ExprData::Literal { raw, .. } => write!(self.writer, "{}", raw)?,
            crate::ExprData::ParenExpr { x, .. } => {
                write!(self.writer, "(")?;
                self.print_expr(x)?;
                write!(self.writer, ")")?;
            }
            crate::ExprData::SliceExpr {
                x, lo, hi, step, ..
            } => {
                self.print_expr(x)?;
                write!(self.writer, "[")?;
                if let Some(lo) = lo {
                    self.print_expr(lo)?;
                }
                write!(self.writer, ":")?;
                if let Some(hi) = hi {
                    self.print_expr(hi)?;
                }
                if let Some(step) = step {
                    write!(self.writer, ":")?;
                    self.print_expr(step)?;
                }
                write!(self.writer, "]")?;
            }
            crate::ExprData::TupleExpr { list, .. } => {
                write!(self.writer, "(")?;
                self.print_comma_separated(list.iter())?;
                write!(self.writer, ")")?;
            }
            crate::ExprData::UnaryExpr { op, x, .. } => {
                write!(self.writer, "{}", op)?;
                if let Some(x) = x {
                    self.print_expr(x)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{parse, Mode};
    use bumpalo::Bump;

    #[test]
    fn test_basic() -> Result<()> {
        let src = "\
#hello
x = 1

#world
y = 1
for x in foo():
  pass # suffix comment

  # Comment in a different place.
  continue
  break
  return {'foo': 'bar'}

";
        let bump = Bump::new();
        let unit = parse(&bump, &"<test>", &src, Mode::RetainComments)?;

        let mut w = String::new();
        let mut printer = Printer::new(unit, &mut w);
        printer.print_file_unit()?;

        assert_eq!(&src, &w);
        Ok(())
    }
}
