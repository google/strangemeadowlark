use crate::{
    quote::{quote, quote_bytes},
    Clause, Expr, ExprData, FileUnit, Literal, Span, Stmt, StmtData,
};
use anyhow::Result;
use std::fmt;

static INDENT: usize = 2;

pub struct PrinterOptions {
    pub split_module_fn_args: bool,
    pub max_chars: Option<usize>,
}

impl Default for PrinterOptions {
    fn default() -> Self {
        Self {
            split_module_fn_args: false,
            max_chars: Some(100),
        }
    }
}

impl PrinterOptions {
    fn nested() -> Self {
        Self {
            split_module_fn_args: false,
            max_chars: None,
        }
    }
}

pub struct Printer<'ast, 'w> {
    unit: &'ast FileUnit<'ast>,
    writer: &'w mut dyn fmt::Write,
    current_line: usize,
    current_col: usize,
    last_comment_line: usize,
    current_indent: usize,
    indents: Vec<usize>,
    options: PrinterOptions,
}

impl<'ast, 'w> Printer<'ast, 'w> {
    pub fn new_with_options(
        unit: &'ast FileUnit<'ast>,
        writer: &'w mut dyn fmt::Write,
        options: PrinterOptions,
    ) -> Self {
        Printer {
            unit,
            writer,
            current_line: 1,
            current_col: 1,
            last_comment_line: 0,
            current_indent: 0,
            indents: vec![],
            options,
        }
    }

    pub fn new(unit: &'ast FileUnit<'ast>, writer: &'w mut dyn fmt::Write) -> Self {
        Self::new_with_options(unit, writer, PrinterOptions::default())
    }

    fn nested<'b>(&self, buffer: &'b mut String) -> Printer<'ast, 'b> {
        Printer {
            unit: self.unit,
            writer: buffer,
            current_line: 1,
            current_col: 1,
            last_comment_line: 0,
            current_indent: 0,
            indents: vec![],
            options: PrinterOptions::nested(),
        }
    }

    fn write(&mut self, text: &str) -> Result<()> {
        self.current_col += text.len();
        write!(self.writer, "{}", text)?;
        Ok(())
    }

    fn write_wrapped(&mut self, prefix: &str, text: &str) -> Result<()> {
        self.current_col += prefix.len() + text.len();
        if let Some(limit) = self.options.max_chars {
            if limit <= self.current_col {
                writeln!(self.writer)?;
                self.current_line += 1;
                self.current_col = 1;
                self.print_indent()?;
                self.current_col += text.len();
            } else {
                write!(self.writer, "{}", prefix)?;
            }
        }
        write!(self.writer, "{}", text)?;
        Ok(())
    }

    fn writeln(&mut self, text: &str) -> Result<()> {
        writeln!(self.writer, "{}", text)?;
        self.current_col = 1;
        Ok(())
    }

    fn print_indent(&mut self) -> Result<()> {
        for _i in 0..self.current_indent {
            self.write(" ")?;
        }
        self.current_col = self.current_indent;
        Ok(())
    }

    fn incr_indent(&mut self) {
        self.current_indent += INDENT;
    }

    fn decr_indent(&mut self) {
        self.current_indent -= INDENT;
    }

    fn push_indent(&mut self) {
        self.indents.push(self.current_indent);
        self.current_indent = self.current_col;
    }

    fn pop_indent(&mut self) {
        self.current_indent = self.indents.pop().unwrap();
    }

    // We infer what line number we are on based on `last`.
    // It might be completely wrong with respect to our output,
    // but it should be consistent with the line information
    // on the line comments.
    fn print_newline(&mut self, last: &Span) -> Result<()> {
        self.writeln("")?;
        self.current_line = last.end.line as usize + 1;
        Ok(())
    }

    fn print_suffix_newline(&mut self, current: &Span) -> Result<()> {
        for comment in self.unit.suffix_comments {
            if comment.start.line == current.start.line {
                self.write(&format!(" {}", comment.text))?;
                break;
            }
        }
        self.print_newline(current)
    }

    fn print_line_comments(&mut self, up_to: &Span) -> Result<()> {
        for comment in self.unit.line_comments {
            if comment.start.line as usize <= self.last_comment_line {
                continue;
            }
            if comment.start.line > up_to.start.line {
                break;
            }
            for _ in 0..(comment.start.line as usize - self.current_line) {
                self.writeln("")?;
                self.current_line += 1;
            }
            for _ in 1..comment.start.col {
                self.write(" ")?;
            }

            self.writeln(comment.text)?;
            self.last_comment_line = comment.start.line as usize;
            self.current_line = comment.start.line as usize + 1;
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
            StmtData::AssignStmt { op, lhs, rhs, .. } => {
                self.print_expr(lhs)?;
                self.write(" ")?;
                self.write(&op.to_string())?;
                self.write(" ")?;
                self.print_expr(rhs)?;
            }
            StmtData::BranchStmt { token, .. } => {
                self.write(&token.to_string())?;
            }
            StmtData::DefStmt {
                name, params, body, ..
            } => {
                let is_module = self.current_indent == 0;
                self.write(&format!("def {}(", name.name))?;
                if is_module && self.options.split_module_fn_args {
                    self.print_line_separated(params.iter(), &stmt.span)?;
                } else {
                    self.push_indent();
                    self.print_comma_separated(params.iter())?;
                    self.pop_indent();
                }
                self.write("):")?;
                self.print_newline(&stmt.span)?;
                self.incr_indent();
                for stmt in body.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
            }
            StmtData::ExprStmt { x } => {
                self.print_expr(x)?;
            }
            StmtData::ForStmt { vars, x, body, .. } => {
                self.write("for ")?;
                match &vars.data {
                    ExprData::TupleExpr { list, .. } => {
                        self.write(
                            &list
                                .iter()
                                .map(|ex| format!("{}", ex.data))
                                .collect::<Vec<_>>()
                                .join(","),
                        )?;
                    }
                    _ => {
                        self.print_expr(vars)?;
                    }
                };
                self.write(" in ")?;
                self.print_expr(x)?;
                self.write(":")?;
                self.print_newline(&x.span)?;
                self.incr_indent();
                for stmt in body.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
            }
            StmtData::WhileStmt { cond, body, .. } => {
                self.write("while ")?;
                self.print_expr(cond)?;
                self.write(":")?;
                self.print_newline(&cond.span)?;
                self.incr_indent();
                for stmt in body.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
            }
            StmtData::IfStmt {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                self.write("if ")?;
                self.print_expr(cond)?;
                self.write(":")?;
                self.print_newline(&cond.span)?;
                self.incr_indent();
                for stmt in then_arm.iter() {
                    self.print_stmt(stmt)?;
                }
                self.decr_indent();
                if !else_arm.is_empty() {
                    self.print_indent()?;
                    self.write("else:")?;
                    self.incr_indent();
                    self.print_newline(&cond.span)?;
                    for stmt in then_arm.iter() {
                        self.print_stmt(stmt)?;
                    }
                    self.decr_indent();
                }
            }
            StmtData::LoadStmt {
                module, from, to, ..
            } => {
                self.write("load(")?;
                self.print_expr(module)?;
                for (f, t) in from.iter().zip(to.iter()) {
                    self.write(", ")?;
                    if f == t {
                        self.write(&format!("{:?}", f.name))?;
                    } else {
                        self.write(&format!("{} = {:?}", f.name, t.name))?;
                    }
                }
                self.write(")")?;
            }
            StmtData::ReturnStmt {
                return_pos: _,
                result,
            } => {
                self.write("return")?;
                if let Some(res) = result {
                    self.write(" ")?;
                    self.print_expr(res)?
                }
            }
        }
        self.print_suffix_newline(&stmt.span)?;
        Ok(())
    }

    pub fn print_clause(&mut self, clause: &Clause) -> Result<()> {
        match clause {
            Clause::ForClause { vars, x, .. } => {
                self.write(" for ")?;
                self.print_expr(vars)?;
                self.write(" in ")?;
                self.print_expr(x)?;
            }
            Clause::IfClause { cond, .. } => {
                self.write("if ")?;
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
            let prefix = if first {
                first = false;
                ""
            } else {
                self.write(",")?;
                " "
            };
            let mut buffer = String::new();
            let mut p = self.nested(&mut buffer);
            p.print_expr(expr)?;
            self.write_wrapped(prefix, &buffer)?;
        }
        Ok(())
    }

    pub fn print_line_separated<'a>(
        &mut self,
        exprs: impl Iterator<Item = &'a &'a Expr<'a>>,
        mut last_span: &'a Span,
    ) -> Result<()> {
        self.incr_indent();
        self.incr_indent();
        let mut first = true;
        for (i, expr) in exprs.enumerate() {
            if first {
                first = false
            } else {
                self.write(",")?;
            }
            self.print_newline(last_span)?;
            self.print_indent()?;
            self.print_expr(expr)?;
            last_span = &expr.span;
        }
        self.decr_indent();
        self.decr_indent();
        Ok(())
    }

    pub fn print_expr(&mut self, expr: &Expr) -> Result<()> {
        match &expr.data {
            ExprData::BinaryExpr { x, op, y, .. } => {
                self.print_expr(x)?;
                self.write(" ")?;
                self.write(&format!("{}", op))?;
                self.write(" ")?;
                self.print_expr(y)?;
            }
            ExprData::CallExpr { func, args, .. } => {
                self.write(&format!("{}", func.data))?;
                self.write("(")?;
                self.push_indent();
                self.print_comma_separated(args.iter())?;
                self.pop_indent();
                self.write(")")?;
            }
            ExprData::Comprehension {
                curly,
                body,
                clauses,
                ..
            } => {
                self.write(if *curly { "{" } else { "[" })?;
                self.print_expr(body)?;
                for clause in clauses.iter() {
                    self.print_clause(clause)?;
                }
                self.write(if *curly { "{" } else { "]" })?;
            }
            ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                self.print_expr(then_arm)?;
                self.write(" if ")?;
                self.print_expr(cond)?;
                self.write(" else ")?;
                self.print_expr(else_arm)?;
            }
            ExprData::DictEntry {
                key,
                colon: _,
                value,
            } => {
                self.print_expr(key)?;
                self.write(": ")?;
                self.print_expr(value)?;
            }
            ExprData::DictExpr { list, .. } => {
                self.write("{")?;
                self.print_comma_separated(list.iter())?;
                self.write("}")?;
            }
            ExprData::DotExpr { x, name, .. } => {
                self.print_expr(x)?;
                self.write(" ")?;
                self.write(name.name)?;
            }
            ExprData::Ident(ident) => {
                self.write(ident.name)?;
            }
            ExprData::IndexExpr { x, y, .. } => {
                self.print_expr(x)?;
                self.write("[")?;
                self.print_expr(y)?;
                self.write("]")?;
            }
            ExprData::LambdaExpr { params, body, .. } => {
                self.print_comma_separated(params.iter())?;
                self.write(": ")?;
                self.print_expr(body)?;
            }
            ExprData::ListExpr { list, .. } => {
                self.write("[")?;
                self.print_comma_separated(list.iter())?;
                self.write("]")?;
            }
            ExprData::Literal {
                token: Literal::String(decoded),
                ..
            } => self.write(&quote(decoded))?,
            ExprData::Literal {
                token: Literal::Bytes(decoded),
                ..
            } => self.write(&quote_bytes(decoded))?,
            ExprData::Literal {
                token: Literal::Int(int_value),
                ..
            } => self.write(&format!("{}", int_value))?,
            ExprData::Literal {
                token: Literal::BigInt(bigint_value),
                ..
            } => self.write(&format!("{}", bigint_value))?,
            ExprData::Literal {
                token: Literal::Float(float_value),
                ..
            } => self.write(&format!("{}", float_value))?,
            ExprData::ParenExpr { x, .. } => {
                self.write("(")?;
                self.print_expr(x)?;
                self.write(")")?;
            }
            ExprData::SliceExpr {
                x, lo, hi, step, ..
            } => {
                self.print_expr(x)?;
                self.write("[")?;
                if let Some(lo) = lo {
                    self.print_expr(lo)?;
                }
                self.write(":")?;
                if let Some(hi) = hi {
                    self.print_expr(hi)?;
                }
                if let Some(step) = step {
                    self.write(":")?;
                    self.print_expr(step)?;
                }
                self.write("]")?;
            }
            ExprData::TupleExpr { list, .. } => {
                self.write("(")?;
                self.print_comma_separated(list.iter())?;
                self.write(")")?;
            }
            ExprData::UnaryExpr { op, x, .. } => {
                self.write(&format!("{}", op))?;
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
    use crate::{parse_with_mode, Arena, Mode};
    use googletest::prelude::*;

    #[test]
    fn test_basic() -> googletest::prelude::Result<()> {
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
  return {\"foo\": \"bar\"}

";
        let arena = Arena::new();
        let unit = parse_with_mode(&arena, &"<test>", &src, Mode::RetainComments)?;

        let mut w = String::new();
        let mut printer = Printer::new(unit, &mut w);

        assert!(printer.print_file_unit().is_ok());

        verify_that!(&w, eq(&src))
    }

    #[test]
    fn test_long_line() -> googletest::prelude::Result<()> {
        let src = "\
def foo(we, have, a, definition, that, has, many, parameters, it, should, be, broken, up, into, multiple, lines):
    pass

foo(same, here, we, have, a, callexpr, that, has, many, parameters, it, should, be, broken, up, into, multiple, lines)
 
";
        let arena = Arena::new();
        let unit = parse_with_mode(&arena, &"<test>", &src, Mode::RetainComments)?;

        let mut w = String::new();
        let mut printer = Printer::new(unit, &mut w);

        assert!(printer.print_file_unit().is_ok());

        let expected = "\
def foo(we, have, a, definition, that, has, many, parameters, it, should, be, broken, up, into,
        multiple, lines):
  pass

foo(same, here, we, have, a, callexpr, that, has, many, parameters, it, should, be, broken, up,
    into, multiple, lines)
";

        verify_that!(&w, eq(&expected))
    }

    #[test]
    fn test_long_line_break() -> googletest::prelude::Result<()> {
        let src = "\
def foo(we, have, a, definition, that, has, many, parameters, it, should, be, broken, up, into, multiple, lines):
    pass

foo(same, here, we, have, a, callexpr, that, has, many, parameters, it, should, be, broken, up, into, multiple, lines)
 
";
        let arena = Arena::new();
        let unit = parse_with_mode(&arena, &"<test>", &src, Mode::RetainComments)?;

        let mut w = String::new();
        let mut options = PrinterOptions::default();
        options.split_module_fn_args = true;
        let mut printer = Printer::new_with_options(unit, &mut w, options);

        assert!(printer.print_file_unit().is_ok());

        let expected = "\
def foo(
    we,
    have,
    a,
    definition,
    that,
    has,
    many,
    parameters,
    it,
    should,
    be,
    broken,
    up,
    into,
    multiple,
    lines):
  pass

foo(same, here, we, have, a, callexpr, that, has, many, parameters, it, should, be, broken, up,
    into, multiple, lines)
";

        verify_that!(&w, eq(&expected))
    }
}
