use std::{fmt::Display, path::Path};

use crate::{
    scan::{Comment, Position},
    token::Token,
};

trait NodeData {
    fn span(&self) -> Option<Span>;
    fn comments(&self) -> Option<Comments>;

    fn add_comment(&mut self, comment: Comment);
}

#[derive(Debug)]
pub struct FileUnit<'a> {
    pub path: &'a Path,
    pub stmts: &'a [&'a Stmt<'a>],
}

impl<'a> NodeData for FileUnit<'a> {
    fn span(&self) -> Option<Span> {
        if self.stmts.is_empty() {
            None
        } else {
            let first = self.stmts.first().unwrap();
            let last = self.stmts.last().unwrap();
            Some(Span {
                start: first.span.start.clone(),
                end: last.span.end.clone(),
            })
        }
    }

    fn comments(&self) -> Option<Comments> {
        todo!()
    }

    fn add_comment(&mut self, _comment: Comment) {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

pub struct Comments {
    pub before: Vec<Comment>,
    pub after: Vec<Comment>,
    pub suffix: Vec<Comment>,
}

#[derive(Debug)]
pub struct Stmt<'a> {
    pub span: Span,
    pub data: StmtData<'a>,
}

#[derive(Debug)]
pub enum StmtData<'a> {
    // op is one of EQ | {PLUS,MINUS,STAR,PERCENT}_EQ
    AssignStmt {
        op_pos: Position,
        op: Token,
        lhs: &'a Expr<'a>,
        rhs: &'a Expr<'a>,
    },
    BranchStmt {
        token: Token, // = BREAK | CONTINUE | PASS
        token_pos: Position,
    },
    DefStmt {
        def_pos: Position,
        name: &'a Ident,
        lparen: Position,
        params: &'a [&'a Expr<'a>],
        rparen: Position,
        body: &'a [&'a Stmt<'a>],
    },
    ExprStmt {
        x: &'a Expr<'a>,
    },
    ForStmt {
        for_pos: Position,
        vars: &'a Expr<'a>, // name, or tuple of names
        x: &'a Expr<'a>,
        body: &'a [&'a Stmt<'a>],
    },
    WhileStmt {
        while_pos: Position,
        cond: &'a Expr<'a>,
        body: &'a [&'a Stmt<'a>],
    },
    IfStmt {
        if_pos: Position, // IF or ELIF
        cond: &'a Expr<'a>,
        then_arm: &'a [&'a Stmt<'a>],
        else_pos: Option<Position>,   // ELSE or ELIF
        else_arm: &'a [&'a Stmt<'a>], // optional
    },
    LoadStmt {
        load_pos: Position,
        module: &'a Expr<'a>,  // Literal string
        from: &'a [&'a Ident], // name defined in loading module
        to: &'a [&'a Ident],   // name in loaded module
        rparen_pos: Position,
    },
    ReturnStmt {
        return_pos: Position,
        result: Option<&'a Expr<'a>>,
    },
}

impl<'a> Display for StmtData<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StmtData::AssignStmt { op, lhs, rhs, .. } => write!(
                f,
                "(AssignStmt Op={} LHS={} RHS={})",
                op, lhs.data, rhs.data
            ),
            StmtData::BranchStmt { token, .. } => write!(f, "(BranchStmt Token={})", token),
            StmtData::DefStmt {
                name, params, body, ..
            } => {
                write!(f, "(DefStmt Name={} Params=(", name.name)?;
                for p in params.iter() {
                    write!(f, "{},", p.data)?;
                }
                write!(f, ") Body=(")?;
                for stmt in body.iter() {
                    write!(f, "{},", stmt.data)?;
                }
                write!(f, "))",)
            }
            StmtData::ExprStmt { x } => write!(f, "(ExprStmt X={})", x.data),
            StmtData::ForStmt { vars, x, body, .. } => {
                write!(f, "(ForStmt Vars={} X={} Body=(", vars.data, x.data)?;
                for stmt in body.iter() {
                    write!(f, "{},", stmt.data)?;
                }
                write!(f, "))")
            }
            StmtData::WhileStmt {
                cond: _, body: _, ..
            } => todo!(),
            StmtData::IfStmt {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                write!(f, "(IfStmt Cond={} True=(", cond.data)?;
                for stmt in then_arm.iter() {
                    write!(f, "{},", stmt.data)?;
                }
                write!(f, ") False=(")?;
                for stmt in else_arm.iter() {
                    write!(f, "{},", stmt.data)?;
                }
                write!(f, "))")
            }
            StmtData::LoadStmt { from, to, .. } => {
                write!(f, "(LoadStmt From=(")?;
                for ident in from.iter() {
                    write!(f, "{},", ident.name)?;
                }
                write!(f, ") To=(")?;
                for ident in to.iter() {
                    write!(f, "{},", ident.name)?;
                }
                write!(f, "))")
            }
            StmtData::ReturnStmt {
                result: Some(result_expr),
                ..
            } => write!(f, "(ReturnStmt Result={})", result_expr.data),
            StmtData::ReturnStmt { result: None, .. } => write!(f, "(ReturnStmt)"),
        }
    }
}

#[derive(Debug)]
pub struct Expr<'a> {
    pub span: Span,
    pub data: ExprData<'a>,
}

#[derive(Debug)]

pub enum ExprData<'a> {
    BinaryExpr {
        x: &'a Expr<'a>,
        op_pos: Position,
        op: Token,
        y: &'a Expr<'a>,
    },
    CallExpr {
        func: &'a Expr<'a>,
        lparen: Position,
        args: &'a [&'a Expr<'a>], // arg = expr | ident=expr | *expr | **expr
        rparen: Position,
    },
    /// A Comprehension represents a list or dict comprehension:
    /// "[Body for ... if ...] or {Body for ... if ...}"
    Comprehension {
        curly: bool, // {x:y for ...} or {x for ...}, not [x for ...]
        lbrack_pos: Position,
        body: &'a Expr<'a>,
        clauses: &'a [&'a Clause<'a>],
        rbrack_pos: Position,
    },
    CondExpr {
        if_pos: Position,
        cond: &'a Expr<'a>,
        then_arm: &'a Expr<'a>,
        else_pos: Position,
        else_arm: &'a Expr<'a>,
    },
    DictEntry {
        key: &'a Expr<'a>,
        colon: Position,
        value: &'a Expr<'a>,
    },
    DictExpr {
        lbrace: Position,
        list: &'a [&'a Expr<'a>], // all *DictEntrys
        rbrace: Position,
    },
    DotExpr {
        x: &'a Expr<'a>,
        dot: Position,
        name_pos: Position,
        name: &'a Ident,
    },
    Ident(&'a Ident),
    IndexExpr {
        x: &'a Expr<'a>,
        lbrack: Position,
        y: &'a Expr<'a>,
        rbrack: Position,
    },
    LambdaExpr {
        lambda_pos: Position,
        // param = ident | ident=expr | * | *ident | **ident
        params: &'a [&'a Expr<'a>],
        body: &'a Expr<'a>,
    },
    ListExpr {
        lbrack: Position,
        list: &'a [&'a Expr<'a>],
        rbrack: Position,
    },
    Literal {
        token: Token, // = STRING | BYTES | INT | FLOAT
        token_pos: Position,
        raw: String, // uninterpreted text
    },
    ParenExpr {
        lparen: Position,
        x: &'a Expr<'a>,
        rparen: Position,
    },
    SliceExpr {
        x: &'a Expr<'a>,
        lbrack: Position,
        lo: Option<&'a Expr<'a>>,
        hi: Option<&'a Expr<'a>>,
        step: Option<&'a Expr<'a>>,
        rbrack: Position,
    },
    TupleExpr {
        lparen: Option<Position>, // optional (e.g. in x, y = 0, 1), but required if List is empty
        list: &'a [&'a Expr<'a>],
        rparen: Option<Position>,
    },
    UnaryExpr {
        op_pos: Position,
        op: Token,
        x: Option<&'a Expr<'a>>, // may be nil if Op==STAR),
    },
}

impl<'a> Display for ExprData<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprData::BinaryExpr { x, op, y, .. } => {
                write!(f, "(BinaryExpr X={} Op={} Y={})", x.data, op, y.data)
            }
            ExprData::CallExpr { func, args, .. } => {
                write!(f, "(CallExpr Fn={} Args=(", func.data)?;
                for arg in args.iter() {
                    write!(f, "{},", arg.data)?;
                }
                write!(f, "))")
            }
            ExprData::Comprehension { body, clauses, .. } => {
                write!(f, "(Comprehension Body={} Clauses=(", body.data)?;
                for clause in clauses.iter() {
                    write!(f, "{},", clause)?;
                }
                write!(f, "))")
            }
            ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                write!(
                    f,
                    "(CondExpr Cond={} True={} False={})",
                    cond.data, then_arm.data, else_arm.data
                )
            }
            ExprData::DictEntry { key, value, .. } => {
                write!(f, "(DictEntry Key={} Value={})", key.data, value.data)
            }
            ExprData::DictExpr { list, .. } => {
                write!(f, "(DictExpr List=(")?;
                for dict_entry in list.iter() {
                    write!(f, "{},", dict_entry.data)?;
                }
                write!(f, "))")
            }
            ExprData::DotExpr { x, name, .. } => {
                write!(f, "(DotExpr X={} Name={})", x.data, name.name)
            }
            ExprData::Ident(id) => write!(f, "{}", id.name),
            ExprData::IndexExpr { x, y, .. } => {
                write!(f, "(IndexExpr X={} Y={})", x.data, y.data)
            }
            ExprData::LambdaExpr { params, body, .. } => {
                write!(f, "(LambdaExpr Params=(")?;
                for param in params.iter() {
                    write!(f, "{},", param.data)?;
                }
                write!(f, ") Body={})", body.data)
            }
            ExprData::ListExpr { list, .. } => {
                write!(f, "(ListExpr List=(")?;
                for expr in list.iter() {
                    write!(f, "{},", expr.data)?;
                }
                write!(f, "))")
            }
            ExprData::Literal { token, .. } => write!(f, "{}", token),
            ExprData::ParenExpr { x, .. } => {
                write!(f, "(ParenExpr X={})", x.data)
            }
            ExprData::SliceExpr {
                x, lo, hi, step, ..
            } => {
                write!(f, "(SliceExpr X={}", x.data)?;
                if lo.is_some() {
                    write!(f, " Lo={}", lo.unwrap().data)?;
                }
                if hi.is_some() {
                    write!(f, " Hi={}", hi.unwrap().data)?;
                }
                if step.is_some() {
                    write!(f, " Step={}", step.unwrap().data)?;
                }
                write!(f, ")")
            }
            ExprData::TupleExpr { list, .. } => {
                write!(f, "(TupleExpr List=(")?;
                for expr in list.iter() {
                    write!(f, "{},", expr.data)?;
                }
                write!(f, "))")
            }
            ExprData::UnaryExpr { op, x, .. } => match x {
                Some(x) => write!(f, "(UnaryExpr Op={} X={})", op, x.data),
                _ => write!(f, "(UnaryExpr Op={})", op),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub name_pos: Position,
    pub name: String,
}

impl Ident {
    pub fn as_expr<'a>(&'a self) -> Expr<'a> {
        Expr {
            span: Span {
                start: self.name_pos.clone(),
                end: self.name_pos.clone(),
            },
            data: ExprData::Ident(self),
        }
    }
}

#[derive(Debug)]
pub enum Clause<'a> {
    // A ForClause represents a for clause in a list comprehension: "for Vars in X".
    ForClause {
        for_pos: Position,
        vars: &'a Expr<'a>, // name, or tuple of names
        in_pos: Position,
        x: &'a Expr<'a>,
    },

    // An IfClause represents an if clause in a list comprehension: if Cond.
    IfClause {
        if_pos: Position,
        cond: &'a Expr<'a>,
    },
}

impl<'a> Display for Clause<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Clause::ForClause { vars, x, .. } => {
                write!(f, "(ForClause Vars={} X={})", vars.data, x.data)
            }
            Clause::IfClause { cond, .. } => write!(f, "(IfClause Cond={})", cond.data),
        }
    }
}
