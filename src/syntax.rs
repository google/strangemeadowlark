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

use crate::ID_GEN;
use std::collections::HashMap;
use std::{cell::RefCell, fmt::Display, path::Path};

use num_bigint::BigInt;

use crate::{
    binding::BindingIndex,
    quote::{quote, quote_bytes},
    scan::{Comment, Position},
    token::Token,
};

pub type StmtRef<'a> = &'a Stmt<'a>;

#[derive(Debug, PartialEq)]
pub struct FileUnit<'a> {
    pub path: &'a Path,
    pub stmts: &'a [StmtRef<'a>],
    pub line_comments: &'a [&'a Comment<'a>], // list of full line comments (if keepComments)
    pub suffix_comments: &'a [&'a Comment<'a>], // list of suffix comments (if keepComments)
    pub comments_before: HashMap<usize, Vec<usize>>,
    pub comments_suffix: HashMap<usize, Vec<usize>>,
    pub comments_after: HashMap<usize, Vec<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

#[derive(Debug)]
pub struct StmtId(pub usize);

#[derive(Debug)]
pub struct Stmt<'a> {
    pub span: Span,
    pub id: StmtId,
    pub data: StmtData<'a>,
}

impl PartialEq for Stmt<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

pub type ExprRef<'a> = &'a Expr<'a>;

#[derive(Debug)]
pub enum StmtData<'a> {
    // op is one of EQ | {PLUS,MINUS,STAR,PERCENT}_EQ
    AssignStmt {
        op_pos: Position,
        op: Token,
        lhs: ExprRef<'a>,
        rhs: ExprRef<'a>,
    },
    BranchStmt {
        token: Token, // = BREAK | CONTINUE | PASS
        token_pos: Position,
    },
    DefStmt {
        def_pos: Position,
        name: &'a Ident<'a>,
        lparen: Position,
        params: &'a [ExprRef<'a>],
        rparen: Position,
        body: &'a [StmtRef<'a>],
        function: RefCell<Option<usize>>,
    },
    ExprStmt {
        x: ExprRef<'a>,
    },
    ForStmt {
        for_pos: Position,
        vars: ExprRef<'a>, // name, or tuple of names
        x: ExprRef<'a>,
        body: &'a [StmtRef<'a>],
    },
    WhileStmt {
        while_pos: Position,
        cond: ExprRef<'a>,
        body: &'a [StmtRef<'a>],
    },
    IfStmt {
        if_pos: Position, // IF or ELIF
        cond: ExprRef<'a>,
        then_arm: &'a [StmtRef<'a>],
        else_pos: Option<Position>,  // ELSE or ELIF
        else_arm: &'a [StmtRef<'a>], // optional
    },
    LoadStmt {
        load_pos: Position,
        module: ExprRef<'a>,       // Literal string
        from: &'a [&'a Ident<'a>], // name defined in loading module
        to: &'a [&'a Ident<'a>],   // name in loaded module
        rparen_pos: Position,
    },
    ReturnStmt {
        return_pos: Position,
        result: Option<ExprRef<'a>>,
    },
}

impl PartialEq for StmtData<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::AssignStmt {
                    op: l_op,
                    lhs: l_lhs,
                    rhs: l_rhs,
                    ..
                },
                Self::AssignStmt {
                    op: r_op,
                    lhs: r_lhs,
                    rhs: r_rhs,
                    ..
                },
            ) => l_op == r_op && l_lhs == r_lhs && l_rhs == r_rhs,
            (
                Self::BranchStmt {
                    token: l_token,
                    token_pos: l_token_pos,
                },
                Self::BranchStmt {
                    token: r_token,
                    token_pos: r_token_pos,
                },
            ) => l_token == r_token && l_token_pos == r_token_pos,
            (
                Self::DefStmt {
                    name: l_name,
                    params: l_params,
                    body: l_body,
                    ..
                },
                Self::DefStmt {
                    name: r_name,
                    params: r_params,
                    body: r_body,
                    ..
                },
            ) => l_name == r_name && l_params == r_params && l_body == r_body,
            (Self::ExprStmt { x: l_x }, Self::ExprStmt { x: r_x }) => l_x == r_x,
            (
                Self::ForStmt {
                    for_pos: l_for_pos,
                    vars: l_vars,
                    x: l_x,
                    body: l_body,
                },
                Self::ForStmt {
                    for_pos: r_for_pos,
                    vars: r_vars,
                    x: r_x,
                    body: r_body,
                },
            ) => l_for_pos == r_for_pos && l_vars == r_vars && l_x == r_x && l_body == r_body,
            (
                Self::WhileStmt {
                    while_pos: l_while_pos,
                    cond: l_cond,
                    body: l_body,
                },
                Self::WhileStmt {
                    while_pos: r_while_pos,
                    cond: r_cond,
                    body: r_body,
                },
            ) => l_while_pos == r_while_pos && l_cond == r_cond && l_body == r_body,
            (
                Self::IfStmt {
                    if_pos: l_if_pos,
                    cond: l_cond,
                    then_arm: l_then_arm,
                    else_pos: l_else_pos,
                    else_arm: l_else_arm,
                },
                Self::IfStmt {
                    if_pos: r_if_pos,
                    cond: r_cond,
                    then_arm: r_then_arm,
                    else_pos: r_else_pos,
                    else_arm: r_else_arm,
                },
            ) => {
                l_if_pos == r_if_pos
                    && l_cond == r_cond
                    && l_then_arm == r_then_arm
                    && l_else_pos == r_else_pos
                    && l_else_arm == r_else_arm
            }
            (
                Self::LoadStmt {
                    load_pos: l_load_pos,
                    module: l_module,
                    from: l_from,
                    to: l_to,
                    rparen_pos: l_rparen_pos,
                },
                Self::LoadStmt {
                    load_pos: r_load_pos,
                    module: r_module,
                    from: r_from,
                    to: r_to,
                    rparen_pos: r_rparen_pos,
                },
            ) => {
                l_load_pos == r_load_pos
                    && l_module == r_module
                    && l_from == r_from
                    && l_to == r_to
                    && l_rparen_pos == r_rparen_pos
            }
            (
                Self::ReturnStmt {
                    return_pos: l_return_pos,
                    result: l_result,
                },
                Self::ReturnStmt {
                    return_pos: r_return_pos,
                    result: r_result,
                },
            ) => l_return_pos == r_return_pos && l_result == r_result,
            _ => false,
        }
    }
}

impl Display for StmtData<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StmtData::AssignStmt { op, lhs, rhs, .. } => write!(
                f,
                "(AssignStmt Op={} LHS={} RHS={})",
                op, lhs.data, rhs.data
            ),
            StmtData::BranchStmt { token, .. } => write!(f, "(BranchStmt Token={token})"),
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
pub struct ExprId(pub usize);

#[derive(Debug)]
pub struct Expr<'a> {
    pub span: Span,
    pub id: ExprId,
    pub data: ExprData<'a>,
}

impl PartialEq for Expr<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

#[derive(Debug)]
pub enum ExprData<'a> {
    BinaryExpr {
        x: ExprRef<'a>,
        op_pos: Position,
        op: Token,
        y: ExprRef<'a>,
    },
    CallExpr {
        func: ExprRef<'a>,
        lparen: Position,
        args: &'a [ExprRef<'a>], // arg = expr | ident=expr | *expr | **expr
        rparen: Position,
    },
    /// A Comprehension represents a list or dict comprehension:
    /// "[Body for ... if ...] or {Body for ... if ...}"
    Comprehension {
        curly: bool, // {x:y for ...} or {x for ...}, not [x for ...]
        lbrack_pos: Position,
        body: ExprRef<'a>,
        clauses: &'a [&'a Clause<'a>],
        rbrack_pos: Position,
    },
    CondExpr {
        if_pos: Position,
        cond: ExprRef<'a>,
        then_arm: ExprRef<'a>,
        else_pos: Position,
        else_arm: ExprRef<'a>,
    },
    DictEntry {
        key: ExprRef<'a>,
        colon: Position,
        value: ExprRef<'a>,
    },
    DictExpr {
        lbrace: Position,
        list: &'a [ExprRef<'a>], // all *DictEntrys
        rbrace: Position,
    },
    DotExpr {
        x: ExprRef<'a>,
        dot: Position,
        name_pos: Position,
        name: &'a Ident<'a>,
    },
    Ident(&'a Ident<'a>),
    IndexExpr {
        x: ExprRef<'a>,
        lbrack: Position,
        y: ExprRef<'a>,
        rbrack: Position,
    },
    LambdaExpr {
        lambda_pos: Position,
        // param = ident | ident=expr | * | *ident | **ident
        params: &'a [ExprRef<'a>],
        body: ExprRef<'a>,

        // Name resolution fills in the index of a resolver::Function
        function: RefCell<Option<usize>>,
    },
    ListExpr {
        lbrack: Position,
        list: &'a [ExprRef<'a>],
        rbrack: Position,
    },
    Literal {
        token: &'a Literal<'a>, // = STRING | BYTES | INT | FLOAT
        token_pos: Position,
    },
    ParenExpr {
        lparen: Position,
        x: ExprRef<'a>,
        rparen: Position,
    },
    SliceExpr {
        x: ExprRef<'a>,
        lbrack: Position,
        lo: Option<ExprRef<'a>>,
        hi: Option<ExprRef<'a>>,
        step: Option<ExprRef<'a>>,
        rbrack: Position,
    },
    TupleExpr {
        lparen: Option<Position>, // optional (e.g. in x, y = 0, 1), but required if List is empty
        list: &'a [ExprRef<'a>],
        rparen: Option<Position>,
    },
    UnaryExpr {
        op_pos: Position,
        op: Token,
        x: Option<ExprRef<'a>>, // may be nil if Op==STAR),
    },
}

impl PartialEq for ExprData<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::BinaryExpr {
                    x: l_x,
                    op: l_op,
                    y: l_y,
                    ..
                },
                Self::BinaryExpr {
                    x: r_x,
                    op: r_op,
                    y: r_y,
                    ..
                },
            ) => l_x == r_x && l_op == r_op && l_y == r_y,
            (
                Self::CallExpr {
                    func: l_func,
                    args: l_args,
                    ..
                },
                Self::CallExpr {
                    func: r_func,
                    args: r_args,
                    ..
                },
            ) => l_func == r_func && l_args == r_args,
            (
                Self::Comprehension {
                    curly: l_curly,
                    body: l_body,
                    clauses: l_clauses,
                    ..
                },
                Self::Comprehension {
                    curly: r_curly,
                    body: r_body,
                    clauses: r_clauses,
                    ..
                },
            ) => l_curly == r_curly && l_body == r_body && l_clauses == r_clauses,
            (
                Self::CondExpr {
                    cond: l_cond,
                    then_arm: l_then_arm,
                    else_arm: l_else_arm,
                    ..
                },
                Self::CondExpr {
                    cond: r_cond,
                    then_arm: r_then_arm,
                    else_arm: r_else_arm,
                    ..
                },
            ) => l_cond == r_cond && l_then_arm == r_then_arm && l_else_arm == r_else_arm,
            (
                Self::DictEntry {
                    key: l_key,
                    value: l_value,
                    ..
                },
                Self::DictEntry {
                    key: r_key,
                    value: r_value,
                    ..
                },
            ) => l_key == r_key && l_value == r_value,
            (Self::DictExpr { list: l_list, .. }, Self::DictExpr { list: r_list, .. }) => {
                l_list == r_list
            }
            (
                Self::DotExpr {
                    x: l_x,
                    name: l_name,
                    ..
                },
                Self::DotExpr {
                    x: r_x,
                    name: r_name,
                    ..
                },
            ) => l_x == r_x && l_name.name == r_name.name,
            (Self::Ident(l0), Self::Ident(r0)) => l0.name == r0.name,
            (Self::IndexExpr { x: l_x, y: l_y, .. }, Self::IndexExpr { x: r_x, y: r_y, .. }) => {
                l_x == r_x && l_y == r_y
            }
            (
                Self::LambdaExpr {
                    params: l_params,
                    body: l_body,
                    ..
                },
                Self::LambdaExpr {
                    params: r_params,
                    body: r_body,
                    ..
                },
            ) => l_params == r_params && l_body == r_body,
            (Self::ListExpr { list: l_list, .. }, Self::ListExpr { list: r_list, .. }) => {
                l_list == r_list
            }
            (Self::Literal { token: l_token, .. }, Self::Literal { token: r_token, .. }) => {
                l_token == r_token
            }
            (Self::ParenExpr { x: l_x, .. }, Self::ParenExpr { x: r_x, .. }) => l_x == r_x,
            (
                Self::SliceExpr {
                    x: l_x,
                    lo: l_lo,
                    hi: l_hi,
                    step: l_step,
                    ..
                },
                Self::SliceExpr {
                    x: r_x,
                    lo: r_lo,
                    hi: r_hi,
                    step: r_step,
                    ..
                },
            ) => l_x == r_x && l_lo == r_lo && l_hi == r_hi && l_step == r_step,
            (Self::TupleExpr { list: l_list, .. }, Self::TupleExpr { list: r_list, .. }) => {
                l_list == r_list
            }
            (
                Self::UnaryExpr {
                    op: l_op, x: l_x, ..
                },
                Self::UnaryExpr {
                    op: r_op, x: r_x, ..
                },
            ) => l_op == r_op && l_x == r_x,
            _ => false,
        }
    }
}

impl Display for ExprData<'_> {
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
            ExprData::Comprehension {
                curly,
                body,
                clauses,
                ..
            } => {
                write!(
                    f,
                    "(Comprehension {}Body={} Clauses=(",
                    if *curly { "Curly " } else { "" },
                    body.data
                )?;
                for clause in clauses.iter() {
                    write!(f, "{clause},")?;
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
            ExprData::Literal { token, .. } => write!(f, "{token}"),
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
                _ => write!(f, "(UnaryExpr Op={op})"),
            },
        }
    }
}

#[derive(Debug)]
pub enum Literal<'a> {
    String(&'a str),
    Bytes(&'a [u8]),
    Int(i64),
    BigInt(BigInt),
    Float(f64),
}

impl Display for Literal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::String(s) => write!(f, "{}", quote(s)),
            Literal::Bytes(s) => write!(f, "{}", quote_bytes(s)),
            Literal::Int(i) => write!(f, "{i}"),
            Literal::BigInt(bi) => write!(f, "{bi}"),
            Literal::Float(fl) => write!(f, "{fl}"),
        }
    }
}

impl PartialEq for Literal<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::Bytes(l0), Self::Bytes(r0)) => l0 == r0,
            (Self::Int(l0), Self::Int(r0)) => l0 == r0,
            (Self::BigInt(l0), Self::BigInt(r0)) => l0 == r0,
            (Self::Float(l0), Self::Float(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl Eq for Literal<'_> {}

#[derive(Clone, PartialEq, Eq)]
pub struct Ident<'a> {
    pub name_pos: Position,
    pub name: &'a str,

    // Name resolution fills in this index of a resolver::Binding
    pub binding: RefCell<Option<BindingIndex>>,
}

impl std::fmt::Debug for Ident<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ident")
            .field("name_pos", &self.name_pos)
            .field("name", &self.name)
            .finish()
    }
}

impl<'a> Ident<'a> {
    pub fn new(name_pos: Position, name: &'a str) -> Self {
        Ident {
            name_pos,
            name,
            binding: RefCell::new(None),
        }
    }

    pub fn as_expr(&'a self) -> Expr<'a> {
        Expr {
            id: ID_GEN.next_expr_id(),
            span: Span {
                start: self.name_pos,
                end: self.name_pos,
            },
            data: ExprData::Ident(self),
        }
    }

    pub fn set_binding(&self, binding: BindingIndex) {
        let mut b = self.binding.borrow_mut();
        *b = Some(binding)
    }

    /// Retrieves the binding for this ident.
    /// Panics if the binding is not set.
    pub fn binding(&self) -> Option<BindingIndex> {
        *self.binding.borrow()
    }
}

#[derive(Debug, PartialEq)]
pub enum Clause<'a> {
    // A ForClause represents a for clause in a list comprehension: "for Vars in X".
    ForClause {
        for_pos: Position,
        vars: ExprRef<'a>, // name, or tuple of names
        in_pos: Position,
        x: ExprRef<'a>,
    },

    // An IfClause represents an if clause in a list comprehension: if Cond.
    IfClause {
        if_pos: Position,
        cond: ExprRef<'a>,
    },
}

impl Display for Clause<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Clause::ForClause { vars, x, .. } => {
                write!(f, "(ForClause Vars={} X={})", vars.data, x.data)
            }
            Clause::IfClause { cond, .. } => write!(f, "(IfClause Cond={})", cond.data),
        }
    }
}
