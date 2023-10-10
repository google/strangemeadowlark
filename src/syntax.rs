use std::path::Path;

use crate::{
    scan::{Comment, Position},
    token::Token,
};

trait NodeData {
    fn span(&self) -> Option<Span>;
    fn comments(&self) -> Option<Comments>;

    fn add_comment(&mut self, comment: Comment);
}

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

    fn add_comment(&mut self, comment: Comment) {
        todo!()
    }
}

#[derive(Clone)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

pub struct Comments {
    pub before: Vec<Comment>,
    pub after: Vec<Comment>,
    pub suffix: Vec<Comment>,
}

pub struct Stmt<'a> {
    pub span: Span,
    pub data: StmtData<'a>,
}

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
        body: Vec<&'a Stmt<'a>>,
    },
    WhileStmt {
        while_pos: Position,
        cond: &'a Expr<'a>,
        body: Vec<&'a Stmt<'a>>,
    },
    IfStmt {
        if_pos: Position, // IF or ELIF
        cond: &'a Expr<'a>,
        then_arm: Vec<&'a Stmt<'a>>,
        else_pos: Option<Position>,  // ELSE or ELIF
        else_arm: Vec<&'a Stmt<'a>>, // optional
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

pub struct Expr<'a> {
    pub data: ExprData<'a>,
}

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
        args: Vec<&'a Expr<'a>>, // arg = expr | ident=expr | *expr | **expr
        rparen: Position,
    },
    /// A Comprehension represents a list or dict comprehension:
    /// "[Body for ... if ...] or {Body for ... if ...}"
    Comprehension {
        curly: bool, // {x:y for ...} or {x for ...}, not [x for ...]
        lbrack_pos: Position,
        body: &'a Expr<'a>,
        clauses: Vec<&'a Clause<'a>>,
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
        lbrace_pos: Position,
        list: Vec<&'a Expr<'a>>, // all *DictEntrys
        rbrace_pos: Position,
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
        lbrack_pos: Position,
        y: &'a Expr<'a>,
        rbrack_pos: Position,
    },
    LambdaExpr {
        lambda_pos: Position,
        // param = ident | ident=expr | * | *ident | **ident
        params: Vec<&'a Expr<'a>>,
        body: &'a Expr<'a>,
    },
    ListExpr {
        lbrack_pos: Position,
        list: Vec<&'a Expr<'a>>,
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
        lbrack: &'a Position,
        lo: Option<&'a Expr<'a>>,
        hi: Option<&'a Expr<'a>>,
        step: Option<&'a Expr<'a>>,
        rbrack_pos: Position,
    },
    TupleExpr {
        lparen: Position, // optional (e.g. in x, y = 0, 1), but required if List is empty
        list: Vec<&'a Expr<'a>>,
        rparen: Position,
    },
    UnaryExpr {
        op_pos: Position,
        op: Token,
        x: Option<&'a Expr<'a>>, // may be nil if Op==STAR),
    },
}

pub struct Ident {
    pub name_pos: Position,
    pub name: String,
}

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
