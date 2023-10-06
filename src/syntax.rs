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
    pub path: String,
    pub stmts: Vec<Stmt<'a>>,
}

impl<'a> NodeData for FileUnit<'a> {
    fn span(&self) -> Option<Span<'a>> {
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
pub struct Span<'a> {
    start: Position<'a>,
    end: Position<'a>,
}

pub struct Comments<'a> {
    pub before: Vec<Comment<'a>>,
    pub after: Vec<Comment<'a>>,
    pub suffix: Vec<Comment<'a>>,
}

pub struct Stmt<'a> {
    pub span: Span<'a>,
    pub data: StmtData<'a>,
}

pub enum StmtData<'a> {
    // op is one of EQ | {PLUS,MINUS,STAR,PERCENT}_EQ
    AssignStmt {
        op_pos: Position<'a>,
        op: Token,
        lhs: &'a Expr<'a>,
        rhs: &'a Expr<'a>,
    },
    BranchStmt {
        token: Token, // = BREAK | CONTINUE | PASS
        token_pos: Position<'a>,
    },
    DefStmt {
        def_pos: Position<'a>,
        name: Ident<'a>,
        params: Vec<&'a Expr<'a>>,
        body: Vec<&'a Stmt<'a>>,
    },
    ExprStmt {
        x: &'a Expr<'a>,
    },
    ForStmt {
        for_pos: Position<'a>,
        vars: &'a Expr<'a>, // name, or tuple of names
        x: &'a Expr<'a>,
        body: Vec<&'a Stmt<'a>>,
    },
    WhileStmt {
        while_pos: Position<'a>,
        cond: &'a Expr<'a>,
        body: Vec<&'a Stmt<'a>>,
    },
    IfStmt {
        if_pos: Position<'a>, // IF or ELIF
        cond: &'a Expr<'a>,
        then_arm: Vec<&'a Stmt<'a>>,
        else_pos: Position<'a>,      // ELSE or ELIF
        else_arm: Vec<&'a Stmt<'a>>, // optional
    },
    LoadStmt {
        load_pos: Position<'a>,
        module: &'a Expr<'a>, // Literal string
        from: Vec<Ident<'a>>, // name defined in loading module
        to: Vec<Ident<'a>>,   // name in loaded module
        rparen_pos: Position<'a>,
    },
    ReturnStmt {
        return_pos: Position<'a>,
        result: Option<&'a Expr<'a>>,
    },
}

pub struct Expr<'a> {
    pub data: ExprData<'a>,
}

pub enum ExprData<'a> {
    BinaryExpr {
        x: &'a Expr<'a>,
        op_pos: Position<'a>,
        op: Token,
        y: &'a Expr<'a>,
    },
    CallExpr {
        func: &'a Expr<'a>,
        lparen: Position<'a>,
        args: Vec<&'a Expr<'a>>, // arg = expr | ident=expr | *expr | **expr
        rparen: Position<'a>,
    },
    /// A Comprehension represents a list or dict comprehension:
    /// "[Body for ... if ...] or {Body for ... if ...}"
    Comprehension{
        curly:   bool, // {x:y for ...} or {x for ...}, not [x for ...]
	    lbrack_pos:  Position<'a>,
	    body:    &'a Expr<'a>,
         clauses: Vec<&'a Clause<'a>>,
	    rbrack_pos:  Position<'a>
     },
    CondExpr {
        if_pos: Position<'a>,
        cond: &'a Expr<'a>,
        then_arm: &'a Expr<'a>,
        else_pos: Position<'a>,
        else_arm: &'a Expr<'a>,
    },
    DictEntry {
        key: &'a Expr<'a>,
        colon: Position<'a>,
        value: &'a Expr<'a>,
    },
    DictExpr {
        lbrace_pos: Position<'a>,
        list: Vec<&'a Expr<'a>>, // all *DictEntrys
        rbrace_pos: Position<'a>,
    },
    DotExpr {
        x: &'a Expr<'a>,
        dot: Position<'a>,
        name_pos: Position<'a>,
        name: Ident<'a>,
    },
    Ident(Ident<'a>),
    IndexExpr {
        x: &'a Expr<'a>,
        lbrack_pos: Position<'a>,
        y: &'a Expr<'a>,
        rbrack_pos: Position<'a>,
    },
    LambdaExpr {
        lambda_pos: Position<'a>,
        // param = ident | ident=expr | * | *ident | **ident
        params: Vec<&'a Expr<'a>>,
        body: &'a Expr<'a>,
    },
    ListExpr {
        lbrack_pos: Position<'a>,
        list: Vec<&'a Expr<'a>>,
        rbrack: Position<'a>,
    },
    Literal {
        token: Token, // = STRING | BYTES | INT | FLOAT
        token_pos: Position<'a>,
        raw: String, // uninterpreted text
    },
    ParenExpr {
        lparen: Position<'a>,
        x: &'a Expr<'a>,
        rparen: Position<'a>,
    },
    SliceExpr {
        x: &'a Expr<'a>,
        lbrack: &'a Position<'a>,
        lo: Option<&'a Expr<'a>>,
        hi: Option<&'a Expr<'a>>,
        step: Option<&'a Expr<'a>>,
        rbrack_pos: Position<'a>,
    },
    TupleExpr {
        lparen: Position<'a>, // optional (e.g. in x, y = 0, 1), but required if List is empty
        list: Vec<&'a Expr<'a>>,
        rparen: Position<'a>,
    },
    UnaryExpr {
        op_pos: Position<'a>,
        op: Token,
        x: Option<&'a Expr<'a>>, // may be nil if Op==STAR),
    },
}

pub struct Ident<'a> {
    pub name_pos: Position<'a>,
    pub name: String,
}

pub enum Clause<'a>  {
    // A ForClause represents a for clause in a list comprehension: "for Vars in X".
     
     ForClause {
        for_pos:  Position<'a>,
	    vars: &'a Expr<'a>, // name, or tuple of names
	    in_pos:   Position<'a>,
	    x:    &'a Expr<'a>
    }, 

    // An IfClause represents an if clause in a list comprehension: if Cond.
    IfClause {
	    if_pos:   Position<'a>,
	    cond: &'a Expr<'a>,
    }
}
