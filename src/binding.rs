use std::cell::RefCell;
use std::rc::Rc;

use crate::scan::Position;
use crate::syntax::{Expr, Stmt};
use crate::Ident;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Scope {
    Undefined,   // name is not defined
    Local,       // name is local to its function or file
    Cell,        // name is function-local but shared with a nested function
    Free,        // name is cell of some enclosing function
    Global,      // name is global to module
    Predeclared, // name is predeclared for this module (e.g. glob)
    Universal,   // name is universal (e.g. len)
}

impl std::fmt::Display for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Binding<'a> {
    pub scope: RefCell<Scope>,

    // Index records the index into the enclosing
    // - {DefStmt,File}.Locals, if Scope==Local
    // - DefStmt.FreeVars,      if Scope==Free
    // - File.Globals,          if Scope==Global.
    // It is zero if Scope is Predeclared, Universal, or Undefined.
    pub index: u8,

    // first binding use (iff Scope==Local/Free/Global)
    pub first: Option<&'a Ident<'a>>,
}

impl<'a> Binding<'a> {
    pub fn get_scope(&self) -> Scope {
        *self.scope.borrow()
    }
    pub fn set_scope(&self, scope: Scope) {
        *self.scope.borrow_mut() = scope
    }
}

// A Module contains resolver information about a file.
#[derive(Debug, PartialEq)]
pub struct Module<'a> {
    pub locals: Vec<Rc<Binding<'a>>>, // the file's (comprehension-)local variables
    pub globals: Vec<Rc<Binding<'a>>>, // the file's global variables
    pub functions: Vec<Function<'a>>,
}

#[derive(Debug, PartialEq)]
// A Function contains resolver information about a named or anonymous function.
// The resolver populates the Function field of each syntax.DefStmt and syntax.LambdaExpr.
pub struct Function<'a> {
    pub pos: Position,              // of DEF or LAMBDA
    pub name: &'a str,              // name of def, or "lambda"
    pub params: &'a [&'a Expr<'a>], // param = ident | ident=expr | * | *ident | **ident
    pub body: &'a [&'a Stmt<'a>],   // contains synthetic 'return expr' for lambda

    pub has_varargs: RefCell<bool>, // whether params includes *args (convenience)
    pub has_kwargs: RefCell<bool>,  // whether params includes **kwargs (convenience)
    pub num_kwonly_params: RefCell<u8>, // number of keyword-only optional parameters
    pub locals: RefCell<Vec<Rc<Binding<'a>>>>, // this function's local/cell variables, parameters first
    pub free_vars: RefCell<Vec<Rc<Binding<'a>>>>, // enclosing cells to capture in closure
}

impl<'a> Function<'a> {
    pub fn push_free_var(&self, v: &Rc<Binding<'a>>) -> u8 {
        let mut vs = self.free_vars.borrow_mut();
        let index: u8 = vs.len().try_into().unwrap();
        vs.push(v.clone());
        index
    }
}
