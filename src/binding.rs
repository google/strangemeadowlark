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

use std::borrow::Borrow;
use std::cell::RefCell;

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

impl Binding<'_> {
    pub fn undefined() -> Self {
        Binding {
            scope: RefCell::new(Scope::Undefined),
            index: 0,
            first: None,
        }
    }

    pub fn get_scope(&self) -> Scope {
        *self.scope.borrow()
    }
    pub fn set_scope(&self, scope: Scope) {
        *self.scope.borrow_mut() = scope
    }
}

// Reference
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct BindingIndex(pub usize);

// A Module contains resolver information about a file.
#[derive(Debug, PartialEq)]
pub struct Module<'a> {
    pub locals: Vec<BindingIndex>, // the file's (comprehension-)local variables
    pub globals: Vec<BindingIndex>, // the file's global variables
    pub functions: Vec<Function<'a>>,
    pub bindings: Vec<Binding<'a>>,
}

impl<'a> Module<'a> {
    pub fn binding<B: Borrow<BindingIndex>>(&self, b: B) -> &Binding<'a> {
        &self.bindings[b.borrow().0]
    }
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
    pub locals: RefCell<Vec<BindingIndex>>, // this function's local/cell variables, parameters first
    pub free_vars: RefCell<Vec<BindingIndex>>, // enclosing cells to capture in closure
}

impl<'a> Function<'a> {
    pub fn push_free_var(&self, v: BindingIndex) -> u8 {
        let mut vs = self.free_vars.borrow_mut();
        let index: u8 = vs.len().try_into().unwrap();
        vs.push(v);
        index
    }

    pub fn new_local(
        &self,
        id: &'a Ident<'a>,
        mk_binding: &mut dyn Fn(&'a Ident<'a>, usize) -> BindingIndex,
    ) -> BindingIndex {
        let v = mk_binding(id, self.locals.borrow().len());
        self.locals.borrow_mut().push(v);
        v
    }
}
