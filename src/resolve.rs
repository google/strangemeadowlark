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

#![allow(unused)]

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::rc::Rc;

use crate::binding::{Binding, BindingIndex, Function, Module, Scope};
use crate::scan::Position;
use crate::syntax::*;
use crate::token::Token;
use crate::{Arena, ID_GEN};
use thiserror::Error;

type Result<T> = std::result::Result<T, ResolveError>;

// All references to names are statically resolved.  Names may be
// predeclared, global, or local to a function or file.
// File-local variables include those bound by top-level comprehensions
// and by load statements. ("Top-level" means "outside of any function".)
// The resolver maps each global name to a small integer and each local
// name to a small integer; these integers enable a fast and compact
// representation of globals and locals in the evaluator.
//
// As an optimization, the resolver classifies each predeclared name as
// either universal (e.g. None, len) or per-module (e.g. glob in Bazel's
// build language), enabling the evaluator to share the representation
// of the universal environment across all modules.
//
// The lexical environment is a tree of blocks with the file block at
// its root. The file's child blocks may be of two kinds: functions
// and comprehensions, and these may have further children of either
// kind.
//
// Python-style resolution requires multiple passes because a name is
// determined to be local to a function only if the function contains a
// "binding" use of it; similarly, a name is determined to be global (as
// opposed to predeclared) if the module contains a top-level binding use.
// Unlike ordinary top-level assignments, the bindings created by load
// statements are local to the file block.
// A non-binding use may lexically precede the binding to which it is resolved.
// In the first pass, we inspect each function, recording in
// 'uses' each identifier and the environment block in which it occurs.
// If a use of a name is binding, such as a function parameter or
// assignment, we add the name to the block's bindings mapping and add a
// local variable to the enclosing function.
//
// As we finish resolving each function, we inspect all the uses within
// that function and discard ones that were found to be function-local. The
// remaining ones must be either free (local to some lexically enclosing
// function), or top-level (global, predeclared, or file-local), but we cannot tell
// which until we have finished inspecting the outermost enclosing
// function. At that point, we can distinguish local from top-level names
// (and this is when Python would compute free variables).
//
// However, Starlark additionally requires that all references to global
// names are satisfied by some declaration in the current module;
// Starlark permits a function to forward-reference a global or file-local
// that has not
// been declared yet so long as it is declared before the end of the
// module.  So, instead of re-resolving the unresolved references after
// each top-level function, we defer this until the end of the module
// and ensure that all such references are satisfied by some definition.
//
// At the end of the module, we visit each of the nested function blocks
// in bottom-up order, doing a recursive lexical lookup for each
// unresolved name.  If the name is found to be local to some enclosing
// function, we must create a DefStmt.FreeVar (capture) parameter for
// each intervening function.  We enter these synthetic bindings into
// the bindings map so that we create at most one freevar per name.  If
// the name was not local, we check that it was defined at module level.
//
// We resolve all uses of locals in the module (due to load statements
// and comprehensions) in a similar way and compute the file's set of
// local variables.
//
// Starlark enforces that all global names are assigned at most once on
// all control flow paths by forbidding if/else statements and loops at
// top level. A global may be used before it is defined, leading to a
// dynamic error. However, the AllowGlobalReassign flag (really: allow
// top-level reassign) makes the resolver allow multiple to a variable
// at top-level. It also allows if-, for-, and while-loops at top-level,
// which in turn may make the evaluator dynamically assign multiple
// values to a variable at top-level. (These two roles should be separated.)

pub struct FileUnitWithModule<'u, 'a> {
    pub file_unit: &'u FileUnit<'a>,
    pub module: Module<'a>,
}

const DEBUG: bool = false;
const DOESNT: &str = "this Starlark dialect does not ";

const FILE_BLOCK: usize = 0;

// An Error describes the nature and position of a resolver error.
#[derive(Error, Debug, Clone)]
pub enum ResolveError {
    #[error("{path}:{pos} undefined: {name}")]
    Undefined {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} duplicate parameter: {name}")]
    DuplicateParameter {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} required parameter may not follow **{name}")]
    RequiredParameterMayNotFollowStarStar {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} required parameter may not follow optional")]
    RequiredParameterMayNotFollowOptional { path: String, pos: Position },
    #[error("{path}:{pos} optional parameter may not follow **{name}")]
    OptionalParameterMayNotFollowStarStar {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} * parameter may not follow **{name}")]
    StarMayNotFollowStarStart {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} bare * must be followed by keyword-only parameters")]
    StarMustBeFollowedByKeywordOnlyParameters { path: String, pos: Position },
    #[error("{path}:{pos} multiple * parameters not allowed")]
    MultipleStarParametersNotAllowed { path: String, pos: Position },
    #[error("{path}:{pos} multiple ** parameters not allowed")]
    MultipleStarStarParametersNotAllowed { path: String, pos: Position },
    #[error("{path}:{pos} cannot reassign {scope} {name} declared at {first}")]
    GlobalReassign {
        path: String,
        pos: Position,
        scope: Scope,
        name: String,
        first: Position,
    },
    #[error("{path}:{pos} load stmt within a function")]
    LoadWithinFunction { path: String, pos: Position },
    #[error("{path}:{pos} load stmt within a loop")]
    LoadWithinLoop { path: String, pos: Position },
    #[error("{path}:{pos} load stmt within if statement")]
    LoadWithinIf { path: String, pos: Position },
    #[error("{path}:{pos} cannot reassign top-level")]
    LoadCannotReassignTopLevel {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} load: empty identifier")]
    LoadEmptyIdentifier { path: String, pos: Position },
    #[error("{path}:{pos} load: names with leading _ are not exported")]
    LoadNameWithLeadingUnderscore { path: String, pos: Position },
    #[error("{path}:{pos} if statement not within a function")]
    IfNotWithinFunction { path: String, pos: Position },
    #[error("{path}:{pos} return stmt not within a function")]
    ReturnNotWithinFunction { path: String, pos: Position },
    #[error("{path}:{pos} for loop not within a function")]
    ForLoopNotWithinFunction { path: String, pos: Position },
    #[error("{path}:{pos} while loop not within a function")]
    WhileLoopNotWithinFunction { path: String, pos: Position },
    #[error("{path}:{pos} encountered {token} outside of loop")]
    BranchNotInLoop {
        path: String,
        pos: Position,
        token: Token,
    },
    #[error("{path}:{pos} encountered {num} positional arguments in call, limit is 255")]
    TooManyPositionalArgumentsInCall {
        path: String,
        pos: Position,
        num: i32,
    },
    #[error("{path}:{pos} encountered {num} keyword arguments in call, limit is 255")]
    TooManyKeywordArgumentsInCall {
        path: String,
        pos: Position,
        num: i32,
    },
    #[error("{path}:{pos} multiple **kwargs not allowed")]
    MultipleKeywordArgsNotAllowed { path: String, pos: Position },
    #[error("{path}:{pos} args may not follow **kwargs")]
    ArgsMayNotFollowKeywordArgs { path: String, pos: Position },
    #[error("{path}:{pos} multiple **kwargs not allowed")]
    MultipleStarStarArgsNotAllowed { path: String, pos: Position },
    #[error("{path}:{pos} keyword argument may not follow *args")]
    KeywordArgumentMayNotFollowStarStarKeywordArgs { path: String, pos: Position },
    #[error("{path}:{pos} keyword argument may not follow **kwargs")]
    KeywordArgumentMayNotFollowStarKeywordArgs { path: String, pos: Position },
    #[error("{path}:{pos} keyword argument {name}")]
    KeywordArgumentIsRepeated {
        path: String,
        pos: Position,
        name: String,
    },
    #[error("{path}:{pos} positional argument may not follow *arg")]
    PositionalArgumentMayNotFollowStarArg { path: String, pos: Position },
    #[error("{path}:{pos} positional argument may not follow **kwarg")]
    PositionalArgumentMayNotFollowStarStarArg { path: String, pos: Position },
    #[error("{path}:{pos} positional argument may not follow named arg")]
    PositionalArgumentMayNotFollowNamed { path: String, pos: Position },
    #[error("{path}:{pos} cannot use tuple expression in augmented assignment")]
    CannotUseTupleinAugmentedAssign { path: String, pos: Position },
    #[error("{path}:{pos} cannot use list expression in augmented assignment")]
    CannotUseListinAugmentedAssign { path: String, pos: Position },
    #[error("{path}:{pos} cannot assign to this expression")]
    CannotAssign { path: String, pos: Position },
}

// File resolves the specified file and records information about the
// module in file.Module.
//
// The isPredeclared and isUniversal predicates report whether a name is
// a pre-declared identifier (visible in the current module) or a
// universal identifier (visible in every module).
// Clients should typically pass predeclared.Has for the first and
// starlark.Universe.Has for the second, where predeclared is the
// module's StringDict of predeclared names and starlark.Universe is the
// standard set of built-ins.
// The isUniverse predicate is supplied a parameter to avoid a cyclic
// dependency upon starlark.Universe, not because users should ever need
// to redefine it.
pub fn resolve_file<'u, 'a>(
    file: &'u FileUnit<'a>,
    arena: &'a Arena,
    is_predeclared: fn(&str) -> bool,
    is_universal: fn(&str) -> bool,
) -> std::result::Result<FileUnitWithModule<'u, 'a>, Vec<ResolveError>> {
    repl_chunk(file, arena, None, is_predeclared, is_universal)
}

// REPLChunk is a generalization of the File function that supports a
// non-empty initial global block, as occurs in a REPL.
pub fn repl_chunk<'u, 'a>(
    file_unit: &'u FileUnit<'a>,
    arena: &'a Arena,
    is_global: Option<fn(&str) -> bool>,
    is_predeclared: fn(&str) -> bool,
    is_universal: fn(&str) -> bool,
) -> std::result::Result<FileUnitWithModule<'u, 'a>, Vec<ResolveError>> {
    let mut r = Resolver::new(
        arena,
        file_unit.path,
        is_global,
        is_predeclared,
        is_universal,
    );
    r.stmts(FILE_BLOCK, file_unit.stmts);
    r.resolve_local_uses(FILE_BLOCK);

    // At the end of the module, resolve all non-local variable references,
    // computing closures.
    // Function bodies may contain forward references to later global declarations.
    r.resolve_non_local_uses(FILE_BLOCK);

    if !r.errors.borrow().is_empty() {
        return Err(r.errors.borrow().clone());
    }
    Ok(FileUnitWithModule {
        file_unit,
        module: Module {
            locals: r.module_locals.take(),
            globals: r.module_globals.take(),
            functions: r.functions.take(),
            bindings: r.bindings.take(),
        },
    })
}

// A use records an identifier and the environment in which it appears.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Use<'a> {
    id: &'a Ident<'a>,
    env: usize,
}

// Block used for lexical scoping.
#[derive(Debug, PartialEq)]
pub struct Block<'a> {
    parent: usize,

    // In the file (root) block, both these fields are nil.
    function: Option<usize>, // only for function blocks, index into functions
    comp: Option<&'a ExprData<'a>>, // only for comprehension blocks

    // bindings maps a name to its binding (which are all stored in the module).
    // A local binding has an index into its innermost enclosing container's locals array.
    // A free binding has an index into its innermost enclosing function's freevars array.
    bindings: RefCell<HashMap<&'a str, BindingIndex>>,

    // children records the child blocks of the current one.
    children: RefCell<Vec<usize>>,

    // uses records all identifiers seen in this container (function or file),
    // and a reference to the environment in which they appear.
    // As we leave each container block, we resolve them,
    // so that only free and global ones remain.
    // At the end of each top-level function we compute closures.
    uses: RefCell<Vec<Use<'a>>>,
}

impl<'a> Block<'a> {
    fn new_file() -> Self {
        Block {
            parent: 0,
            function: None,
            comp: None,
            bindings: RefCell::new(HashMap::new()),
            children: RefCell::new(vec![]),
            uses: RefCell::new(vec![]),
        }
    }

    fn from_comp(parent: usize, comp: &'a ExprData<'a>) -> Self {
        Block {
            parent,
            function: None,
            comp: Some(comp),
            bindings: RefCell::new(HashMap::new()),
            children: RefCell::new(vec![]),
            uses: RefCell::new(vec![]),
        }
    }

    fn from_function(parent: usize, function_index: usize) -> Self {
        Block {
            parent,
            function: Some(function_index),
            comp: None,
            bindings: RefCell::new(HashMap::new()),
            children: RefCell::new(vec![]),
            uses: RefCell::new(vec![]),
        }
    }

    fn bind(&self, name: &'a str, bindx: BindingIndex) {
        self.bindings.borrow_mut().insert(name, bindx);
    }
}

pub struct Resolver<'a> {
    arena: &'a Arena,
    path: &'a Path,
    // file = blocks[0]
    blocks: Vec<Block<'a>>,
    bindings: RefCell<Vec<Binding<'a>>>,
    // moduleLocals contains the local variables of the module
    // (due to load statements and comprehensions outside any function).
    // moduleGlobals contains the global variables of the module.
    module_locals: RefCell<Vec<BindingIndex>>,
    module_globals: RefCell<Vec<BindingIndex>>,
    functions: RefCell<Vec<Function<'a>>>,
    // globals maps each global name in the module to its binding.
    // predeclared does the same for predeclared and universal names.
    globals: RefCell<HashMap<&'a str, BindingIndex>>,
    predeclared: RefCell<HashMap<&'a str, BindingIndex>>,

    // These predicates report whether a name is
    // pre-declared, either in this module or universally,
    // or already declared in the module globals (as in a REPL).
    // isGlobal may be nil.
    is_global: Option<fn(&str) -> bool>,
    is_predeclared: fn(&str) -> bool,
    is_universal: fn(&str) -> bool,

    loops: u16,   // number of enclosing for/while loops
    ifstmts: u16, // number of enclosing if statements loops

    errors: RefCell<Vec<ResolveError>>,
}

impl<'arena> Resolver<'arena> {
    fn new(
        arena: &'arena Arena,
        path: &'arena Path,
        is_global: Option<fn(&str) -> bool>,
        is_predeclared: fn(&str) -> bool,
        is_universal: fn(&str) -> bool,
    ) -> Self {
        Resolver {
            arena,
            path,
            blocks: vec![Block::new_file()],
            bindings: RefCell::new(vec![]),
            is_global,
            is_predeclared,
            is_universal,
            module_locals: RefCell::new(Vec::new()),
            module_globals: RefCell::new(Vec::new()),
            functions: RefCell::new(Vec::new()),
            globals: RefCell::new(HashMap::new()),
            predeclared: RefCell::new(HashMap::new()),
            loops: 0,
            ifstmts: 0,
            errors: RefCell::new(vec![]),
        }
    }

    fn path_string(&self) -> String {
        self.path.to_string_lossy().to_string()
    }

    fn push_block(&mut self, block: Block<'arena>) -> usize {
        let index = self.blocks.len();
        self.blocks[block.parent].children.borrow_mut().push(index);
        self.blocks.push(block);
        index
    }

    fn block(&self, index: usize) -> &Block<'arena> {
        &self.blocks[index]
    }

    fn new_binding(&self, b: Binding<'arena>) -> BindingIndex {
        let index = self.bindings.borrow().len();
        self.bindings.borrow_mut().push(b);
        BindingIndex(index)
    }

    fn push_module_local(&self, id: &'arena Ident<'arena>) -> BindingIndex {
        let bindx = self.new_binding(Binding {
            first: Some(id),
            scope: RefCell::new(Scope::Local),
            index: self.module_locals.borrow().len() as _,
        });
        self.module_locals.borrow_mut().push(bindx);
        bindx
    }

    fn push_module_global(&self, id: &'arena Ident<'arena>) -> BindingIndex {
        let bindx = self.new_binding(Binding {
            first: Some(id),
            scope: RefCell::new(Scope::Global),
            index: self.module_globals.borrow().len() as _,
        });
        self.module_globals.borrow_mut().push(bindx);
        bindx
    }

    // resolveLocalUses is called when leaving a container (function/module)
    // block.  It resolves all uses of locals/cells within that block.
    fn resolve_local_uses(&mut self, index: usize) {
        let b = self.block(index);
        let mut unresolved: Vec<Use<'arena>> = vec![];
        for u in b.uses.borrow_mut().drain(..) {
            match self.lookup_local(&u) {
                Some(bindx) => {
                    let bind = &self.bindings.borrow()[bindx.0];
                    if matches!(bind.get_scope(), Scope::Local | Scope::Cell) {
                        u.id.set_binding(bindx)
                    } else {
                        unresolved.push(u)
                    }
                }
                _ => unresolved.push(u),
            }
        }
        *b.uses.borrow_mut() = unresolved
    }

    // lookupLocal looks up an identifier within its immediately enclosing function.
    fn lookup_local(&self, u: &Use) -> Option<BindingIndex> {
        let mut env = u.env;
        let mut b = self.block(env);
        loop {
            if let Some(bindx) = b.bindings.borrow().get(u.id.name) {
                let bind = &self.bindings.borrow()[bindx.0];
                if bind.get_scope() == Scope::Free {
                    // shouldn't exist till later
                    panic!(
                        "{}: internal error: {}, {:?}",
                        u.id.name_pos, u.id.name, bind
                    )
                }
                return Some(*bindx);
            }

            if b.function.is_some() {
                break;
            }

            if b.parent != FILE_BLOCK {
                env = b.parent;
                b = self.block(env);
            } else {
                break;
            }
        }
        None
    }

    // lookup_lexical looks up an identifier use.id within its lexically enclosing environment.
    // The use.env field captures the original environment for error reporting.
    // This function can update scope as a side-effect.
    fn lookup_lexical(&self, u: Use<'arena>, env: usize) -> Option<BindingIndex> {
        if DEBUG {
            println!("lookupLexical {} in {:?} = ...", u.id.name, env);
        }

        if env == FILE_BLOCK {
            let bind = self.use_top_level(u); // file-local, global, predeclared, or not found
            if DEBUG {
                println!("= {bind:?}\n");
            }
            return bind;
        }

        // Defined in this block?
        let b = self.block(env);
        let mut memoize = false;

        let bindx = b.bindings.borrow().get(u.id.name).copied();
        if bindx.is_some() {
            return bindx;
        }

        // Defined in parent block?
        let bindx = self.lookup_lexical(u, b.parent);
        // If not, we are done.
        bindx?;

        let mut bindx = bindx.unwrap();
        let mut binding_to_add: Option<Binding> = None;
        {
            let bind = &self.bindings.borrow()[bindx.0];
            if let Some(fun_index) = b.function
                && matches!(bind.get_scope(), Scope::Local | Scope::Free | Scope::Cell) {
                    let function = &self.functions.borrow()[fun_index];
                    // Found in parent block, which belongs to enclosing function.
                    // Add the parent's binding to the function's freevars,
                    // and add a new 'free' binding to the inner function's block,
                    // and turn the parent's local into cell.
                    if bind.get_scope() == Scope::Local {
                        bind.set_scope(Scope::Cell)
                    }
                    let index: u8 = function.push_free_var(bindx);
                    if DEBUG {
                        println!(
                            "creating freevar {} in function at {}: {}\n",
                            index + 1,
                            function.pos,
                            u.id.name
                        )
                    }
                    binding_to_add = Some(Binding {
                        first: bind.first,
                        scope: RefCell::new(Scope::Free),
                        index,
                    });
                };
        }
        if let Some(bind) = binding_to_add {
            bindx = self.new_binding(bind)
        }
        // Memoize, to avoid duplicate free vars
        // and redundant global (failing) lookups.
        b.bind(u.id.name, bindx);
        if DEBUG {
            println!("= {:?}\n", &self.bindings.borrow()[bindx.0]);
        }

        Some(bindx)
    }

    fn stmts(&mut self, env: usize, stmts: &'arena [StmtRef<'arena>]) {
        for stmt in stmts {
            self.stmt(env, stmt);
        }
    }

    fn stmt(&mut self, env: usize, stmt: StmtRef<'arena>) {
        match &stmt.data {
            StmtData::ExprStmt { x } => self.expr(env, x),

            StmtData::BranchStmt { token, token_pos } => {
                if self.loops == 0 && (*token == Token::Break || *token == Token::Continue) {
                    self.push_error(ResolveError::BranchNotInLoop {
                        path: self.path_string(),
                        pos: *token_pos,
                        token: token.clone(),
                    })
                }
            }

            StmtData::IfStmt {
                if_pos,
                cond,
                then_arm,
                else_pos,
                else_arm,
            } => {
                if self.container(env).function.is_none() {
                    self.errors
                        .borrow_mut()
                        .push(ResolveError::IfNotWithinFunction {
                            path: self.path_string(),
                            pos: *if_pos,
                        })
                }
                self.expr(env, cond);
                self.ifstmts += 1;
                self.stmts(env, then_arm);
                self.stmts(env, else_arm);
                self.ifstmts -= 1;
            }

            StmtData::AssignStmt {
                op_pos,
                op,
                lhs,
                rhs,
            } => {
                self.expr(env, rhs);
                let is_augmented = *op != Token::Eq;
                self.assign(env, lhs, is_augmented);
            }
            StmtData::DefStmt {
                def_pos,
                name,
                lparen,
                params,
                rparen,
                body,
                function,
            } => {
                self.bind(env, name);
                let fun_index = self.functions.borrow().len();
                self.functions.borrow_mut().push(Function {
                    pos: *def_pos,
                    name: name.name,
                    params,
                    body,
                    has_varargs: RefCell::new(false),
                    has_kwargs: RefCell::new(false),
                    num_kwonly_params: RefCell::new(0),
                    locals: RefCell::new(vec![]),
                    free_vars: RefCell::new(vec![]),
                });
                self.function(env, fun_index);
                *function.borrow_mut() = Some(fun_index);
            }
            StmtData::ForStmt {
                for_pos,
                vars,
                x,
                body,
            } => {
                // Assuming !option.TopLevelControl
                if self.container(env).function.is_none() {
                    self.push_error(ResolveError::ForLoopNotWithinFunction {
                        path: self.path_string(),
                        pos: *for_pos,
                    });
                }
                self.expr(env, x);
                let is_augmented = false;
                self.assign(env, vars, is_augmented);
                self.loops += 1;
                self.stmts(env, body);
                self.loops -= 1;
            }
            StmtData::WhileStmt {
                while_pos,
                cond,
                body,
            } => {
                // Assuming option.While and !option.TopLevelControl
                if self.container(env).function.is_none() {
                    self.push_error(ResolveError::WhileLoopNotWithinFunction {
                        path: self.path_string(),
                        pos: *while_pos,
                    });
                }
                self.expr(env, cond);
                self.loops += 1;
                self.stmts(env, body);
                self.loops -= 1;
            }
            StmtData::LoadStmt {
                load_pos,
                module,
                from,
                to,
                rparen_pos,
            } => {
                if self.container(env).function.is_some() {
                    self.push_error(ResolveError::LoadWithinFunction {
                        path: self.path_string(),
                        pos: *load_pos,
                    });
                } else if self.loops > 0 {
                    self.push_error(ResolveError::LoadWithinLoop {
                        path: self.path_string(),
                        pos: *load_pos,
                    });
                } else if self.ifstmts > 0 {
                    self.push_error(ResolveError::LoadWithinIf {
                        path: self.path_string(),
                        pos: *load_pos,
                    });
                }
                for (i, from) in from.iter().enumerate() {
                    if from.name.is_empty() {
                        self.push_error(ResolveError::LoadEmptyIdentifier {
                            path: self.path_string(),
                            pos: from.name_pos,
                        });
                        continue;
                    }
                    if from.name.starts_with('_') {
                        self.push_error(ResolveError::LoadNameWithLeadingUnderscore {
                            path: self.path_string(),
                            pos: from.name_pos,
                        });
                    }
                    let id = to[i];
                    // Assume !LoadBindsGlobally
                    if self.bind_local(env, id) {
                        self.push_error(ResolveError::LoadCannotReassignTopLevel {
                            path: self.path_string(),
                            pos: id.name_pos,
                            name: id.name.to_string(),
                        });
                    }
                }
            }
            StmtData::ReturnStmt { return_pos, result } => {
                if self.container(env).function.is_none() {
                    self.push_error(ResolveError::ReturnNotWithinFunction {
                        path: self.path_string(),
                        pos: *return_pos,
                    });
                }
                if let Some(result) = result {
                    self.expr(env, result);
                }
            }
        }
    }

    fn assign(&mut self, env: usize, lhs: &'arena Expr<'arena>, is_augmented: bool) {
        match lhs.data {
            ExprData::Ident(id) => {
                // x = ...
                self.bind(env, id);
            }
            ExprData::IndexExpr { x, y, .. } => {
                // x[i] = ...
                self.expr(env, x);
                self.expr(env, y);
            }

            ExprData::DotExpr { x, .. } =>
            // x.f = ...
            {
                self.expr(env, x)
            }

            ExprData::TupleExpr { list, .. } => {
                // (x, y) = ...
                if is_augmented {
                    self.push_error(ResolveError::CannotUseTupleinAugmentedAssign {
                        path: self.path_string(),
                        pos: lhs.span.start,
                    })
                }
                for elem in list.iter() {
                    self.assign(env, elem, is_augmented)
                }
            }
            ExprData::ListExpr { list, .. } => {
                // [x, y, z] = ...
                if is_augmented {
                    self.push_error(ResolveError::CannotUseListinAugmentedAssign {
                        path: self.path_string(),
                        pos: lhs.span.start,
                    })
                }
                for elem in list {
                    self.assign(env, elem, is_augmented)
                }
            }
            ExprData::ParenExpr { x, .. } => self.assign(env, x, is_augmented),
            _ => self.push_error(ResolveError::CannotAssign {
                path: self.path_string(),
                pos: lhs.span.start,
            }),
        }
    }

    // container returns the innermost enclosing "container" block:
    // a function (function != nil) or file (function == nil).
    // Container blocks accumulate local variable bindings.
    fn container(&self, mut env: usize) -> &Block<'arena> {
        let mut b = self.block(env);
        loop {
            if b.function.is_some() || env == FILE_BLOCK
            /* file */
            {
                return b;
            }
            env = b.parent;
        }
    }

    fn push_error(&self, e: ResolveError) {
        self.errors.borrow_mut().push(e)
    }

    // bind creates a binding for id: a global (not file-local)
    // binding at top-level, a local binding otherwise.
    // At top-level, it reports an error if a global or file-local
    // binding already exists, unless AllowGlobalReassign.
    // It sets id.Binding to the binding (whether old or new),
    // and returns whether a binding already existed.
    fn bind(&mut self, env: usize, id: &'arena Ident<'arena>) -> bool {
        // Binding outside any local (comprehension/function) block?
        if env == FILE_BLOCK {
            let file = self.block(FILE_BLOCK);
            let (mut bindx, ok) = match file.bindings.borrow_mut().get(id.name) {
                None => match self.globals.borrow_mut().entry(id.name) {
                    Entry::Vacant(e) => {
                        // first global binding of this name
                        let bindx = self.push_module_global(id);
                        e.insert(bindx);
                        (bindx, false)
                    }
                    Entry::Occupied(e) => (*e.get(), true),
                },
                Some(bindx) => (*bindx, true),
            };
            if !ok
                && let Entry::Vacant(e) = self.globals.borrow_mut().entry(id.name) {
                    // first global binding of this name
                    bindx = self.push_module_global(id);
                    e.insert(bindx);
                }
            // Assuming !self.options.GlobalReassign
            if ok {
                let bind = &self.bindings.borrow()[bindx.0];
                if let Some(first) = bind.first {
                    self.push_error(ResolveError::GlobalReassign {
                        path: self.path_string(),
                        pos: id.name_pos,
                        scope: *bind.scope.borrow(),
                        name: id.name.to_string(),
                        first: first.name_pos,
                    })
                }
            }
            *id.binding.borrow_mut() = Some(bindx);
            return ok;
        }

        self.bind_local(env, id)
    }

    /// Returns true if a binding already existed for this name.
    fn bind_local(&mut self, env: usize, id: &'arena Ident<'arena>) -> bool {
        let b = self.block(env);
        // Mark this name as local to current block.
        // Assign it a new local (positive) index in the current container.
        let ok = b.bindings.borrow().contains_key(&id.name);
        if !ok {
            if let Some(fun_index) = &self.container(env).function {
                let fun = &self.functions.borrow()[*fun_index];
                let bindx = fun.new_local(id, &mut |id, index| {
                    self.new_binding(Binding {
                        first: Some(id),
                        scope: RefCell::new(Scope::Local),
                        index: index as u8,
                    })
                });
                b.bind(id.name, bindx);
            } else {
                b.bind(id.name, self.push_module_local(id));
            }
        }

        self.r#use(env, id);
        ok
    }

    fn r#use(&self, env: usize, id: &'arena Ident<'arena>) {
        let u = Use { id, env };
        let b = self.container(env);
        let uses: &mut Vec<Use> = &mut b.uses.borrow_mut();
        uses.push(u);
    }

    // use_top_level resolves u.id as a reference to a name visible at top-level.
    // The u.env field captures the original environment for error reporting.
    fn use_top_level(&self, u: Use<'arena>) -> Option<BindingIndex> {
        let is_global = if let Some(is_global) = self.is_global {
            is_global
        } else {
            |_: &str| false
        };
        let id = u.id;

        let bindx: BindingIndex =
            if let Some(prev) = self.block(FILE_BLOCK).bindings.borrow().get(id.name) {
                // use of load-defined name in file block
                *prev
            } else if let Some(prev) = self.globals.borrow().get(id.name) {
                // use of global declared by module
                return Some(*prev);
            } else if is_global(id.name) {
                // use of global defined in a previous REPL chunk
                // setting ".first" is wrong: this is not even a binding use
                let bindx = self.push_module_global(id);
                self.globals.borrow_mut().insert(id.name, bindx);
                bindx
            } else if let Some(prev) = self.predeclared.borrow().get(id.name) {
                // repeated use of predeclared or universal
                *prev
            } else if (self.is_predeclared)(id.name) {
                // use of pre-declared name
                let bindx = self.new_binding(Binding {
                    scope: RefCell::new(Scope::Predeclared),
                    index: 0,
                    first: None,
                });
                self.predeclared.borrow_mut().insert(id.name, bindx); // save it
                bindx
            } else if (self.is_universal)(id.name) {
                // use of universal name
                /*
                if !self.options.Set && id.name == "set" {
                    //self.push_error(id.name_pos, doesnt+"support sets")
                    panic!("todo")
                }
                 */
                let bindx = self.new_binding(Binding {
                    scope: RefCell::new(Scope::Universal),
                    index: 0,
                    first: None,
                });
                self.predeclared.borrow_mut().insert(id.name, bindx); // save it
                bindx
            } else {
                id.set_binding(self.new_binding(Binding::undefined()));
                self.push_error(ResolveError::Undefined {
                    path: self.path_string(),
                    pos: id.name_pos,
                    name: id.name.to_string(),
                });

                return None;
            };
        id.set_binding(bindx);
        Some(bindx)
    }

    fn expr(&mut self, env: usize, e: ExprRef<'arena>) {
        match &e.data {
            ExprData::Ident(id) => self.r#use(env, id),

            ExprData::Literal { .. } => {}

            ExprData::ListExpr { list, .. } => {
                for x in list.iter() {
                    self.expr(env, x)
                }
            }

            ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                self.expr(env, cond);
                self.expr(env, then_arm);
                self.expr(env, else_arm)
            }

            ExprData::IndexExpr { x, y, .. } => {
                self.expr(env, x);
                self.expr(env, y)
            }

            ExprData::DictEntry { key, value, .. } => {
                self.expr(env, key);
                self.expr(env, value)
            }
            ExprData::SliceExpr {
                x, lo, hi, step, ..
            } => {
                self.expr(env, x);
                if let Some(lo) = lo {
                    self.expr(env, lo)
                }
                if let Some(hi) = hi {
                    self.expr(env, hi)
                }
                if let Some(step) = step {
                    self.expr(env, step)
                }
            }
            comp @ ExprData::Comprehension { clauses, body, .. } =>
            // The 'in' operand of the first clause (always a ForClause)
            // is resolved in the outer block; consider: [x for x in x].
            {
                if let clause @ Clause::ForClause { x, vars, .. } = clauses[0] {
                    self.expr(env, x);

                    // A list/dict comprehension defines a new lexical block.
                    // Locals defined within the block will be allotted
                    // distinct slots in the locals array of the innermost
                    // enclosing container (function/module) block.
                    let env = self.push_block(Block::from_comp(env, comp));

                    let is_augmented = false;
                    self.assign(env, vars, is_augmented);

                    for clause in &clauses[1..] {
                        match clause {
                            Clause::IfClause { cond, .. } => self.expr(env, cond),
                            Clause::ForClause { vars, x, .. } => {
                                self.assign(env, vars, is_augmented);
                                self.expr(env, x)
                            }
                        }
                    }
                    self.expr(env, body); // body may be *DictEntry
                } else {
                    panic!("unexpected: {}", clauses[0])
                }
            }
            ExprData::TupleExpr { list, .. } => {
                for x in list.iter() {
                    self.expr(env, x);
                }
            }

            ExprData::DictExpr { list, .. } => {
                for entry in list.iter() {
                    if let ExprData::DictEntry { key, value, .. } = entry.data {
                        self.expr(env, key);
                        self.expr(env, value);
                    }
                }
            }
            ExprData::UnaryExpr { x, .. } => {
                if let Some(x) = x {
                    self.expr(env, x)
                }
            }

            ExprData::BinaryExpr { x, y, .. } => {
                self.expr(env, x);
                self.expr(env, y)
            }

            ExprData::DotExpr { x, .. } => self.expr(env, x),
            // ignore e.Name
            ExprData::CallExpr { func, args, .. } => {
                self.expr(env, func);
                let mut seen_varargs = false;
                let mut seen_kwargs = false;

                /*
                var n, p int
                */
                let mut n = 0;
                let mut p = 0;
                let mut seen_name: HashSet<&str> = HashSet::new();
                for arg in args.iter() {
                    let pos = arg.span.start;
                    match arg.data {
                        ExprData::UnaryExpr {
                            op: Token::StarStar,
                            ..
                        } => {
                            // **kwargs
                            if seen_kwargs {
                                self.push_error(ResolveError::MultipleKeywordArgsNotAllowed {
                                    path: self.path_string(),
                                    pos,
                                })
                            }
                            seen_kwargs = true;
                            self.expr(env, arg)
                        }
                        ExprData::UnaryExpr {
                            op: Token::Star, ..
                        } => {
                            // *args
                            if seen_kwargs {
                                self.push_error(ResolveError::ArgsMayNotFollowKeywordArgs {
                                    path: self.path_string(),
                                    pos,
                                });
                            } else if seen_varargs {
                                self.push_error(ResolveError::MultipleStarStarArgsNotAllowed {
                                    path: self.path_string(),
                                    pos,
                                });
                            }
                            seen_varargs = true;
                            self.expr(env, arg)
                        }
                        ExprData::BinaryExpr {
                            op: Token::Eq,
                            x:
                                Expr {
                                    data: ExprData::Ident(id),
                                    ..
                                },
                            y,
                            ..
                        } => {
                            // k=v
                            n += 1;
                            if seen_kwargs {
                                self.push_error(
                                    ResolveError::KeywordArgumentMayNotFollowStarStarKeywordArgs {
                                        path: self.path_string(),
                                        pos,
                                    },
                                );
                            } else if seen_varargs {
                                self.push_error(
                                    ResolveError::KeywordArgumentMayNotFollowStarKeywordArgs {
                                        path: self.path_string(),
                                        pos,
                                    },
                                );
                            }
                            if seen_name.contains(id.name) {
                                self.push_error(ResolveError::KeywordArgumentIsRepeated {
                                    path: self.path_string(),
                                    pos: id.name_pos,
                                    name: id.name.to_string(),
                                })
                            } else {
                                seen_name.insert(id.name);
                            }
                            self.expr(env, y)
                        }
                        _ => {
                            // positional argument
                            p += 1;
                            if seen_varargs {
                                self.push_error(
                                    ResolveError::PositionalArgumentMayNotFollowStarArg {
                                        path: self.path_string(),
                                        pos,
                                    },
                                )
                            } else if seen_kwargs {
                                self.push_error(
                                    ResolveError::PositionalArgumentMayNotFollowStarStarArg {
                                        path: self.path_string(),
                                        pos,
                                    },
                                )
                            } else if !seen_name.is_empty() {
                                self.push_error(
                                    ResolveError::PositionalArgumentMayNotFollowNamed {
                                        path: self.path_string(),
                                        pos,
                                    },
                                );
                            }
                            self.expr(env, arg)
                        }
                    }

                    // Fail gracefully if compiler-imposed limit is exceeded.
                    if p >= 256 {
                        self.push_error(ResolveError::TooManyPositionalArgumentsInCall {
                            path: self.path_string(),
                            pos: arg.span.start,
                            num: n,
                        });
                    }
                    if n >= 256 {
                        self.push_error(ResolveError::TooManyKeywordArgumentsInCall {
                            path: self.path_string(),
                            pos: arg.span.start,
                            num: n,
                        });
                    }
                }
            }
            ExprData::LambdaExpr {
                params,
                body,
                function,
                ..
            } => {
                let fun_index = self.functions.borrow().len();
                self.functions.borrow_mut().push(Function {
                    name: "lambda",
                    pos: e.span.start,
                    params,
                    body: self.arena.alloc_slice_copy(&[&*self.arena.alloc(Stmt {
                        id: ID_GEN.next_stmt_id(),
                        span: e.span,
                        data: StmtData::ReturnStmt {
                            result: Some(body),
                            return_pos: e.span.start,
                        },
                    })]),
                    has_kwargs: RefCell::new(false),
                    has_varargs: RefCell::new(false),
                    num_kwonly_params: RefCell::new(0),
                    locals: RefCell::new(vec![]),
                    free_vars: RefCell::new(vec![]),
                });
                self.function(env, fun_index);
                *function.borrow_mut() = Some(fun_index);
            }
            ExprData::ParenExpr { x, .. } => self.expr(env, x),

            _ => panic!("unexpected expr {e:?}"),
        }
    }

    fn function(&mut self, env: usize, fun_index: usize) {
        let params: &[&Expr<'arena>] = {
            let fun = &self.functions.borrow()[fun_index];
            fun.params
        };
        // Resolve defaults in enclosing environment.
        for param in params.iter() {
            if let ExprData::BinaryExpr { y, .. } = param.data {
                self.expr(env, y);
            }
        }

        // Enter function block.
        let env = self.push_block(Block::from_function(env, fun_index));
        let mut seen_optional = false;
        let mut star: Option<&Expr> = None; // * or *args param
        let mut star_star: Option<&Ident> = None; // **kwargs ident
        let mut num_kwonly_params = 0;
        let params = {
            let fun_index = *self.block(env).function.as_ref().unwrap();
            let fun = &self.functions.borrow()[fun_index];
            fun.params
        };
        for param in params {
            match &param.data {
                ExprData::Ident(p) => {
                    // e.g. x
                    if let Some(star_star) = star_star {
                        self.push_error(ResolveError::RequiredParameterMayNotFollowStarStar {
                            path: self.path_string(),
                            pos: p.name_pos,
                            name: star_star.name.to_string(),
                        });
                    } else if star.is_some() {
                        num_kwonly_params += 1;
                    } else if seen_optional {
                        self.push_error(ResolveError::RequiredParameterMayNotFollowOptional {
                            path: self.path_string(),
                            pos: p.name_pos,
                        });
                    }
                    if self.bind(env, p) {
                        self.push_error(ResolveError::DuplicateParameter {
                            path: self.path_string(),
                            pos: p.name_pos,
                            name: p.name.to_string(),
                        });
                    }
                }
                ExprData::BinaryExpr { x, op_pos, .. } => {
                    // e.g. y=dflt
                    if let Some(star_star) = star_star {
                        self.push_error(ResolveError::OptionalParameterMayNotFollowStarStar {
                            path: self.path_string(),
                            pos: *op_pos,
                            name: star_star.name.to_string(),
                        });
                    } else if star.is_some() {
                        num_kwonly_params += 1
                    }
                    if let ExprData::Ident(id) = x.data
                        && self.bind(env, id) {
                            self.push_error(ResolveError::DuplicateParameter {
                                path: self.path_string(),
                                pos: *op_pos,
                                name: id.name.to_string(),
                            });
                        }
                    seen_optional = true
                }
                ExprData::UnaryExpr { op, op_pos, x, .. } => {
                    // * or *args or **kwargs
                    if *op == Token::Star {
                        if let Some(star_star) = star_star {
                            self.push_error(ResolveError::StarMayNotFollowStarStart {
                                path: self.path_string(),
                                pos: *op_pos,
                                name: star_star.name.to_string(),
                            });
                        } else if star.is_some() {
                            self.push_error(ResolveError::MultipleStarParametersNotAllowed {
                                path: self.path_string(),
                                pos: *op_pos,
                            });
                        } else {
                            star = Some(param)
                        }
                    } else {
                        if star_star.is_some() {
                            self.push_error(ResolveError::MultipleStarStarParametersNotAllowed {
                                path: self.path_string(),
                                pos: *op_pos,
                            })
                        }
                        if let Some(ExprData::Ident(x)) = x.map(|x| &x.data) {
                            star_star = Some(x)
                        }
                    }
                }
                _ => {
                    panic!("unexpected {param:?}")
                }
            }
        }

        // Bind the *args and **kwargs parameters at the end,
        // so that regular parameters a/b/c are contiguous and
        // there is no hole for the "*":
        //   def f(a, b, *args, c=0, **kwargs)
        //   def f(a, b, *,     c=0, **kwargs)
        if let Some(star) = star {
            if let ExprData::Ident(id) = star.data {
                // *args
                if self.bind(env, id) {
                    self.push_error(ResolveError::DuplicateParameter {
                        path: self.path_string(),
                        pos: id.name_pos,
                        name: id.name.to_string(),
                    });
                }
                let fun = &self.functions.borrow()[fun_index];
                *fun.has_varargs.borrow_mut() = true;
            } else if num_kwonly_params == 0 {
                self.push_error(ResolveError::StarMustBeFollowedByKeywordOnlyParameters {
                    path: self.path_string(),
                    pos: star.span.start,
                });
            }
        }
        if let Some(star_star) = star_star {
            if self.bind(env, star_star) {
                self.push_error(ResolveError::DuplicateParameter {
                    path: self.path_string(),
                    pos: star_star.name_pos,
                    name: star_star.name.to_string(),
                });
            }
            let functions = self.functions.borrow();
            let fun = &functions[fun_index];
            *fun.has_kwargs.borrow_mut() = true;
        }
        let stmts = {
            let fun = &self.functions.borrow()[fun_index];
            *fun.num_kwonly_params.borrow_mut() = num_kwonly_params;
            fun.body
        };
        self.stmts(env, stmts);

        // Resolve all uses of this function's local vars,
        // and keep just the remaining uses of free/global vars.
        self.resolve_local_uses(env);

        // Leave function block.
        //self.pop()

        // References within the function body to globals are not
        // resolved until the end of the module.
    }

    fn resolve_non_local_uses(&self, env: usize) {
        let b = self.block(env);
        // First resolve inner blocks.
        for child in b.children.borrow().iter() {
            self.resolve_non_local_uses(*child)
        }
        let uses = b.uses.borrow();
        for u in uses.iter().copied() {
            if let Some(b) = self.lookup_lexical(u, u.env) {
                u.id.set_binding(b);
            }
        }
    }
} // impl

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::{Result, anyhow};
    use googletest::prelude::*;

    use crate::{FileUnit, Mode, parse};
    fn prepare<'a>(arena: &'a Arena, input: &'a str) -> Result<(FileUnit<'a>, Module<'a>)> {
        let file_unit = parse(arena, input)?;
        let res = resolve_file(&file_unit, arena, |s| false, |s| false).map_err(|e| anyhow!("{e:?}"))?;
        let FileUnitWithModule { module, .. } = res;
        Ok((file_unit, module))
    }

    #[test]
    fn basic_file_global() -> Result<()> {
        let arena = Arena::new();
        let input = "a = 3";
        let (file_unit, module) = prepare(&arena, input)?;

        assert_eq!(module.globals.len(), 1);
        let bx = module.globals[0];
        let b = &module.bindings[bx.0];
        assert_that!(b.get_scope(), eq(Scope::Global));
        assert_that!(b.index, eq(0));
        if let Some(id) = b.first {
            assert_that!(id.name, eq("a"));
        } else {
            fail!("first is 0");
        }
        Ok(())
    }

    #[test]
    fn basic_file_global_error() -> googletest::Result<()> {
        let arena = Arena::new();
        let input = "a = 3\na = 4";
        let f = prepare(&arena, input);

        // Expect error due to global reassign.
        verify_that!(f.is_err(), eq(true))
    }

    #[derive(MatcherBase)]
    struct IdentHasName {
        expected: String,
    }

    impl Matcher<Option<&'_ Ident<'_>>> for IdentHasName {
        fn matches(&self, actual: Option<&'_ Ident<'_>>) -> googletest::matcher::MatcherResult {
            if let Some(actual) = actual {
                (self.expected == actual.name).into()
            } else {
                false.into()
            }
        }

        fn describe(
            &self,
            matcher_result: googletest::matcher::MatcherResult,
        ) -> googletest::description::Description {
            match matcher_result {
                googletest::matcher::MatcherResult::Match => {
                    format!("has name {:?}", self.expected).into()
                }
                googletest::matcher::MatcherResult::NoMatch => {
                    format!("does not have name {:?}", self.expected).into()
                }
            }
        }
    }
    fn ident_has_name(name: &str) -> IdentHasName {
        IdentHasName {
            expected: name.to_owned(),
        }
    }

    #[test]
    fn basic_file_local() -> Result<()> {
        let arena = Arena::new();
        let input = "def f(b):\n  a = b\na = 2";
        let (file_unit, module) = prepare(&arena, input)?;

        assert_eq!(module.globals.len(), 2);
        let bx = module.globals[0];
        let b = &module.bindings[bx.0];

        assert_that!(b.get_scope(), eq(Scope::Global));
        assert_eq!(b.index, 0);
        assert_that!(b.first, ident_has_name("f"));

        let bx = &module.globals[1];
        let b = &module.bindings[bx.0];
        assert_eq!(b.get_scope(), Scope::Global);
        assert_eq!(b.index, 1);
        assert_that!(b.first, ident_has_name("a"));

        Ok(())
    }

    #[test]
    fn load_comprehension_local() -> Result<()> {
        let arena = Arena::new();
        let input = "load('foo.sl', 'bar', baz='bak')\n[x for x in baz if bar]";
        let (file_unit, module) = prepare(&arena, input)?;

        assert_eq!(module.locals.len(), 3);
        let bx = module.locals[0];
        let b = &module.bindings[bx.0];
        assert_eq!(b.get_scope(), Scope::Local);
        assert_eq!(b.index, 0);
        assert_that!(b.first, ident_has_name("bar"));

        let bx = module.locals[1];
        let b = &module.bindings[bx.0];
        assert_eq!(b.get_scope(), Scope::Local);
        assert_eq!(b.index, 1);
        assert_that!(b.first, ident_has_name("baz"));

        let bx = module.locals[2];
        let b = &module.bindings[bx.0];
        assert_eq!(b.get_scope(), Scope::Local);
        assert_eq!(b.index, 2);
        assert_that!(b.first, ident_has_name("x"));

        Ok(())
    }

    #[test]
    fn nestedvar() -> Result<()> {
        let arena = Arena::new();
        let input = "
def nested(x):   # x has Scope::Cell
  def update(d): # has a freevar x
    def f(d):    # has a freevar x
      d[0] = x
    f(d)
  e = {}
  update(e)
  return e
";
        let (file_unit, module) = prepare(&arena, input)?;
        assert_eq!(module.globals.len(), 1);
        let bx = &module.globals[0];
        let b = &module.bindings[bx.0];
        assert_eq!(b.get_scope(), Scope::Global);
        assert_eq!(b.index, 0);
        assert_that!(b.first, ident_has_name("nested"));

        assert_eq!(file_unit.stmts.len(), 1);
        if let StmtData::DefStmt {
            function,
            def_pos,
            body,
            ..
        } = &file_unit.stmts[0].data
        {
            if let Some(fun_index) = *function.borrow() {
                let fun = &module.functions[fun_index];
                assert_eq!(fun.free_vars.borrow().len(), 0);
                let locals = &fun.locals.borrow();
                assert_eq!(locals.len(), 3);

                let local = &module.bindings[locals[0].0];
                assert_eq!(local.get_scope(), Scope::Cell);
                assert_that!(local.first, ident_has_name("x"));

                let local = &module.bindings[locals[1].0];
                assert_eq!(local.get_scope(), Scope::Local);
                assert_that!(local.first, ident_has_name("update"));

                let local = &module.bindings[locals[2].0];
                assert_eq!(local.get_scope(), Scope::Local);
                assert_that!(local.first, ident_has_name("e"));

                assert!(!body.is_empty());
                if let StmtData::DefStmt {
                    function,
                    def_pos,
                    body,
                    ..
                } = &body[0].data
                {
                    if let Some(fun_index) = *function.borrow() {
                        let fun = &module.functions[fun_index];

                        assert_eq!(fun.free_vars.borrow().len(), 1);
                        let bindx = fun.free_vars.borrow()[0];
                        let bind = &module.bindings[bindx.0];

                        assert_eq!(bind.get_scope(), Scope::Cell);
                        assert_that!(bind.first, ident_has_name("x"));

                        let locals = fun.locals.borrow();
                        assert_eq!(locals.len(), 2);

                        let local = &module.bindings[locals[0].0];
                        assert_that!(local.first, ident_has_name("d"));

                        let local = &module.bindings[locals[1].0];
                        assert_that!(local.first, ident_has_name("f"));

                        if let StmtData::DefStmt {
                            function,
                            def_pos,
                            body,
                            ..
                        } = &body[0].data
                        {
                            let fun = &module.functions[fun_index];

                            assert_eq!(fun.free_vars.borrow().len(), 1);
                            let bindx = fun.free_vars.borrow()[0];
                            let bind = &module.bindings[bindx.0];

                            assert_eq!(bind.get_scope(), Scope::Cell);
                            assert_that!(bind.first, ident_has_name("x"));

                            if let StmtData::AssignStmt {
                                rhs:
                                    Expr {
                                        data: ExprData::Ident(id),
                                        ..
                                    },
                                ..
                            } = &body[0].data
                            {
                                let bindx = id.binding.borrow().unwrap();
                                let local = &module.bindings[bindx.0];
                                assert_eq!(local.get_scope(), Scope::Free);
                                assert_that!(bind.first, ident_has_name("x"));
                                Ok(())
                            } else {
                                Err(anyhow!("unexpected body of function `f`"))
                            }
                        } else {
                            Err(anyhow!("function `f` not resolved"))
                        }
                    } else {
                        Err(anyhow!("function `update` not resolved"))
                    }
                } else {
                    Err(anyhow!("function `nested` not resolved"))
                }
            } else {
                Err(anyhow!("function `nested` not resolved"))
            }
        } else {
            Err(anyhow!("no defstmt found for `nested`"))
        }
    }

    #[test]
    fn test_body() -> Result<()> {
        let arena = Arena::new();
        let input = "
def fib(n):
  if n == 0:
    return 1
  if n == 1:
    return 1
  x = 1
  y = 1
  i = 0
  while i < n:
    tmp = x
    x = y
    y = x + tmp
  return y
";
        let _ = prepare(&arena, input)?;
        Ok(())
    }

    #[test]
    fn test_undefined() -> Result<()> {
        let arena = Arena::new();
        let input = "
def fib(n):
  while i < n:
    n = i + 1
  return i
";
        let f = prepare(&arena, input);

        if let Err(e) = f {
            Ok(())
        } else {
            Err(anyhow!(
                "expected error due to undefined var {:?}.",
                f.unwrap().0
            ))
        }
    }

    #[test]
    fn test_weird_defined() -> Result<()> {
        let arena = Arena::new();
        let input = "
def spec_says_fails_at_runtime(n):
  while i < n:
    i = i + 1
  return i
";
        let _ = prepare(&arena, input)?;
        Ok(())
    }

    #[test]
    fn test_reference_local() -> Result<()> {
        let arena = Arena::new();
        let input = r#"
load("foo.scl", "foo")

def bar(x):
  foo(foo(x))

y = bar(1)
"#;
        let _ = prepare(&arena, input)?;
        Ok(())
    }
}
