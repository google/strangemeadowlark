#![allow(unused)]

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::binding::{Binding, Function, Module, Scope};
use crate::scan::Position;
use crate::syntax::*;
use crate::token::Token;
use anyhow::{anyhow, Result};
use bumpalo::Bump;

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

pub struct FileUnitWithModule<'a> {
    file_unit: &'a FileUnit<'a>,
    module: Module<'a>,
}

const DEBUG: bool = false;
const DOESNT: &str = "this Starlark dialect does not ";

const FILE_BLOCK: usize = 0;

// An Error describes the nature and position of a resolver error.
#[derive(Debug)]
struct Error {
    pos: Position,
    msg: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.pos, self.msg)
    }
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
pub fn resolve_file<'a>(
    file: &'a FileUnit<'a>,
    bump: &'a Bump,
    is_predeclared: fn(&str) -> bool,
    is_universal: fn(&str) -> bool,
) -> Result<&'a FileUnitWithModule<'a>> {
    repl_chunk(file, bump, None, is_predeclared, is_universal)
}

// REPLChunk is a generalization of the File function that supports a
// non-empty initial global block, as occurs in a REPL.
pub fn repl_chunk<'a>(
    file: &'a FileUnit<'a>,
    bump: &'a Bump,
    is_global: Option<fn(&str) -> bool>,
    is_predeclared: fn(&str) -> bool,
    is_universal: fn(&str) -> bool,
) -> Result<&'a FileUnitWithModule<'a>> {
    let file_block = bump.alloc(Block::new_file());
    let blocks = vec![&*file_block];
    let r = bump.alloc(Resolver::new(
        bump,
        blocks,
        is_global,
        is_predeclared,
        is_universal,
    ));
    r.stmts(FILE_BLOCK, file.stmts);
    r.resolve_local_uses(file_block);

    // At the end of the module, resolve all non-local variable references,
    // computing closures.
    // Function bodies may contain forward references to later global declarations.
    r.resolve_non_local_uses(FILE_BLOCK);

    if !r.errors.borrow().is_empty() {
        return Err(anyhow!("errors: {:?}", r.errors.borrow()));
    }
    let mut module_locals = vec![];
    for v in r.module_locals.borrow().iter() {
        module_locals.push(v.clone())
    }
    let mut module_globals = vec![];
    for v in r.module_globals.borrow().iter() {
        module_globals.push(v.clone())
    }
    Ok(bump.alloc(FileUnitWithModule {
        file_unit: file,
        module: Module {
            locals: module_locals,
            globals: module_globals,
        },
    }))
}

// A use records an identifier and the environment in which it appears.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Use<'a> {
    id: &'a Ident<'a>,
    env: usize,
}

#[derive(Debug, PartialEq)]
pub struct Block<'a> {
    parent: usize,

    // In the file (root) block, both these fields are nil.
    function: Option<&'a Function<'a>>, // only for function blocks
    comp: Option<&'a ExprData<'a>>,     // only for comprehension blocks

    // bindings maps a name to its binding.
    // A local binding has an index into its innermost enclosing container's locals array.
    // A free binding has an index into its innermost enclosing function's freevars array.
    bindings: RefCell<HashMap<&'a str, Rc<Binding<'a>>>>,

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

    fn from_function(parent: usize, function: &'a Function<'a>) -> Self {
        Block {
            parent,
            function: Some(function),
            comp: None,
            bindings: RefCell::new(HashMap::new()),
            children: RefCell::new(vec![]),
            uses: RefCell::new(vec![]),
        }
    }

    fn bind(&'a self, name: &'a str, bind: Rc<Binding<'a>>) {
        self.bindings.borrow_mut().insert(name, bind.clone());
    }
}

pub struct Resolver<'a> {
    bump: &'a Bump,
    // file = blocks[0]
    blocks: RefCell<Vec<&'a Block<'a>>>,
    // moduleLocals contains the local variables of the module
    // (due to load statements and comprehensions outside any function).
    // moduleGlobals contains the global variables of the module.
    module_locals: RefCell<Vec<Rc<Binding<'a>>>>,
    module_globals: RefCell<Vec<Rc<Binding<'a>>>>,

    // globals maps each global name in the module to its binding.
    // predeclared does the same for predeclared and universal names.
    globals: RefCell<HashMap<&'a str, Rc<Binding<'a>>>>,
    predeclared: RefCell<HashMap<&'a str, Rc<Binding<'a>>>>,

    // These predicates report whether a name is
    // pre-declared, either in this module or universally,
    // or already declared in the module globals (as in a REPL).
    // isGlobal may be nil.
    is_global: Option<fn(&str) -> bool>,
    is_predeclared: fn(&str) -> bool,
    is_universal: fn(&str) -> bool,

    loops: u16,   // number of enclosing for/while loops
    ifstmts: u16, // number of enclosing if statements loops

    errors: RefCell<Vec<Error>>,
}

impl<'a> Resolver<'a> {
    fn new(
        bump: &'a Bump,
        blocks: Vec<&'a Block<'a>>,
        is_global: Option<fn(&str) -> bool>,
        is_predeclared: fn(&str) -> bool,
        is_universal: fn(&str) -> bool,
    ) -> Self {
        Resolver {
            bump,
            blocks: RefCell::new(blocks),
            //env: RefCell::new(file_block),
            is_global,
            is_predeclared,
            is_universal,
            module_locals: RefCell::new(Vec::new()),
            module_globals: RefCell::new(Vec::new()),
            globals: RefCell::new(HashMap::new()),
            predeclared: RefCell::new(HashMap::new()),
            loops: 0,
            ifstmts: 0,
            errors: RefCell::new(vec![]),
        }
    }

    // resolveLocalUses is called when leaving a container (function/module)
    // block.  It resolves all uses of locals/cells within that block.
    fn resolve_local_uses(&'a self, b: &'a Block<'a>) {
        let mut unresolved: Vec<Use<'a>> = vec![];
        for u in b.uses.borrow_mut().drain(..) {
            match self.lookup_local(&u) {
                Some(bind) if matches!(bind.get_scope(), Scope::Local | Scope::Cell) => {
                    u.id.set_binding(&bind)
                }
                _ => unresolved.push(u),
            }
        }
        *b.uses.borrow_mut() = unresolved
    }

    // lookupLocal looks up an identifier within its immediately enclosing function.
    fn lookup_local<'b>(&self, u: &'b Use) -> Option<Rc<Binding<'a>>> {
        let mut env = u.env;
        let mut b = self.blocks.borrow()[env];
        loop {
            match b.bindings.borrow().get(u.id.name) {
                Some(bind) => {
                    if bind.get_scope() == Scope::Free {
                        // shouldn't exist till later
                        panic!(
                            "{}: internal error: {}, {:?}",
                            u.id.name_pos, u.id.name, bind
                        )
                    }
                    return Some(bind.clone());
                }
                _ => {}
            }

            if b.function.is_some() {
                break;
            }

            if b.parent != FILE_BLOCK {
                env = b.parent;
                b = self.blocks.borrow()[env];
            } else {
                break;
            }
        }
        return None;
    }

    // lookup_lexical looks up an identifier use.id within its lexically enclosing environment.
    // The use.env field captures the original environment for error reporting.
    fn lookup_lexical(&'a self, u: Use<'a>, env: usize) -> Rc<Binding> {
        if DEBUG {
            println!("lookupLexical {} in {:?} = ...", u.id.name, env);
        }

        if env == FILE_BLOCK {
            let bind = self.use_top_level(u); // file-local, global, predeclared, or not found
            if DEBUG {
                println!("= {:?}\n", bind);
            }
            return bind;
        }

        // Defined in this block?
        let b = self.blocks.borrow()[env];
        match b.bindings.borrow().get(u.id.name) {
            Some(bind) => bind.clone(),
            None => {
                let parent = b.parent;
                // Defined in parent block?
                let mut bind = self.lookup_lexical(u, parent);
                match &b.function {
                    Some(function)
                        if matches!(bind.get_scope(), Scope::Local | Scope::Free | Scope::Cell) =>
                    {
                        // Found in parent block, which belongs to enclosing function.
                        // Add the parent's binding to the function's freevars,
                        // and add a new 'free' binding to the inner function's block,
                        // and turn the parent's local into cell.
                        if bind.get_scope() == Scope::Local {
                            bind.set_scope(Scope::Cell)
                        }
                        let index: u8 = function.push_free_var(&bind);
                        bind = Rc::new(Binding {
                            first: bind.first,
                            scope: RefCell::new(Scope::Free),
                            index,
                        });
                        if DEBUG {
                            println!(
                                "creating freevar {} in function at {}: {}\n",
                                index + 1,
                                function.pos,
                                u.id.name
                            )
                        }
                    }
                    _ => {}
                }

                // Memoize, to avoid duplicate free vars
                // and redundant global (failing) lookups.
                b.bind(u.id.name, bind.clone());
                if DEBUG {
                    println!("= {:?}\n", bind);
                }
                bind
            }
        }
    }

    fn stmts(&'a self, env: usize, stmts: &'a [StmtRef<'a>]) {
        for stmt in stmts {
            self.stmt(env, stmt);
        }
    }

    fn stmt(&'a self, env: usize, stmt: StmtRef<'a>) {
        match &stmt.data {
            StmtData::ExprStmt { x } => self.expr(env, x),

            StmtData::BranchStmt { token, token_pos } => {
                if self.loops == 0 && (*token == Token::Break || *token == Token::Continue) {
                    self.errorf(token_pos.clone(), format!("{} not in a loop", token))
                }
            }

            StmtData::IfStmt {
                if_pos,
                cond,
                then_arm,
                else_pos,
                else_arm,
            } => {
                if let None = self.container(env).function {
                    self.errors.borrow_mut().push(Error {
                        pos: if_pos.clone(),
                        msg: format!("if statement not within a function"),
                    })
                }
                self.expr(env, &cond);
                //self.ifstmts++
                self.stmts(env, then_arm);
                self.stmts(env, else_arm);
                //self.ifstmts--
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
                let f = Function {
                    pos: *def_pos,
                    name: name.name,
                    params,
                    body,
                    has_varargs: RefCell::new(false),
                    has_kwargs: RefCell::new(false),
                    num_kwonly_params: RefCell::new(0),
                    locals: RefCell::new(vec![]),
                    free_vars: RefCell::new(vec![]),
                };
                let f = self.function(env, f);
                *function.borrow_mut() = Some(f);
            }
            StmtData::ForStmt {
                for_pos,
                vars,
                x,
                body,
            } => {
                // Assuming !option.TopLevelControl
                if self.container(env).function.is_none() {
                    self.errorf(*for_pos, "for loop not within a function".to_string());
                }
                self.expr(env, x);
                let is_augmented = false;
                self.assign(env, vars, is_augmented);
                self.stmts(env, body);
            }
            StmtData::WhileStmt {
                while_pos,
                cond,
                body,
            } => {
                // Assuming option.While and !option.TopLevelControl
                if self.container(env).function.is_none() {
                    self.errorf(*while_pos, "while loop not within a function".to_string());
                }
                self.expr(env, cond);
                self.stmts(env, body);
            }
            StmtData::LoadStmt {
                load_pos,
                module,
                from,
                to,
                rparen_pos,
            } => {
                if self.container(env).function.is_some() {
                    self.errorf(*load_pos, "load stmt within a function".to_string());
                }
                for (i, from) in from.iter().enumerate() {
                    if from.name.is_empty() {
                        self.errorf(from.name_pos, "load: empty identifier".to_string());
                        continue;
                    }
                    if from.name.starts_with('_') {
                        self.errorf(
                            from.name_pos,
                            "load: names with leading _ are not exported".to_string(),
                        );
                    }
                    let id = to[i];
                    // Assume !LoadBindsGlobally
                    if self.bind_local(env, id) {
                        self.errorf(
                            id.name_pos,
                            format!("cannot reassign top-level {}", id.name),
                        );
                    }
                }
            }
            StmtData::ReturnStmt { return_pos, result } => {
                if self.container(env).function.is_none() {
                    self.errorf(*return_pos, "return stmt not within a function".to_string());
                }
            }
        }
    }

    fn assign(&'a self, env: usize, lhs: &'a Expr<'a>, is_augmented: bool) {
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
                    self.errorf(
                        lhs.span.start,
                        "can't use tuple expression in augmented assignment".to_string(),
                    )
                }
                for elem in list.iter() {
                    self.assign(env, elem, is_augmented)
                }
            }
            ExprData::ListExpr { list, .. } => {
                // [x, y, z] = ...
                if is_augmented {
                    self.errorf(
                        lhs.span.start,
                        "can't use list expression in augmented assignment".to_string(),
                    )
                }
                for elem in list {
                    self.assign(env, elem, is_augmented)
                }
            }
            ExprData::ParenExpr { x, .. } => self.assign(env, x, is_augmented),
            _ => self.errorf(lhs.span.start, format!("can't assign to {}", lhs.data)),
        }
    }

    /*
    // Expr calls [ExprOptions] using [syntax.LegacyFileOptions].
    //
    // Deprecated: use [ExprOptions] with [syntax.FileOptions] instead,
    // because this function relies on legacy global variables.
    func Expr(expr syntax.Expr, isPredeclared, isUniversal func(name string) bool) ([]*Binding, error) {
        return ExprOptions(syntax.LegacyFileOptions(), expr, isPredeclared, isUniversal)
    }

    // ExprOptions resolves the specified expression.
    // It returns the local variables bound within the expression.
    //
    // The isPredeclared and isUniversal predicates behave as for the File function
    func ExprOptions(opts *syntax.FileOptions, expr syntax.Expr, isPredeclared, isUniversal func(name string) bool) ([]*Binding, error) {
        r := newResolver(opts, nil, isPredeclared, isUniversal)
        self.expr(expr)
        self.env.resolveLocalUses()
        self.resolveNonLocalUses(self.env) // globals & universals
        if len(self.errors) > 0 {
            return nil, self.errors
        }
        return self.moduleLocals, nil
    }

    // An ErrorList is a non-empty list of resolver error messages.
    type ErrorList []Error // len > 0

    func (e ErrorList) Error() string { return e[0].Error() }

    func (e Error) Error() string { return e.Pos.String() + ": " + e.Msg }

    func newResolver(options *syntax.FileOptions, isGlobal, isPredeclared, isUniversal func(name string) bool) *resolver {
        file := new(block)
        return &resolver{
            options:       options,
            file:          file,
            env:           file,
            isGlobal:      isGlobal,
            isPredeclared: isPredeclared,
            isUniversal:   isUniversal,
            globals:       make(map[string]*Binding),
            predeclared:   make(map[string]*Binding),
        }
    }

    */

    // container returns the innermost enclosing "container" block:
    // a function (function != nil) or file (function == nil).
    // Container blocks accumulate local variable bindings.
    fn container(&'a self, mut env: usize) -> &'a Block<'a> {
        let mut b = &self.blocks.borrow()[env];
        loop {
            if b.function.is_some() || env == FILE_BLOCK
            /* file */
            {
                return b;
            }
            env = b.parent;
        }
    }

    fn errorf(&self, pos: Position, msg: String) {
        self.errors.borrow_mut().push(Error { pos, msg })
    }

    //fn push(&'a self, b: &'a Block) {
    //    self.env.borrow_mut().children.push(b);
    //    *b.parent.borrow_mut() = Some(*self.env.borrow());
    //    *self.env.borrow_mut() = b
    //}

    //fn pop(&self) { *self.env.borrow_mut() = (*self.env.borrow()).parent.unwrap() }
    /*

    func (b *block) String() string {
        if b.function != nil {
            return "function block at " + fmt.Sprint(b.function.Pos)
        }
        if b.comp != nil {
            return "comprehension block at " + fmt.Sprint(b.comp.Span())
        }
        return "file block"
    }


    // A use records an identifier and the environment in which it appears.
    type use struct {
        id  *syntax.Ident
        env *block
    }*/

    // bind creates a binding for id: a global (not file-local)
    // binding at top-level, a local binding otherwise.
    // At top-level, it reports an error if a global or file-local
    // binding already exists, unless AllowGlobalReassign.
    // It sets id.Binding to the binding (whether old or new),
    // and returns whether a binding already existed.
    fn bind(&'a self, env: usize, id: &'a Ident<'a>) -> bool {
        // Binding outside any local (comprehension/function) block?
        if env == FILE_BLOCK {
            let file = self.blocks.borrow()[0];
            let (mut bind, ok) = match file.bindings.borrow_mut().get(id.name) {
                None => match self.globals.borrow_mut().entry(id.name) {
                    Entry::Vacant(e) => {
                        // first global binding of this name
                        let bind = Rc::new(Binding {
                            first: Some(id),
                            scope: RefCell::new(Scope::Global),
                            index: self.module_globals.borrow().len() as _,
                        });
                        e.insert(Rc::clone(&bind));
                        self.module_globals.borrow_mut().push(Rc::clone(&bind));
                        (bind, false)
                    }
                    Entry::Occupied(e) => (e.get().clone(), true),
                },
                Some(bind) => (bind.clone(), true),
            };
            if !ok {
                match self.globals.borrow_mut().entry(id.name) {
                    Entry::Vacant(e) => {
                        // first global binding of this name
                        bind = Rc::new(Binding {
                            first: Some(id),
                            scope: RefCell::new(Scope::Global),
                            index: self.module_globals.borrow().len() as _,
                        });
                        e.insert(Rc::clone(&bind));
                        self.module_globals.borrow_mut().push(Rc::clone(&bind));
                    }
                    _ => {}
                }
            }
            // Assuming !self.options.GlobalReassign
            if ok {
                if let Some(first) = bind.first {
                    self.errorf(
                        id.name_pos,
                        format!(
                            "cannot reassign {} {} declared at {:?}",
                            bind.scope.borrow(),
                            id.name,
                            first
                        ),
                    )
                }
            }
            *id.binding.borrow_mut() = Some(bind);
            return ok;
        }

        return self.bind_local(env, &id);
    }

    fn bind_local(&'a self, env: usize, id: &'a Ident<'a>) -> bool {
        let b = self.blocks.borrow()[env];
        // Mark this name as local to current block.
        // Assign it a new local (positive) index in the current container.
        let ok = b.bindings.borrow().contains_key(&id.name);
        if !ok {
            if let Some(fnc) = &self.container(env).function {
                let bind = Rc::new(Binding {
                    first: Some(id),
                    scope: RefCell::new(Scope::Local),
                    index: fnc.locals.borrow().len() as _,
                });
                b.bind(id.name, Rc::clone(&bind));
                fnc.locals.borrow_mut().push(bind);
            } else {
                let bind = Rc::new(Binding {
                    first: Some(id),
                    scope: RefCell::new(Scope::Local),
                    index: self.module_locals.borrow().len() as _,
                });
                b.bind(id.name, Rc::clone(&bind));
                self.module_locals.borrow_mut().push(bind);
            }
        }

        self.r#use(env, id);
        return ok;
    }

    fn r#use(&'a self, env: usize, id: &'a Ident<'a>) {
        let u = Use { id, env };
        // Assuming !GlobalReassign
        /* if self.options.GlobalReassign && ...
        if env == FILE_BLOCK {
            self.use_top_level(u);
            return;
        }
        */
        let b = self.container(env);
        b.uses.borrow_mut().push(u)
    }

    // use_top_level resolves u.id as a reference to a name visible at top-level.
    // The u.env field captures the original environment for error reporting.
    fn use_top_level(&self, u: Use<'a>) -> Rc<Binding<'a>> {
        let is_global = if let Some(is_global) = self.is_global {
            is_global
        } else {
            |_: &str| false
        };
        let id = u.id;

        let bind: Rc<Binding> = if let Some(prev) = self.blocks.borrow()[FILE_BLOCK]
            .bindings
            .borrow()
            .get(id.name)
        {
            // use of load-defined name in file block
            Rc::clone(prev)
        } else if let Some(prev) = self.globals.borrow().get(id.name) {
            // use of global declared by module
            return prev.clone();
        } else if is_global(id.name) {
            // use of global defined in a previous REPL chunk
            let bind = Rc::new(Binding {
                first: Some(id), // wrong: this is not even a binding use
                scope: RefCell::new(Scope::Global),
                index: self.module_globals.borrow().len().try_into().unwrap(),
            });
            self.globals.borrow_mut().insert(id.name, bind.clone());
            self.module_globals.borrow_mut().push(bind.clone());
            bind
        } else if let Some(prev) = self.predeclared.borrow().get(id.name) {
            // repeated use of predeclared or universal
            prev.clone()
        } else if (self.is_predeclared)(id.name) {
            // use of pre-declared name
            let bind = Rc::new(Binding {
                scope: RefCell::new(Scope::Predeclared),
                index: 0,
                first: None,
            });
            self.predeclared.borrow_mut().insert(id.name, bind.clone()); // save it
            bind
        } else if (self.is_universal)(id.name) {
            // use of universal name
            /*
            if !self.options.Set && id.name == "set" {
                //self.errorf(id.name_pos, doesnt+"support sets")
                panic!("todo")
            }
             */
            let bind = Rc::new(Binding {
                scope: RefCell::new(Scope::Universal),
                index: 0,
                first: None,
            });
            self.predeclared.borrow_mut().insert(id.name, bind.clone()); // save it
            bind
        } else {
            let bind = Rc::new(Binding {
                scope: RefCell::new(Scope::Undefined),
                index: 0,
                first: None,
            });
            //var hint string
            //if n := self.spellcheck(use); n != "" {
            //	hint = fmt.Sprintf(" (did you mean %s?)", n)
            //}
            self.errorf(id.name_pos, format!("undefined: {}", id.name /* , hint*/));
            bind
        };
        id.set_binding(&bind);
        return bind;
    }

    /*
    // spellcheck returns the most likely misspelling of
    // the name use.id in the environment use.env.
    func (r *resolver) spellcheck(use use) string {
        var names []string

        // locals
        for b := use.env; b != nil; b = b.parent {
            for name := range b.bindings {
                names = append(names, name)
            }
        }

        // globals
        //
        // We have no way to enumerate the sets whose membership
        // tests are isPredeclared, isUniverse, and isGlobal,
        // which includes prior names in the REPL session.
        for _, bind := range self.moduleGlobals {
            names = append(names, bind.First.Name)
        }

        sort.Strings(names)
        return spell.Nearest(use.id.Name, names)
    }
    */
    fn expr(&'a self, env: usize, e: ExprRef<'a>) {
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
                    let index = self.blocks.borrow().len();
                    let b = self.bump.alloc(Block::from_comp(env, &comp));
                    self.blocks.borrow_mut().push(b);
                    b.children.borrow_mut().push(index);
                    let env = index;

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
                    let pos = arg.span.start.clone();
                    match arg.data {
                        ExprData::UnaryExpr {
                            op: Token::StarStar,
                            ..
                        } => {
                            // **kwargs
                            if seen_kwargs {
                                self.errorf(pos, "multiple **kwargs not allowed".to_string())
                            }
                            seen_kwargs = true;
                            self.expr(env, arg)
                        }
                        ExprData::UnaryExpr {
                            op: Token::Star, ..
                        } => {
                            // *args
                            if seen_kwargs {
                                self.errorf(pos, "*args may not follow **kwargs".to_string())
                            } else if seen_varargs {
                                self.errorf(pos, "multiple *args not allowed".to_string())
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
                                self.errorf(
                                    pos,
                                    "keyword argument may not follow **kwargs".to_string(),
                                )
                            } else if seen_varargs {
                                self.errorf(
                                    pos,
                                    "keyword argument may not follow *args".to_string(),
                                )
                            }
                            if seen_name.contains(id.name) {
                                self.errorf(
                                    id.name_pos.clone(),
                                    format!("keyword argument {} is repeated", id.name),
                                )
                            } else {
                                seen_name.insert(id.name);
                            }
                            self.expr(env, y)
                        }
                        _ => {
                            // positional argument
                            p += 1;
                            if seen_varargs {
                                self.errorf(
                                    pos,
                                    "positional argument may not follow *args".to_string(),
                                )
                            } else if seen_kwargs {
                                self.errorf(
                                    pos,
                                    "positional argument may not follow **kwargs".to_string(),
                                )
                            } else if seen_name.len() > 0 {
                                self.errorf(
                                    pos,
                                    "positional argument may not follow named".to_string(),
                                )
                            }
                            self.expr(env, arg)
                        }
                    }

                    // Fail gracefully if compiler-imposed limit is exceeded.
                    if p >= 256 {
                        self.errorf(
                            arg.span.start.clone(),
                            format!("{} positional arguments in call, limit is 255", p),
                        );
                    }
                    if n >= 256 {
                        self.errorf(
                            arg.span.start.clone(),
                            format!("{} keyword arguments in call, limit is 255", n),
                        );
                    }
                }
            }
            ExprData::LambdaExpr {
                params,
                body,
                function,
                ..
            } => {
                let mut func = Function {
                    name: "lambda",
                    pos: e.span.start.clone(),
                    params: self.bump.alloc_slice_copy(params),
                    body: self.bump.alloc_slice_copy(&[&*self.bump.alloc(Stmt {
                        span: e.span.clone(),
                        data: StmtData::ReturnStmt {
                            result: Some(body),
                            return_pos: e.span.start.clone(),
                        },
                    })]),
                    has_kwargs: RefCell::new(false),
                    has_varargs: RefCell::new(false),
                    num_kwonly_params: RefCell::new(0),
                    locals: RefCell::new(vec![]),
                    free_vars: RefCell::new(vec![]),
                };
                *function.borrow_mut() = Some(self.function(env, func))
            }
            ExprData::ParenExpr { x, .. } => self.expr(env, x),

            _ => panic!("unexpected expr {:?}", e),
        }
    }

    fn function(&'a self, env: usize, mut function: Function<'a>) -> &'a Function<'a> {
        // Resolve defaults in enclosing environment.
        for param in function.params.into_iter() {
            match param.data {
                ExprData::BinaryExpr { y, .. } => self.expr(env, y),
                _ => {}
            }
        }

        // Enter function block.
        let index = self.blocks.borrow().len();
        let function = self.bump.alloc(function);
        let b = self.bump.alloc(Block::from_function(env, &*function));
        self.blocks.borrow()[env].children.borrow_mut().push(index);
        self.blocks.borrow_mut().push(b);
        let env = index;

        let mut seen_optional = false;
        let mut star: Option<&Expr> = None; // * or *args param
        let mut star_star: Option<&Ident> = None; // **kwargs ident
        let mut num_kwonly_params = 0;
        for param in b.function.unwrap().params {
            match &param.data {
                ExprData::Ident(p) => {
                    // e.g. x
                    if let Some(star_star) = star_star {
                        self.errorf(
                            p.name_pos.clone(),
                            format!("required parameter may not follow **{}", star_star.name),
                        );
                    } else if star.is_some() {
                        num_kwonly_params += 1;
                    } else if seen_optional {
                        self.errorf(
                            p.name_pos.clone(),
                            "required parameter may not follow optional".to_string(),
                        )
                    }
                    if self.bind(env, p) {
                        self.errorf(
                            p.name_pos.clone(),
                            format!("duplicate parameter: {}", p.name),
                        )
                    }
                }
                ExprData::BinaryExpr { x, op_pos, .. } => {
                    // e.g. y=dflt
                    if let Some(star_star) = star_star {
                        self.errorf(
                            op_pos.clone(),
                            format!("optional parameter may not follow **{}", star_star.name),
                        )
                    } else if star.is_some() {
                        num_kwonly_params += 1
                    }
                    if let ExprData::Ident(id) = x.data {
                        if self.bind(env, id) {
                            self.errorf(op_pos.clone(), format!("duplicate parameter: {}", id.name))
                        }
                    }
                    seen_optional = true
                }
                ExprData::UnaryExpr { op, op_pos, x, .. } => {
                    // * or *args or **kwargs
                    if *op == Token::Star {
                        if let Some(star_star) = star_star {
                            self.errorf(
                                op_pos.clone(),
                                format!("* parameter may not follow **{}", star_star.name),
                            )
                        } else if star.is_some() {
                            self.errorf(
                                op_pos.clone(),
                                "multiple * parameters not allowed".to_string(),
                            )
                        } else {
                            star = Some(param)
                        }
                    } else {
                        if star_star.is_some() {
                            self.errorf(
                                op_pos.clone(),
                                "multiple ** parameters not allowed".to_string(),
                            )
                        }
                        if let Some(ExprData::Ident(x)) = x.map(|x| &x.data) {
                            star_star = Some(x)
                        }
                    }
                }
                _ => {
                    panic!("unexpected {:?}", param)
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
                    self.errorf(
                        id.name_pos.clone(),
                        format!("duplicate parameter: {}", id.name),
                    )
                }
                *function.has_varargs.borrow_mut() = true
            } else if num_kwonly_params == 0 {
                self.errorf(
                    star.span.start.clone(),
                    "bare * must be followed by keyword-only parameters".to_string(),
                )
            }
        }
        if let Some(star_star) = star_star {
            if self.bind(env, star_star) {
                self.errorf(
                    star_star.name_pos.clone(),
                    format!("duplicate parameter: {}", star_star.name),
                )
            }
            *function.has_kwargs.borrow_mut() = true
        }

        *function.num_kwonly_params.borrow_mut() = num_kwonly_params;
        self.stmts(env, function.body);

        // Resolve all uses of this function's local vars,
        // and keep just the remaining uses of free/global vars.
        self.resolve_local_uses(b);

        // Leave function block.
        //self.pop()

        // References within the function body to globals are not
        // resolved until the end of the module.
        function
    }

    fn resolve_non_local_uses(&'a self, env: usize) {
        let b = &self.blocks.borrow()[env];
        // First resolve inner blocks.
        for child in b.children.borrow().iter() {
            self.resolve_non_local_uses(*child)
        }
        let uses = b.uses.borrow();
        for u in uses.iter().copied() {
            u.id.set_binding(&self.lookup_lexical(u, u.env))
        }
    }
} // impl

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{parse, FileUnit, Mode};

    #[test]
    fn basic_file_global() -> Result<()> {
        let bump = Bump::new();
        let src = "a = 3";
        let file_unit = parse(&bump, &"test", src, Mode::Plain)?;
        let f = resolve_file(file_unit, &bump, |s| false, |s| false)?;

        assert_eq!(f.module.globals.len(), 1);
        let b = &f.module.globals[0];
        assert_eq!(b.get_scope(), Scope::Global);
        assert_eq!(b.index, 0);
        if let Some(id) = b.first {
            assert_eq!(id.name, "a");
        } else {
            panic!("first is 0");
        }
        Ok(())
    }

    #[test]
    fn basic_file_global_error() -> Result<()> {
        let bump = Bump::new();
        let src = "a = 3\na = 4";
        let file_unit = parse(&bump, &"test", src, Mode::Plain)?;
        let f = resolve_file(file_unit, &bump, |s| false, |s| false);
        if let Err(e) = f {
            Ok(())
        } else {
            Err(anyhow!(
                "expected error due to global reassign {:?}.",
                f.unwrap().file_unit
            ))
        }
    }

    #[test]
    fn basic_file_local() -> Result<()> {
        let bump = Bump::new();
        let src = "def f(b):\n  a = b\na = 2";
        let file_unit = parse(&bump, &"test", src, Mode::Plain)?;
        let f = resolve_file(file_unit, &bump, |s| false, |s| false)?;

        assert_eq!(f.module.globals.len(), 2);
        let b = &f.module.globals[0];
        assert_eq!(b.get_scope(), Scope::Global);
        assert_eq!(b.index, 0);
        if let Some(id) = b.first {
            assert_eq!(id.name, "f");
        } else {
            panic!("first is None");
        }
        let b = &f.module.globals[1];
        assert_eq!(b.get_scope(), Scope::Global);
        assert_eq!(b.index, 1);
        if let Some(id) = b.first {
            assert_eq!(id.name, "a");
        } else {
            panic!("first is None");
        }
        Ok(())
    }

    #[test]
    fn load_comprehension_local() -> Result<()> {
        let bump = Bump::new();
        let src = "load('foo.sl', 'bar', baz='bak')\n[x for x in baz if bar]";
        let file_unit = parse(&bump, &"test", src, Mode::Plain)?;
        let f = resolve_file(file_unit, &bump, |s| false, |s| false)?;

        assert_eq!(f.module.locals.len(), 3);
        let b = &f.module.locals[0];
        assert_eq!(b.get_scope(), Scope::Local);
        assert_eq!(b.index, 0);
        if let Some(id) = b.first {
            assert_eq!(id.name, "bar");
        } else {
            panic!("first is None");
        }
        let b = &f.module.locals[1];
        assert_eq!(b.get_scope(), Scope::Local);
        assert_eq!(b.index, 1);
        if let Some(id) = b.first {
            assert_eq!(id.name, "baz");
        } else {
            panic!("first is None");
        }
        let b = &f.module.locals[2];
        assert_eq!(b.get_scope(), Scope::Local);
        assert_eq!(b.index, 2);
        if let Some(id) = b.first {
            assert_eq!(id.name, "x");
        } else {
            panic!("first is None");
        }
        Ok(())
    }
}
