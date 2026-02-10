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

//! Translates to mid-level intermediate representation (inspired by rustc MIR).
//! To learn more about the Rust MIR, see <https://rust-lang.github.io/rfcs/1211-mir.html>

use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;
use std::sync::Mutex;

use crate::Arena;
use crate::binding::{BindingIndex, Module, Scope};
use crate::scan::Position;
use crate::value::{StarlarkType, Value};
use crate::{ExprData, ExprRef, Ident, Literal, StmtData, StmtRef, Token};

/// Lowered representation of a function body.
pub struct Lowered<'a> {
    locals: Vec<LocalDef<'a>>,
    blocks: Vec<BlockData>,
    funcs: HashMap<usize, FuncDescriptor>,
}

/// Index into Vec<BlockData>.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Block(usize);

impl Block {
    fn apply_offset(&self, block_offset: usize) -> Self {
        Block(self.0 + block_offset)
    }
}
/// Index into Vec<LocalDef>.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Local(usize);

impl Local {
    fn apply_offset(&self, local_offset: usize) -> Self {
        Local(self.0 + local_offset)
    }
}

const LOCAL_RETURN: Local = Local(0);

/// A block is a (possibly empty) list of instructions and a terminator
#[derive(PartialEq, Eq, Debug)]
pub struct BlockData {
    instructions: Vec<Instruction>,
    terminator: Terminator,

    // If this is set, is the start block of a function.
    function_info: Option<String>,
}

impl BlockData {
    fn new() -> Self {
        BlockData {
            instructions: vec![],
            terminator: Terminator::Return,
            function_info: None,
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum Instruction {
    Nop,
    MakeCell(Local),
    MkFunc(Local, Box<[Local]>),
    Assign(Place, Rvalue),
    Eval(Rvalue),
    Ascribe(Place, StarlarkType),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Terminator {
    Call {
        func: Local,
        args: Box<[Local]>,
        destination: Local,
        target: Block,
    },
    ConditionalJump {
        cond: Operand,
        true_tgt: Block,
        false_tgt: Block,
    },
    Jump(Block),
    Return,

    Abort(Value),
}

impl Terminator {
    fn apply_offset(&self, block_offset: usize) -> Self {
        match self {
            Terminator::Call {
                func,
                args,
                destination,
                target,
            } => Terminator::Call {
                func: *func,
                args: args.clone(),
                destination: *destination,
                target: target.apply_offset(block_offset),
            },

            Terminator::ConditionalJump {
                cond,
                true_tgt,
                false_tgt,
            } => Terminator::ConditionalJump {
                cond: cond.clone(),
                true_tgt: true_tgt.apply_offset(block_offset),
                false_tgt: false_tgt.apply_offset(block_offset),
            },

            Terminator::Jump(block) => Terminator::Jump(block.apply_offset(block_offset)),
            Terminator::Return => Terminator::Return,
            Terminator::Abort(value) => Terminator::Abort(value.clone()),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Place {
    place_ref: Ref,
    projections: Vec<Projection>,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum Ref {
    Local(Local),
    FreeVar(u8),
}

impl Place {
    // Local place: contains Value directly.
    fn from_local(local: Local) -> Self {
        Place {
            place_ref: Ref::Local(local),
            projections: vec![],
        }
    }

    // Free var: a free var that references a cell.
    fn from_free(index: u8) -> Self {
        Place {
            place_ref: Ref::FreeVar(index),
            projections: vec![],
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum Projection {
    Deref,
    Index(Local),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Rvalue {
    UnaryOp(UnOp, Operand),
    BinaryOp(BinOp, Operand, Operand),
    Use(Operand),
    // Constructs a tuple
    Tuple(Box<[Local]>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Operand {
    Local(Local),
    FreeVar(u8),
    Cell(Local),
    Constant(Value),
    Copy(Place),
}

impl Operand {
    fn from_place(place: &Place) -> Self {
        match &place.place_ref {
            Ref::Local(local) => Operand::Local(*local),
            Ref::FreeVar(index) => Operand::FreeVar(*index),
        }
    }
}

#[derive(PartialEq, Eq)]
struct LocalDef<'a> {
    name: Option<&'a Ident<'a>>,
}

impl Display for LocalDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.name {
            Some(Ident { name: id, .. }) => write!(f, "{id}"),
            None => write!(f, "<local>"),
        }
    }
}

impl std::fmt::Debug for LocalDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FuncDescriptor {
    start_block: usize,
    frame_size: usize,
}

impl FuncDescriptor {
    fn apply_offset(&self, block_offset: usize, local_offset: usize) -> Self {
        FuncDescriptor {
            start_block: self.start_block + block_offset,
            frame_size: self.frame_size,
        }
    }
}

pub struct MirBuilder<'a, 'module> {
    arena: &'a Arena,
    module: &'module Module<'a>,
    locals: Vec<LocalDef<'a>>,
    blocks: Vec<BlockData>,
    current: Block,
    loop_break: Vec<Block>,
    loop_continue: Vec<Block>,
    funcs: HashMap<usize, FuncDescriptor>,
    offset: usize,
}

impl<'a, 'module> MirBuilder<'a, 'module> {
    fn new(arena: &'a Arena, module: &'module Module<'a>) -> Self {
        Self::with_offset(arena, module, 0)
    }

    fn with_offset(arena: &'a Arena, module: &'module Module<'a>, offset: usize) -> Self {
        let b = BlockData::new();
        MirBuilder {
            arena,
            module,
            locals: vec![],
            blocks: vec![b],
            current: Block(0),
            loop_break: vec![],
            loop_continue: vec![],
            funcs: HashMap::new(),
            offset,
        }
    }

    fn push_loop(&mut self, break_b: Block, continue_b: Block) {
        self.loop_break.push(break_b);
        self.loop_continue.push(continue_b);
    }

    fn pop_loop(&mut self) {
        self.loop_break.pop();
        self.loop_continue.pop();
    }

    fn operand(&mut self, expr: ExprRef<'a>) -> Operand {
        match &expr.data {
            ExprData::Literal {
                token: Literal::String(string_lit),
                ..
            } => Operand::Constant(Value::String(string_lit.to_string())),
            ExprData::Literal {
                token: Literal::Int(int_lit),
                ..
            } => Operand::Constant(Value::Int(*int_lit)),
            ExprData::Literal {
                token: Literal::BigInt(bigint_lit),
                ..
            } => Operand::Constant(Value::BigInt(bigint_lit.clone())),
            ExprData::Literal {
                token: Literal::Float(float_lit),
                ..
            } => Operand::Constant(Value::Float(*float_lit)),
            ExprData::Literal {
                token: Literal::Bytes(bytes_lit),
                ..
            } => {
                let v = Vec::from(*bytes_lit);
                Operand::Constant(Value::Bytes(v.into_boxed_slice()))
            }
            ExprData::Ident(x) => {
                let bindx = x.binding.borrow().unwrap();
                let bind = self.module.binding(bindx);
                match bind.get_scope() {
                    Scope::Local => Operand::Local(self.local(x)),
                    Scope::Free => Operand::FreeVar(bind.index),
                    Scope::Cell => Operand::Cell(self.local(x)),
                    _ => todo!(),
                }
            }
            ExprData::BinaryExpr { x, y, op, .. } => {
                let res = self.create_tmp();
                let rv = self.rvalue(expr);
                self.push_instr(Instruction::Assign(Place::from_local(res), rv));
                Operand::Local(res)
            }

            ExprData::CallExpr { .. } => {
                let tmp = self.create_tmp();
                let rvalue = self.rvalue(expr);
                self.push_instr(Instruction::Assign(Place::from_local(tmp), rvalue));
                Operand::Local(tmp)
            }
            _ => todo!("{:?}", expr.data),
        }
    }

    fn rvalue_binary(&mut self, op: &Token, left: ExprRef<'a>, right: ExprRef<'a>) -> Rvalue {
        let left = self.operand(left);
        let right = self.operand(right);
        match BinOp::from_token(op) {
            Some(BinOp::Div) => {
                let tmp_right = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(tmp_right),
                    Rvalue::Use(right),
                ));
                let non_zero = self.create_tmp();
                let abort = self.create_block();
                let tail = self.create_block();

                self.push_instr(Instruction::Assign(
                    Place::from_local(non_zero),
                    Rvalue::Use(Operand::Local(tmp_right)),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(non_zero),
                    StarlarkType::Bool,
                ));
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(non_zero),
                    true_tgt: tail,
                    false_tgt: abort,
                });

                self.current = abort;
                self.terminate(Terminator::Abort(Value::String(
                    "float-division by zero".to_string(),
                )));

                self.current = tail;
                Rvalue::BinaryOp(BinOp::Div, left, Operand::Local(tmp_right))
            }
            Some(op) => Rvalue::BinaryOp(op, left, right),
            _ => panic!("token {op} cannot be binary op"),
        }
    }

    fn rvalue(&mut self, expr: ExprRef<'a>) -> Rvalue {
        match &expr.data {
            ExprData::BinaryExpr {
                x,
                op: Token::And,
                y,
                ..
            } => {
                // shortcut evaluation
                let tmp_res = self.create_tmp();
                let x = self.operand(x);
                self.push_instr(Instruction::Assign(
                    Place::from_local(tmp_res),
                    Rvalue::Use(x),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(tmp_res),
                    StarlarkType::Bool,
                ));

                let is_true = self.create_block();
                let tail = self.create_block();
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(tmp_res),
                    true_tgt: is_true,
                    false_tgt: tail,
                });

                self.current = is_true;
                let y = self.operand(y);
                self.push_instr(Instruction::Assign(
                    Place::from_local(tmp_res),
                    Rvalue::Use(y),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(tmp_res),
                    StarlarkType::Bool,
                ));
                self.terminate(Terminator::Jump(tail));

                self.current = tail;
                Rvalue::Use(Operand::Local(tmp_res))
            }
            ExprData::BinaryExpr {
                x,
                op: Token::Or,
                y,
                ..
            } => {
                // shortcut evaluation
                let tmp_res = self.create_tmp();
                let x = self.operand(x);
                self.push_instr(Instruction::Assign(
                    Place::from_local(tmp_res),
                    Rvalue::Use(x),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(tmp_res),
                    StarlarkType::Bool,
                ));

                let is_false = self.create_block();
                let tail = self.create_block();
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(tmp_res),
                    true_tgt: tail,
                    false_tgt: is_false,
                });

                self.current = is_false;
                let y = self.operand(y);
                self.push_instr(Instruction::Assign(
                    Place::from_local(tmp_res),
                    Rvalue::Use(y),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(tmp_res),
                    StarlarkType::Bool,
                ));
                self.terminate(Terminator::Jump(tail));

                self.current = tail;
                Rvalue::Use(Operand::Local(tmp_res))
            }
            ExprData::BinaryExpr { x, op, y, .. } => self.rvalue_binary(op, x, y),
            ExprData::CallExpr {
                func,
                lparen,
                args,
                rparen,
            } => {
                let res = self.create_tmp();
                let tmp = self.create_tmp();
                let func_rvalue = self.rvalue(func);
                self.push_instr(Instruction::Assign(Place::from_local(tmp), func_rvalue));

                let mut arglocals = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    let argtmp = self.create_tmp();
                    arglocals.push(argtmp);
                    let arg_rvalue = self.rvalue(arg);
                    self.push_instr(Instruction::Assign(Place::from_local(argtmp), arg_rvalue));
                }
                let tail = self.create_block();
                self.terminate(Terminator::Call {
                    func: tmp,
                    args: arglocals.into_boxed_slice(),
                    destination: res,
                    target: tail,
                });
                self.current = tail;
                Rvalue::Use(Operand::Local(res))
            }
            ExprData::Comprehension {
                curly,
                lbrack_pos,
                body,
                clauses,
                rbrack_pos,
            } => todo!(),
            ExprData::CondExpr {
                if_pos,
                cond,
                then_arm,
                else_pos,
                else_arm,
            } => todo!(),
            ExprData::DictEntry { key, colon, value } => todo!(),
            ExprData::DictExpr {
                lbrace,
                list,
                rbrace,
            } => todo!(),
            ExprData::DotExpr {
                x,
                dot,
                name_pos,
                name,
            } => todo!(),
            ExprData::Ident(_) => {
                let place = self.place(expr);
                Rvalue::Use(Operand::from_place(&place))
            }
            ExprData::IndexExpr {
                x,
                lbrack,
                y,
                rbrack,
            } => todo!(),
            ExprData::LambdaExpr {
                lambda_pos,
                params,
                body,
                function,
            } => todo!(),
            ExprData::ListExpr {
                lbrack,
                list,
                rbrack,
            } => todo!(),
            ExprData::Literal { .. } => Rvalue::Use(self.operand(expr)),
            ExprData::ParenExpr { lparen, x, rparen } => todo!(),
            ExprData::SliceExpr {
                x,
                lbrack,
                lo,
                hi,
                step,
                rbrack,
            } => todo!(),
            ExprData::TupleExpr {
                lparen,
                list,
                rparen,
            } => todo!(),
            ExprData::UnaryExpr { op_pos, op, x } => todo!(),
        }
    }

    fn create_tmp(&mut self) -> Local {
        let n = self.locals.len();

        // for debugging only
        let name = self.arena.alloc_str(format!("_{n}").as_str());
        self.locals.push(LocalDef {
            name: Some(self.arena.alloc(Ident::new(Position::new(), name))),
        });
        Local(n as _)
    }

    fn local(&self, id: &'a Ident<'a>) -> Local {
        let b = id.binding.borrow().unwrap();
        let b = self.module.binding(b);
        Local(1 + (b.index as usize))
    }

    fn create_local(
        &mut self,
        id: &'a Ident<'a>,
        scope: Scope,
        cell: Option<BindingIndex>,
    ) -> Local {
        let n = self.locals.len();
        let local = LocalDef { name: Some(id) };
        self.locals.push(local);
        Local(n as _)
    }

    fn create_block(&mut self) -> Block {
        let n = self.blocks.len();
        self.blocks.push(BlockData::new());
        Block(n as _)
    }

    fn push_instr(&mut self, i: Instruction) {
        self.blocks[self.current.0].instructions.push(i);
    }

    fn terminate(&mut self, t: Terminator) {
        self.blocks[self.current.0].terminator = t;
    }

    fn build_mir(&mut self, func: usize) {
        let func = &self.module.functions[func];

        {
            // debug only
            let mut func_info = func.name.to_string();
            func_info.push_str(" locals:");
            for b in func.locals.borrow().iter() {
                let bind = self.module.binding(b);
                use std::fmt::Write;
                write!(
                    func_info,
                    " {}:{} ({})",
                    bind.index,
                    bind.first.unwrap().name,
                    bind.get_scope()
                )
                .unwrap();
            }
            func_info.push_str(" freevars:");
            for b in func.free_vars.borrow().iter() {
                let bind = self.module.binding(b);
                use std::fmt::Write;
                write!(
                    func_info,
                    " {}:{} ({})",
                    bind.index,
                    bind.first.unwrap().name,
                    bind.get_scope()
                )
                .unwrap();
            }
            self.blocks[0].function_info = Some(func_info);
        }

        // Set up LOCAL_RETURN.
        self.locals.push(LocalDef { name: None });

        for local in func.locals.borrow().iter() {
            let b = self.module.binding(local);
            if let Some(id) = b.first.as_ref() {
                let scope = b.get_scope();
                let local = self.create_local(
                    id,
                    scope,
                    if scope == Scope::Local {
                        None
                    } else {
                        Some(*local)
                    },
                );
                if scope == Scope::Cell {
                    self.push_instr(Instruction::MakeCell(local));
                }
            }
        }

        for stmt in func.body {
            self.stmt(stmt);
        }
    }

    /// Turns builder into Lowered
    fn lowered(self) -> Lowered<'a> {
        Lowered {
            locals: self.locals,
            blocks: self.blocks,
            funcs: self.funcs,
        }
    }

    fn lowered_with_offset(mut self, block_offset: usize) -> Lowered<'a> {
        for block in self.blocks.iter_mut() {
            block.terminator = block.terminator.apply_offset(block_offset);
        }
        self.lowered()
    }

    fn debug_string(&self) -> String {
        use std::fmt::Write;
        let mut s = String::new();
        for (i, b) in self.blocks.iter().enumerate() {
            write!(s, "Block {i} ;;").expect("could not write block");
            match &b.function_info {
                Some(info) => writeln!(s, " function {info}").unwrap(),
                _ => writeln!(s).unwrap(),
            };
            for instr in &b.instructions {
                writeln!(s, "  {instr:?}").expect("could not write instruction");
            }
            writeln!(s, "  {:?}", b.terminator).expect("could not write terminator");
        }
        s
    }

    fn place(&mut self, expr: ExprRef<'a>) -> Place {
        match expr.data {
            ExprData::Ident(id) => {
                let bindx = id.binding.borrow().unwrap();
                let bind = self.module.binding(bindx);
                match bind.get_scope() {
                    Scope::Local | Scope::Cell => Place::from_local(self.local(id)),
                    Scope::Free => Place::from_free(bind.index as _),
                    _ => todo!(),
                }
            }
            ExprData::IndexExpr {
                x,
                lbrack,
                y,
                rbrack,
            } => todo!(),
            _ => panic!("cannot handle case: {:?}", expr.data),
        }
    }

    fn stmt(&mut self, stmt: StmtRef<'a>) {
        match &stmt.data {
            StmtData::AssignStmt {
                op_pos,
                op: Token::Eq,
                lhs,
                rhs,
            } => {
                let place = self.place(lhs);
                let rvalue = self.rvalue(rhs);
                self.push_instr(Instruction::Assign(place, rvalue));
            }
            StmtData::AssignStmt {
                op_pos,
                op,
                lhs,
                rhs,
            } => {
                if let Some(token) = op.augmented() {
                    let op = BinOp::from_token(&token).unwrap();
                    let place = self.place(lhs);
                    let operand = self.rvalue(rhs);
                    let tmp = self.create_tmp();
                    self.push_instr(Instruction::Assign(Place::from_local(tmp), operand));
                    let res =
                        Rvalue::BinaryOp(op, Operand::from_place(&place), Operand::Local(tmp));
                    self.push_instr(Instruction::Assign(place, res));
                }
                let place = self.place(lhs);
                let rvalue = self.rvalue(rhs);
                self.push_instr(Instruction::Assign(place, rvalue));
            }
            StmtData::BranchStmt {
                token: Token::Break,
                ..
            } => {
                self.terminate(Terminator::Jump(*self.loop_break.last().unwrap()));
                self.current = self.create_block();
            }
            StmtData::BranchStmt {
                token: Token::Continue,
                ..
            } => {
                self.terminate(Terminator::Jump(*self.loop_continue.last().unwrap()));
                self.current = self.create_block();
            }
            StmtData::BranchStmt {
                token: Token::Pass, ..
            } => {
                self.push_instr(Instruction::Nop);
            }

            StmtData::DefStmt {
                name,
                function: f,
                params,
                ..
            } => {
                // We build a closure (f, env) where
                // f   the index (code pointer) of the function
                // env a tuple with references to each free variable
                let func_index = f.borrow().unwrap();
                let func = &self.module.functions[func_index];

                let mut clos = vec![];
                let tmp = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(tmp),
                    Rvalue::Use(Operand::Constant(Value::FuncRef(func_index))),
                ));
                clos.push(tmp);
                for bindx in func.free_vars.borrow().iter() {
                    let bind = self.module.binding(bindx);
                    let tmp = self.create_tmp();
                    match bind.get_scope() {
                        Scope::Cell => {
                            let place = Place::from_local(self.local(bind.first.unwrap()));
                            self.push_instr(Instruction::Assign(
                                Place::from_local(tmp),
                                Rvalue::Use(Operand::Copy(place)),
                            ));
                        }
                        Scope::Free => {
                            let place = Place::from_free(bind.index);
                            self.push_instr(Instruction::Assign(
                                Place::from_local(tmp),
                                Rvalue::Use(Operand::Copy(place)),
                            ));
                        }
                        x => unreachable!("This cannot happen: {x:?}"),
                    };

                    clos.push(tmp)
                }

                let tmp = self.create_tmp();
                let clos = Rvalue::Tuple(clos.into_boxed_slice());

                let fn_local = self.local(name);
                self.push_instr(Instruction::Assign(Place::from_local(fn_local), clos));

                // Translate the function's blocks
                let block_offset = self.blocks.len();
                let local_offset = self.locals.len();
                let mut builder = Self::with_offset(self.arena, self.module, self.blocks.len());
                builder.build_mir(f.borrow().unwrap());
                self.funcs.insert(
                    func_index,
                    FuncDescriptor {
                        start_block: block_offset,
                        frame_size: builder.locals.len(),
                    },
                );
                let lowered = builder.lowered_with_offset(block_offset);
                self.locals.extend(lowered.locals);
                self.blocks.extend(lowered.blocks);

                for (index, descr) in lowered.funcs.iter() {
                    self.funcs
                        .insert(*index, descr.apply_offset(block_offset, local_offset));
                }
            }

            StmtData::ExprStmt { x } => {
                let rv = self.rvalue(x);
                self.push_instr(Instruction::Eval(rv));
            }

            StmtData::ForStmt { vars, x, body, .. } => {
                let head_next = self.create_block();
                //let head_test = self.create_block();
                let body_b = self.create_block();
                let tail = self.create_block();

                let seq = self.create_tmp();
                let seq_rvalue = self.rvalue(x);
                self.push_instr(Instruction::Assign(Place::from_local(seq), seq_rvalue));

                // Get iterator.
                let iter = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(iter),
                    Rvalue::UnaryOp(UnOp::Iterate, Operand::Local(seq)),
                ));
                self.terminate(Terminator::Jump(head_next));

                self.current = head_next;
                let next = self.create_tmp();

                self.push_instr(Instruction::Assign(
                    Place::from_local(next),
                    Rvalue::UnaryOp(UnOp::IteratorNext, Operand::Local(iter)),
                ));

                let test = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(test),
                    Rvalue::BinaryOp(
                        BinOp::TupleGet,
                        Operand::Local(next),
                        Operand::Constant(Value::Int(0)),
                    ),
                ));
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(test),
                    true_tgt: body_b,
                    false_tgt: tail,
                });

                self.current = body_b;
                match &vars.data {
                    x @ ExprData::Ident(_) => {
                        let place = self.place(vars);
                        self.push_instr(Instruction::Assign(
                            place,
                            Rvalue::BinaryOp(
                                BinOp::TupleGet,
                                Operand::Local(next),
                                Operand::Constant(Value::Int(1)),
                            ),
                        ));
                    }
                    ExprData::TupleExpr { list, .. } => {
                        let mut i = 1;
                        for var in list.iter() {
                            let place = self.place(var);
                            self.push_instr(Instruction::Assign(
                                place,
                                Rvalue::BinaryOp(
                                    BinOp::TupleGet,
                                    Operand::Local(next),
                                    Operand::Constant(Value::Int(i)),
                                ),
                            ));
                            i += 1;
                        }
                    }
                    _ => todo!("cannot happen"),
                }

                self.push_loop(tail, head_next);
                for stmt in *body {
                    self.stmt(stmt)
                }
                self.pop_loop();
                self.current = tail;
            }
            StmtData::WhileStmt { cond, body, .. } => {
                let head = self.create_block();
                let body_b = self.create_block();
                let tail = self.create_block();
                self.terminate(Terminator::Jump(head));

                self.current = head;
                let cond = self.operand(cond);
                self.terminate(Terminator::ConditionalJump {
                    cond,
                    true_tgt: body_b,
                    false_tgt: tail,
                });

                self.current = body_b;
                self.push_loop(tail, body_b);
                for stmt in *body {
                    self.stmt(stmt);
                }
                self.pop_loop();
                self.terminate(Terminator::Jump(head));

                self.current = tail;
            }
            StmtData::IfStmt {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                let cond = self.operand(cond);
                let then_b = self.create_block();
                let tail = self.create_block();

                if else_arm.is_empty() {
                    self.terminate(Terminator::ConditionalJump {
                        cond,
                        true_tgt: then_b,
                        false_tgt: tail,
                    });
                    self.current = then_b;
                    for stmt in *then_arm {
                        self.stmt(stmt);
                    }
                    self.terminate(Terminator::Jump(tail));
                } else {
                    let else_b = self.create_block();
                    self.terminate(Terminator::ConditionalJump {
                        cond,
                        true_tgt: then_b,
                        false_tgt: else_b,
                    });
                    self.current = then_b;
                    for stmt in *then_arm {
                        self.stmt(stmt);
                    }
                    self.terminate(Terminator::Jump(tail));
                    self.current = else_b;
                    for stmt in *else_arm {
                        self.stmt(stmt);
                    }
                    self.terminate(Terminator::Jump(tail));
                }
                self.current = tail;
            }
            StmtData::ReturnStmt { return_pos, result } => {
                let rvalue = if let Some(result) = result {
                    self.rvalue(result)
                } else {
                    Rvalue::Use(Operand::Constant(Value::None))
                };
                self.push_instr(Instruction::Assign(Place::from_local(LOCAL_RETURN), rvalue));
                self.terminate(Terminator::Return);
            }
            StmtData::BranchStmt { .. } => {
                todo!("cannot happen") // we covered all branch stmt tokens above
            }
            StmtData::LoadStmt { .. } => {
                todo!("This cannot happen") // load must be at top-level
            }
        }
    }

    fn stmts(&mut self, stmts: &'a [StmtRef<'a>]) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }
}

struct Activation {
    free_vars: Vec<Rc<Mutex<Value>>>,
    start_block: usize,
    frame_start: usize,
    cont_target: Block,
    cont_destination: Local,
}

impl<'a> Lowered<'a> {
    /// Evaluating just one function. Useful for testing.
    fn run(&self, args: &[Value], module: &Module<'a>) -> Value {
        struct FrameStack {
            state: Vec<Value>, //Vec<Slot>,
            frames: Vec<Activation>,
        }
        impl FrameStack {
            fn new(size: usize) -> Self {
                Self {
                    state: Vec::with_capacity(size),
                    frames: vec![],
                }
            }
            fn cell_local(&self, local: &Local) -> Value {
                let index = self.get_frame_start() + local.0;
                self.state[index].clone()
            }
            fn read_local(&self, local: &Local) -> Value {
                let index = self.get_frame_start() + local.0;
                self.state[index].clone()
            }
            fn cell_freevar(&self, index: u8) -> Value {
                Value::Cell(Rc::clone(
                    &self.frames.last().unwrap().free_vars[index as usize],
                ))
            }
            fn read_freevar(&self, index: u8) -> Value {
                let cell: &Rc<Mutex<Value>> =
                    &self.frames.last().unwrap().free_vars[index as usize];
                cell.lock().unwrap().clone()
            }
            fn read(&self, place: &Place) -> Value {
                match &place.place_ref {
                    Ref::Local(local) => self.read_local(local),
                    Ref::FreeVar(index) => self.read_freevar(*index),
                }
            }

            fn frame(&self) -> &Activation {
                self.frames.last().unwrap()
            }
            fn get_frame_start(&self) -> usize {
                self.frames.last().map_or(0, |f| f.frame_start)
            }
            fn get_op(&self, op: &Operand) -> Value {
                match op {
                    Operand::Constant(c) => c.clone(),
                    Operand::FreeVar(index) => self.read_freevar(*index),
                    Operand::Cell(local) => todo!(),
                    Operand::Local(local) => self.read_local(local),
                    Operand::Copy(place) => match place.place_ref {
                        Ref::FreeVar(index) => {
                            if let Some(Projection::Deref) = place.projections.first() {
                                self.read_freevar(index)
                            } else {
                                self.cell_freevar(index)
                            }
                        }
                        Ref::Local(local) => self.cell_local(&local),
                    },
                }
            }
            fn run_rvalue(&self, rv: &Rvalue) -> Value {
                match rv {
                    Rvalue::UnaryOp(un_op, operand) => {
                        let mut v = self.get_op(operand);
                        if let Value::Cell(cell) = &v {
                            v = Value::deref(cell);
                        }
                        match un_op {
                            UnOp::Not => Value::not(&v),
                            UnOp::BitwiseNot => Value::bitwise_not(&v),
                            _ => todo!(),
                        }
                    }
                    Rvalue::BinaryOp(bin_op, left, right) => {
                        let mut left = self.get_op(left);
                        if let Value::Cell(cell) = &left {
                            left = Value::deref(cell);
                        }
                        let mut right = self.get_op(right);
                        if let Value::Cell(cell) = &right {
                            right = Value::deref(cell);
                        }

                        match bin_op {
                            BinOp::Plus => Value::plus(&left, &right),
                            BinOp::Minus => Value::minus(&left, &right),
                            BinOp::Times => Value::times(&left, &right),
                            BinOp::Div => Value::div(&left, &right),
                            BinOp::FloorDiv => Value::floor_div(&left, &right),
                            BinOp::RemFloorDivOrStringInterpolation => {
                                Value::floor_rem(&left, &right)
                            }
                            BinOp::BitwiseAnd => Value::bitwise_and(&left, &right),
                            BinOp::BitwiseOr => Value::bitwise_and(&left, &right),
                            BinOp::BitwiseXor => Value::bitwise_xor(&left, &right),
                            BinOp::ShiftLeft => Value::shift_left(&left, &right),
                            BinOp::ShiftRight => Value::shift_right(&left, &right),
                            BinOp::Lt => Value::less_than(&left, &right),
                            BinOp::Gt => Value::greater_than(&left, &right),
                            BinOp::Ge => Value::greater_than_or_equals(&left, &right),
                            BinOp::Le => Value::less_than_or_equals(&left, &right),
                            BinOp::Equals => Value::equals(&left, &right),
                            BinOp::Neq => Value::not_equals(&left, &right),
                            BinOp::TupleGet => match (left, right) {
                                (Value::Tuple(elements), Value::Int(index)) => {
                                    elements[index as usize].clone()
                                }
                                _ => todo!(),
                            },
                        }
                    }
                    Rvalue::Use(operand) => self.get_op(operand),
                    Rvalue::Tuple(locals) => {
                        let mut values = vec![];
                        for local in locals.iter() {
                            values.push(self.read_local(local));
                        }
                        Value::Tuple(values.into_boxed_slice())
                    }
                }
            }

            fn assign(&mut self, place: &Place, v: Value) {
                if !place.projections.is_empty() {
                    todo!();
                }
                match place.place_ref {
                    Ref::Local(local) => {
                        let index = self.get_frame_start() + local.0;
                        self.state[index] = v;
                    }
                    _ => todo!(),
                }
            }
        }

        let mut fs = FrameStack::new(self.locals.len());

        fs.state.push(Value::None); // return value
        for (i, v) in args.iter().enumerate() {
            fs.state.push(v.clone());
        }
        for i in 1 + args.len()..self.locals.len() {
            fs.state.push(Value::None);
        }
        let mut pc_block = Block(0);
        let mut pc_instr = 0;
        loop {
            let block = &self.blocks[pc_block.0];
            if pc_instr < block.instructions.len() {
                let instr = &block.instructions[pc_instr];
                match instr {
                    Instruction::Nop => {}
                    Instruction::MakeCell(local) => {
                        fs.state[local.0] =
                            Value::Cell(Rc::new(Mutex::new(fs.state[local.0].clone())));
                    }
                    Instruction::Assign(place, rvalue) => {
                        fs.assign(place, fs.run_rvalue(rvalue));
                    }
                    Instruction::Eval(rvalue) => {
                        fs.run_rvalue(rvalue);
                    }
                    Instruction::Ascribe(place, StarlarkType::Bool)
                        if place.projections.is_empty() =>
                    {
                        let v = &fs.read(place);
                        if let Value::Bool(_) = v {
                        } else {
                            fs.assign(place, v.bool())
                        }
                    }
                    _ => todo!(),
                }
                pc_instr += 1;
                continue;
            }
            match &block.terminator {
                Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                } => {
                    let (func_index, env) = match &fs.read_local(func) {
                        Value::Tuple(elems) => match (&elems[0], &elems[1..]) {
                            (Value::FuncRef(func_index), values) => {
                                let mut cells = vec![];
                                for v in values.iter() {
                                    match v {
                                        Value::Cell(cell) => cells.push(cell.clone()),
                                        _ => todo!(),
                                    }
                                }
                                (*func_index, cells)
                            }
                            (x, y) => todo!("{x:?}{y:?}"),
                        },
                        x => todo!("{x:?}"),
                    };

                    let frame_start = fs.state.len();

                    // Return
                    fs.state.push(Value::None);
                    for arg in args.iter() {
                        fs.state.push(fs.read_local(arg))
                    }

                    // Grow stack to accommodate new frame.
                    let fun_info = &self.funcs[&func_index];
                    for i in args.len()..fun_info.frame_size {
                        fs.state.push(Value::None);
                    }

                    let start_block = self.funcs[&func_index].start_block;
                    fs.frames.push(Activation {
                        free_vars: env.to_vec(),
                        start_block,
                        frame_start,
                        cont_target: *target,
                        cont_destination: *destination,
                    });

                    pc_block = Block(start_block);
                    pc_instr = 0;
                }
                Terminator::ConditionalJump {
                    cond,
                    true_tgt,
                    false_tgt,
                } => match fs.get_op(cond) {
                    Value::Bool(b) => {
                        pc_block = if b { *true_tgt } else { *false_tgt };
                        pc_instr = 0
                    }
                    _ => todo!(),
                },
                Terminator::Jump(tgt) => {
                    pc_block = *tgt;
                    pc_instr = 0;
                }
                Terminator::Return => {
                    if let Some(frame) = fs.frames.pop() {
                        let index = fs.get_frame_start() + frame.cont_destination.0;
                        fs.state[index] = fs.state[frame.frame_start].clone();
                        fs.state.shrink_to(frame.frame_start);
                        pc_block = frame.cont_target;
                        pc_instr = 0;
                    } else {
                        return fs.state[0].clone(); //read();
                    }
                }
                Terminator::Abort(Value::String(s)) => return Value::Abort(s.clone()),
                _ => todo!(),
            }
        }
    }
}
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum UnOp {
    Not,
    Bool,
    Str,
    Type,
    Hash,
    BitwiseNot, // ~

    // Using operators for built-ins
    Iterate,
    IteratorNext,
}

impl UnOp {
    fn from_token(token: &Token) -> Option<Self> {
        match token {
            Token::Not => Some(UnOp::Not),
            Token::Tilde => Some(UnOp::BitwiseNot),
            _ => None,
        }
    }
}

/// BinOp has binary operators that our virtual machine supports.
///
/// Compared to source syntax:
/// - assignment variants, "in", "notin", "and" and "or" are lowered.
/// - "div" can assume that divisor is non-zero.
/// - a "TupleGet" in order to support iteration
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum BinOp {
    Plus,                             // +
    Minus,                            // -
    Times,                            // *
    Div,                              // /
    FloorDiv,                         // //
    RemFloorDivOrStringInterpolation, // %
    BitwiseAnd,                       // &
    BitwiseOr,                        // |
    BitwiseXor,                       // ^
    ShiftLeft,                        // <<
    ShiftRight,                       // >>
    Lt,                               // <
    Gt,                               // >
    Ge,                               // >=
    Le,                               // <=
    Equals,                           // ==
    Neq,                              // !=

    TupleGet, // internal tuple get operation - cannot fail
}

impl BinOp {
    fn from_token(token: &Token) -> Option<Self> {
        match token {
            Token::Plus => Some(BinOp::Plus),
            Token::Minus => Some(BinOp::Minus),
            Token::Star => Some(BinOp::Times),
            Token::Slash => Some(BinOp::Div),
            Token::SlashSlash => Some(BinOp::FloorDiv),
            Token::Percent => Some(BinOp::RemFloorDivOrStringInterpolation),
            Token::Ampersand => Some(BinOp::BitwiseAnd),
            Token::Pipe => Some(BinOp::BitwiseOr),
            Token::Caret => Some(BinOp::BitwiseXor),
            Token::LtLt => Some(BinOp::ShiftLeft),
            Token::GtGt => Some(BinOp::ShiftRight),
            Token::Lt => Some(BinOp::Lt),
            Token::Gt => Some(BinOp::Gt),
            Token::Ge => Some(BinOp::Ge),
            Token::Le => Some(BinOp::Le),
            Token::EqEq => Some(BinOp::Equals),
            Token::Neq => todo!(),
            Token::StarStar => todo!(),

            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{FileUnit, StmtData, parse, resolve::FileUnitWithModule, resolve_file};

    use super::*;
    use anyhow::{Result, anyhow};

    fn prepare<'a>(arena: &'a Arena, input: &'a str) -> Result<(FileUnit<'a>, Module<'a>)> {
        let file_unit = parse(arena, input)?;
        let res =
            resolve_file(&file_unit, arena, |s| false, |s| false).map_err(|e| anyhow!("{e:?}"))?;
        let FileUnitWithModule { module, .. } = res;
        Ok((file_unit, module))
    }

    #[test]
    fn test_empty() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(&arena, "def foo():\n  return\n")?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());

                assert_eq!(builder.blocks.len(), 1);
                let bb = &builder.blocks[0];
                assert_eq!(bb.instructions.len(), 1);
                assert_eq!(bb.terminator, Terminator::Return);

                let lowered = builder.lowered();
                assert_eq!(lowered.run(&[], &module), Value::None);
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_basic() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(&arena, "def foo(x):\n  return x + 2\n")?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&arena, &module);

                builder.build_mir(f.borrow().unwrap());

                assert_eq!(builder.blocks.len(), 1);
                let bb = &builder.blocks[0];
                assert_eq!(bb.instructions.len(), 1);
                assert!(matches!(
                    bb.instructions[0],
                    Instruction::Assign(
                        Place {
                            place_ref: Ref::Local(LOCAL_RETURN),
                            ..
                        },
                        Rvalue::BinaryOp(
                            BinOp::Plus,
                            Operand::Local(Local(1)),
                            Operand::Constant(Value::Int(2))
                        )
                    )
                ));
                assert_eq!(bb.terminator, Terminator::Return);

                let lowered = builder.lowered();
                assert_eq!(lowered.run(&[Value::Int(5)], &module), Value::Int(7));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_body() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(
            &arena,
            "
def fib(n):
  if n == 0:
    return 1
  if n == 1:
    return 1
  x = 1
  y = 1
  i = 1
  while i < n:
    tmp = x
    x = y
    y = x + tmp
    i = i + 1
  return y
",
        )?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();
                assert_eq!(lowered.run(&[Value::Int(4)], &module), Value::Int(5));
                assert_eq!(lowered.run(&[Value::Int(5)], &module), Value::Int(8));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_nested_nofree() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(
            &arena,
            "
def foo(x):
  def bar(y):
    return y + 1
  return bar(x)
",
        )?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt {
                function: f,
                params,
                ..
            } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();
                assert_eq!(lowered.run(&[Value::Int(1)], &module), Value::Int(2));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_nested_simple() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(
            &arena,
            "
def foo(x):
  def bar():
    return x + 1
  return bar()
    ",
        )?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt {
                function: f,
                params,
                ..
            } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();

                assert_eq!(lowered.run(&[Value::Int(2)], &module), Value::Int(3));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_nested_cell() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(
            &arena,
            "
def foo(x):
  def bar(y):
    def baz():
      return x
    return y + baz()
  return bar(x)
    ",
        )?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt {
                function: f,
                params,
                ..
            } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();

                assert_eq!(lowered.run(&[Value::Int(2)], &module), Value::Int(4));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_and_sanity() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(&arena, "def fooand(x, y):\n  return x and y\n")?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();

                // Sanity
                assert_eq!(
                    lowered.run(&[Value::Bool(true), Value::Bool(true)], &module),
                    Value::Bool(true)
                );
                assert_eq!(
                    lowered.run(&[Value::Bool(false), Value::Bool(true)], &module),
                    Value::Bool(false)
                );
                assert_eq!(
                    lowered.run(&[Value::Bool(true), Value::Bool(false)], &module),
                    Value::Bool(false)
                );
                assert_eq!(
                    lowered.run(&[Value::Bool(false), Value::Bool(false)], &module),
                    Value::Bool(false)
                );
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_and_shortcut() -> Result<()> {
        let arena = Arena::new();
        let (file_unit, module) = prepare(&arena, "def fooshort(x):\n  return x and 1/0\n")?;
        assert_eq!(file_unit.stmts.len(), 1);
        match &file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&arena, &module);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();

                assert_eq!(
                    lowered.run(&[Value::Bool(false)], &module),
                    Value::Bool(false)
                );
                assert!(matches!(
                    lowered.run(&[Value::Bool(true)], &module),
                    Value::Abort(_)
                ));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }
}
