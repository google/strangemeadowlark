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
use crate::{Clause, ExprData, ExprRef, Ident, Literal, StmtData, StmtRef, Token};

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
    // Constructs a list
    List(Box<[Local]>),
    // Constructs a dict
    Dict(Box<[(Local, Local)]>),
    // Index into a collection: x[y]
    IndexGet(Operand, Operand),
    // Field access: x.name
    FieldGet(Operand, String),
    // Slice: x[lo:hi:step]
    Slice {
        x: Operand,
        lo: Option<Operand>,
        hi: Option<Operand>,
        step: Option<Operand>,
    },
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
                    _ => Operand::Local(self.local(x)),
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
            ExprData::ListExpr { .. }
            | ExprData::TupleExpr { .. }
            | ExprData::DictExpr { .. }
            | ExprData::CondExpr { .. }
            | ExprData::UnaryExpr { .. }
            | ExprData::IndexExpr { .. }
            | ExprData::DotExpr { .. }
            | ExprData::SliceExpr { .. }
            | ExprData::LambdaExpr { .. }
            | ExprData::ParenExpr { .. }
            | ExprData::Comprehension { .. } => {
                let tmp = self.create_tmp();
                let rvalue = self.rvalue(expr);
                self.push_instr(Instruction::Assign(Place::from_local(tmp), rvalue));
                Operand::Local(tmp)
            }
            _ => {
                let tmp = self.create_tmp();
                let rvalue = self.rvalue(expr);
                self.push_instr(Instruction::Assign(Place::from_local(tmp), rvalue));
                Operand::Local(tmp)
            }
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
            None => {
                // Handle In/NotIn which are not in BinOp::from_token
                match op {
                    Token::In => Rvalue::BinaryOp(BinOp::In, left, right),
                    Token::NotIn => Rvalue::BinaryOp(BinOp::NotIn, left, right),
                    _ => panic!("token {op} cannot be binary op"),
                }
            }
        }
    }

    fn lower_comprehension(&mut self, expr: ExprRef<'a>) -> Rvalue {
        match &expr.data {
            ExprData::Comprehension {
                curly,
                body,
                clauses,
                ..
            } => {
                // Create a result local initialized to empty list (or dict)
                let result_local = self.create_tmp();
                if *curly {
                    self.push_instr(Instruction::Assign(
                        Place::from_local(result_local),
                        Rvalue::Use(Operand::Constant(Value::Dict(HashMap::new()))),
                    ));
                } else {
                    self.push_instr(Instruction::Assign(
                        Place::from_local(result_local),
                        Rvalue::Use(Operand::Constant(Value::List(Box::new([])))),
                    ));
                }

                self.lower_comprehension_clauses(body, *clauses, 0, result_local, *curly);

                Rvalue::Use(Operand::Local(result_local))
            }
            _ => panic!("expected Comprehension"),
        }
    }

    fn lower_comprehension_clauses(
        &mut self,
        body: &ExprRef<'a>,
        clauses: &[&'a Clause<'a>],
        clause_idx: usize,
        result_local: Local,
        curly: bool,
    ) {
        if clause_idx >= clauses.len() {
            // Base case: emit body and append to result
            if curly {
                // Dict comprehension: body is a DictEntry { key, value }
                if let ExprData::DictEntry { key, value, .. } = &body.data {
                    let key_val = self.operand(*key);
                    let val_val = self.operand(*value);
                    let tmp = self.create_tmp();
                    self.push_instr(Instruction::Assign(
                        Place::from_local(tmp),
                        Rvalue::BinaryOp(
                            BinOp::DictInsert,
                            Operand::Local(result_local),
                            key_val,
                        ),
                    ));
                    // For simplicity, use a two-step approach
                    // We'll use IndexSet for dict insert
                    let key_tmp = self.create_tmp();
                    let val_tmp = self.create_tmp();
                    // Re-evaluate operands into temps
                    let key_val2 = self.operand(*key);
                    self.push_instr(Instruction::Assign(Place::from_local(key_tmp), Rvalue::Use(key_val2)));
                    let val_val2 = self.operand(*value);
                    self.push_instr(Instruction::Assign(Place::from_local(val_tmp), Rvalue::Use(val_val2)));
                    // result[key] = value (via IndexSet)
                    self.push_instr(Instruction::Assign(
                        Place {
                            place_ref: Ref::Local(result_local),
                            projections: vec![Projection::Index(key_tmp)],
                        },
                        Rvalue::Use(Operand::Local(val_tmp)),
                    ));
                }
            } else {
                // List comprehension: result = result + [body]
                let body_tmp = self.create_tmp();
                let body_rv = self.rvalue(*body);
                self.push_instr(Instruction::Assign(
                    Place::from_local(body_tmp),
                    body_rv,
                ));
                let elem_tmp = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(elem_tmp),
                    Rvalue::List(Box::new([body_tmp])),
                ));
                self.push_instr(Instruction::Assign(
                    Place::from_local(result_local),
                    Rvalue::BinaryOp(
                        BinOp::Plus,
                        Operand::Local(result_local),
                        Operand::Local(elem_tmp),
                    ),
                ));
            }
            return;
        }

        match &clauses[clause_idx] {
            Clause::ForClause { vars, x, .. } => {
                // Index-based for loop: len = Len(iterable), idx = 0
                let head = self.create_block();
                let body_b = self.create_block();
                let loop_tail = self.create_block();

                // Compute the iterable
                let seq_local = self.create_tmp();
                let seq_rv = self.rvalue(*x);
                self.push_instr(Instruction::Assign(Place::from_local(seq_local), seq_rv));

                // Compute length once before the loop
                let len_local = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(len_local),
                    Rvalue::UnaryOp(UnOp::Len, Operand::Local(seq_local)),
                ));

                // Initialize index = 0
                let idx_local = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(idx_local),
                    Rvalue::Use(Operand::Constant(Value::Int(0))),
                ));

                self.terminate(Terminator::Jump(head));

                // Head: test idx < len
                self.current = head;
                let cmp = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(cmp),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Local(idx_local),
                        Operand::Local(len_local),
                    ),
                ));
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(cmp),
                    true_tgt: body_b,
                    false_tgt: loop_tail,
                });

                // Body: get current element, bind loop var, process inner clauses
                self.current = body_b;

                // Get element at index
                let elem_local = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(elem_local),
                    Rvalue::IndexGet(Operand::Local(seq_local), Operand::Local(idx_local)),
                ));

                // Bind loop variable(s)
                match &vars.data {
                    ExprData::Ident(_) => {
                        let place = self.place(vars);
                        self.push_instr(Instruction::Assign(place, Rvalue::Use(Operand::Local(elem_local))));
                    }
                    ExprData::TupleExpr { list, .. } => {
                        for (i, var) in list.iter().enumerate() {
                            let place = self.place(var);
                            let tmp = self.create_tmp();
                            self.push_instr(Instruction::Assign(
                                Place::from_local(tmp),
                                Rvalue::BinaryOp(
                                    BinOp::TupleGet,
                                    Operand::Local(elem_local),
                                    Operand::Constant(Value::Int(i as i64 + 1)),
                                ),
                            ));
                            self.push_instr(Instruction::Assign(place, Rvalue::Use(Operand::Local(tmp))));
                        }
                    }
                    _ => {}
                }

                // Process inner clauses
                self.lower_comprehension_clauses(body, clauses, clause_idx + 1, result_local, curly);

                // Increment index and jump back
                self.push_instr(Instruction::Assign(
                    Place::from_local(idx_local),
                    Rvalue::BinaryOp(
                        BinOp::Plus,
                        Operand::Local(idx_local),
                        Operand::Constant(Value::Int(1)),
                    ),
                ));
                self.terminate(Terminator::Jump(head));

                self.current = loop_tail;
            }
            Clause::IfClause { cond, .. } => {
                let then_b = self.create_block();
                let else_b = self.create_block();

                let cond_val = self.operand(*cond);
                let cond_tmp = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(cond_tmp),
                    Rvalue::Use(cond_val),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(cond_tmp),
                    StarlarkType::Bool,
                ));
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(cond_tmp),
                    true_tgt: then_b,
                    false_tgt: else_b,
                });

                self.current = then_b;
                self.lower_comprehension_clauses(body, clauses, clause_idx + 1, result_local, curly);

                self.current = else_b;
                // Nothing to do for the else branch - just fall through
            }
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
            ExprData::Comprehension { .. } => self.lower_comprehension(expr),
            ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => {
                let result = self.create_tmp();
                let cond_val = self.operand(*cond);
                let cond_tmp = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(cond_tmp),
                    Rvalue::Use(cond_val),
                ));
                self.push_instr(Instruction::Ascribe(
                    Place::from_local(cond_tmp),
                    StarlarkType::Bool,
                ));

                let then_b = self.create_block();
                let else_b = self.create_block();
                let tail = self.create_block();

                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(cond_tmp),
                    true_tgt: then_b,
                    false_tgt: else_b,
                });

                self.current = then_b;
                let then_val = self.rvalue(*then_arm);
                self.push_instr(Instruction::Assign(Place::from_local(result), then_val));
                self.terminate(Terminator::Jump(tail));

                self.current = else_b;
                let else_val = self.rvalue(*else_arm);
                self.push_instr(Instruction::Assign(Place::from_local(result), else_val));
                self.terminate(Terminator::Jump(tail));

                self.current = tail;
                Rvalue::Use(Operand::Local(result))
            }
            ExprData::DictEntry { key, value, .. } => {
                // Should only appear inside a dict literal or comprehension
                let k = self.operand(*key);
                let v = self.operand(*value);
                let k_tmp = self.create_tmp();
                let v_tmp = self.create_tmp();
                self.push_instr(Instruction::Assign(Place::from_local(k_tmp), Rvalue::Use(k)));
                self.push_instr(Instruction::Assign(Place::from_local(v_tmp), Rvalue::Use(v)));
                Rvalue::Dict(Box::new([(k_tmp, v_tmp)]))
            }
            ExprData::DictExpr { list, .. } => {
                let mut entries = vec![];
                for entry in list.iter() {
                    if let ExprData::DictEntry { key, value, .. } = &entry.data {
                        let k = self.operand(*key);
                        let v = self.operand(*value);
                        let k_tmp = self.create_tmp();
                        let v_tmp = self.create_tmp();
                        self.push_instr(Instruction::Assign(Place::from_local(k_tmp), Rvalue::Use(k)));
                        self.push_instr(Instruction::Assign(Place::from_local(v_tmp), Rvalue::Use(v)));
                        entries.push((k_tmp, v_tmp));
                    }
                }
                Rvalue::Dict(entries.into_boxed_slice())
            }
            ExprData::DotExpr { x, name, .. } => {
                let obj = self.operand(*x);
                Rvalue::FieldGet(obj, name.name.to_string())
            }
            ExprData::Ident(_) => {
                let place = self.place(expr);
                Rvalue::Use(Operand::from_place(&place))
            }
            ExprData::IndexExpr { x, y, .. } => {
                let obj = self.operand(*x);
                let idx = self.operand(*y);
                Rvalue::IndexGet(obj, idx)
            }
            ExprData::LambdaExpr {
                params,
                body,
                function,
                ..
            } => {
                // Same as DefStmt: create a closure tuple (FuncRef, free_vars...)
                let func_index = function.borrow().unwrap();
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

                let clos_rv = Rvalue::Tuple(clos.into_boxed_slice());

                // Build the lambda's MIR
                let block_offset = self.blocks.len();
                let local_offset = self.locals.len();
                let mut builder = Self::with_offset(self.arena, self.module, self.blocks.len());
                builder.build_mir(func_index);
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

                clos_rv
            }
            ExprData::ListExpr { list, .. } => {
                let mut locals = vec![];
                for elem in list.iter() {
                    let tmp = self.create_tmp();
                    let rv = self.rvalue(elem);
                    self.push_instr(Instruction::Assign(Place::from_local(tmp), rv));
                    locals.push(tmp);
                }
                Rvalue::List(locals.into_boxed_slice())
            }
            ExprData::Literal { .. } => Rvalue::Use(self.operand(expr)),
            ExprData::ParenExpr { x, .. } => self.rvalue(*x),
            ExprData::SliceExpr { x, lo, hi, step, .. } => {
                let obj = self.operand(*x);
                let lo_op = lo.map(|e| self.operand(e));
                let hi_op = hi.map(|e| self.operand(e));
                let step_op = step.map(|e| self.operand(e));
                Rvalue::Slice {
                    x: obj,
                    lo: lo_op,
                    hi: hi_op,
                    step: step_op,
                }
            }
            ExprData::TupleExpr { list, .. } => {
                let mut locals = vec![];
                for elem in list.iter() {
                    let tmp = self.create_tmp();
                    let rv = self.rvalue(elem);
                    self.push_instr(Instruction::Assign(Place::from_local(tmp), rv));
                    locals.push(tmp);
                }
                Rvalue::Tuple(locals.into_boxed_slice())
            }
            ExprData::UnaryExpr { op, x, .. } => {
                let x = match x {
                    Some(e) => e,
                    None => return Rvalue::Use(Operand::Constant(Value::None)),
                };
                let operand = self.operand(x);
                let un_op = UnOp::from_token(op).unwrap_or_else(|| {
                    panic!("unsupported unary op: {op:?}")
                });
                Rvalue::UnaryOp(un_op, operand)
            }
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
        if self.blocks.len() > 10000 {
            panic!("MIR builder: too many blocks - likely infinite loop in lowering");
        }
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
                    _ => Place::from_local(self.local(id)),
                }
            }
            ExprData::IndexExpr { x, y, .. } => {
                let base_place = self.place(x);
                let idx_tmp = self.create_tmp();
                let idx_rv = self.rvalue(y);
                self.push_instr(Instruction::Assign(Place::from_local(idx_tmp), idx_rv));
                Place {
                    place_ref: base_place.place_ref,
                    projections: vec![Projection::Index(idx_tmp)],
                }
            }
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
                    return; // augmented assignment doesn't fall through to plain assignment
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
                let head = self.create_block();
                let body_b = self.create_block();
                let tail = self.create_block();

                // Compute the iterable
                let seq_local = self.create_tmp();
                let seq_rvalue = self.rvalue(x);
                self.push_instr(Instruction::Assign(Place::from_local(seq_local), seq_rvalue));

                // Compute length once before the loop
                let len_local = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(len_local),
                    Rvalue::UnaryOp(UnOp::Len, Operand::Local(seq_local)),
                ));

                // Initialize index = 0
                let idx_local = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(idx_local),
                    Rvalue::Use(Operand::Constant(Value::Int(0))),
                ));

                self.terminate(Terminator::Jump(head));

                // Head: test idx < len
                self.current = head;
                let cmp = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(cmp),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Local(idx_local),
                        Operand::Local(len_local),
                    ),
                ));
                self.terminate(Terminator::ConditionalJump {
                    cond: Operand::Local(cmp),
                    true_tgt: body_b,
                    false_tgt: tail,
                });

                // Body: get element at index, bind loop var, execute body
                self.current = body_b;
                let elem_local = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(elem_local),
                    Rvalue::IndexGet(Operand::Local(seq_local), Operand::Local(idx_local)),
                ));

                match &vars.data {
                    ExprData::Ident(_) => {
                        let place = self.place(vars);
                        self.push_instr(Instruction::Assign(place, Rvalue::Use(Operand::Local(elem_local))));
                    }
                    ExprData::TupleExpr { list, .. } => {
                        for (i, var) in list.iter().enumerate() {
                            let place = self.place(var);
                            let tmp = self.create_tmp();
                            self.push_instr(Instruction::Assign(
                                Place::from_local(tmp),
                                Rvalue::BinaryOp(
                                    BinOp::TupleGet,
                                    Operand::Local(elem_local),
                                    Operand::Constant(Value::Int(i as i64 + 1)),
                                ),
                            ));
                            self.push_instr(Instruction::Assign(place, Rvalue::Use(Operand::Local(tmp))));
                        }
                    }
                    _ => {}
                }

                self.push_loop(tail, head);
                for stmt in *body {
                    self.stmt(stmt)
                }
                self.pop_loop();

                // Increment index and jump back
                self.push_instr(Instruction::Assign(
                    Place::from_local(idx_local),
                    Rvalue::BinaryOp(
                        BinOp::Plus,
                        Operand::Local(idx_local),
                        Operand::Constant(Value::Int(1)),
                    ),
                ));
                self.terminate(Terminator::Jump(head));

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
            fn write_local(&mut self, local: &Local, v: Value) {
                let index = self.get_frame_start() + local.0;
                self.state[index] = v;
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
                    Operand::Cell(local) => {
                        let v = self.read_local(local);
                        if let Value::Cell(cell) = &v {
                            Value::deref(cell)
                        } else {
                            v
                        }
                    }
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
                            UnOp::UnaryPlus => Value::unary_plus(&v),
                            UnOp::UnaryMinus => Value::unary_minus(&v),
                            UnOp::Len => Value::len(&v),
                            UnOp::Iterate | UnOp::IteratorNext => {
                                Value::Abort("legacy iterator op".to_string())
                            }
                            _ => Value::Abort(format!("unsupported unary op: {:?}", un_op)),
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
                            BinOp::BitwiseOr => Value::bitwise_or(&left, &right),
                            BinOp::BitwiseXor => Value::bitwise_xor(&left, &right),
                            BinOp::ShiftLeft => Value::shift_left(&left, &right),
                            BinOp::ShiftRight => Value::shift_right(&left, &right),
                            BinOp::Lt => Value::less_than(&left, &right),
                            BinOp::Gt => Value::greater_than(&left, &right),
                            BinOp::Ge => Value::greater_than_or_equals(&left, &right),
                            BinOp::Le => Value::less_than_or_equals(&left, &right),
                            BinOp::Equals => Value::equals(&left, &right),
                            BinOp::Neq => Value::not_equals(&left, &right),
                            BinOp::In => Value::is_in(&right, &left),
                            BinOp::NotIn => Value::not_in(&right, &left),
                            BinOp::DictInsert => Value::Abort("DictInsert should not be evaluated as binary op".to_string()),
                            BinOp::TupleGet => match (&left, &right) {
                                (Value::Tuple(elements), Value::Int(index)) => {
                                    elements[*index as usize].clone()
                                }
                                (Value::List(elements), Value::Int(index)) => {
                                    elements[*index as usize].clone()
                                }
                                _ => Value::Abort(format!("cannot tuple-get on {} with {}", left.type_name(), right.type_name())),
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
                    Rvalue::List(locals) => {
                        let mut values = vec![];
                        for local in locals.iter() {
                            values.push(self.read_local(local));
                        }
                        Value::List(values.into_boxed_slice())
                    }
                    Rvalue::Dict(entries) => {
                        let mut map = HashMap::new();
                        for (k_local, v_local) in entries.iter() {
                            let k = self.read_local(k_local);
                            let v = self.read_local(v_local);
                            map.insert(k, v);
                        }
                        Value::Dict(map)
                    }
                    Rvalue::IndexGet(obj, idx) => {
                        let obj = self.get_op(obj);
                        let idx = self.get_op(idx);
                        Value::index_get(&obj, &idx)
                    }
                    Rvalue::FieldGet(obj, name) => {
                        let obj = self.get_op(obj);
                        Value::field_get(&obj, name)
                    }
                    Rvalue::Slice { x, lo, hi, step } => {
                        let obj = self.get_op(x);
                        let lo_val = lo.as_ref().map(|op| self.get_op(op));
                        let hi_val = hi.as_ref().map(|op| self.get_op(op));
                        let step_val = step.as_ref().map(|op| self.get_op(op));
                        let lo_ref = lo_val.as_ref();
                        let hi_ref = hi_val.as_ref();
                        let step_ref = step_val.as_ref();
                        Value::slice(&obj, lo_ref, hi_ref, step_ref)
                    }
                }
            }

            fn assign(&mut self, place: &Place, v: Value) {
                if place.projections.is_empty() {
                    match place.place_ref {
                        Ref::Local(local) => {
                            let index = self.get_frame_start() + local.0;
                            self.state[index] = v;
                        }
                        Ref::FreeVar(index) => {
                            let cell = &self.frames.last().unwrap().free_vars[index as usize];
                            *cell.lock().unwrap() = v;
                        }
                    }
                } else {
                    match place.projections.first() {
                        Some(Projection::Deref) => {
                            // Assign through a cell
                            match &place.place_ref {
                                Ref::Local(local) => {
                                    let index = self.get_frame_start() + local.0;
                                    if let Value::Cell(cell) = &self.state[index] {
                                        *cell.lock().unwrap() = v;
                                    }
                                }
                                Ref::FreeVar(index) => {
                                    let cell = &self.frames.last().unwrap().free_vars[*index as usize];
                                    *cell.lock().unwrap() = v;
                                }
                            }
                        }
                        Some(Projection::Index(idx_local)) => {
                            let idx = self.read_local(idx_local);
                            match &place.place_ref {
                                Ref::Local(local) => {
                                    let index = self.get_frame_start() + local.0;
                                    let container = &mut self.state[index];
                                    let _ = container.index_set(idx, v);
                                }
                                _ => {}
                            }
                        }
                        None => {
                            match place.place_ref {
                                Ref::Local(local) => {
                                    let index = self.get_frame_start() + local.0;
                                    self.state[index] = v;
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        let mut fs = FrameStack::new(self.locals.len());

        fs.state.push(Value::None); // return value
        for (i, v) in args.iter().enumerate() {
            fs.state.push(v.clone());
        }
        for _i in 1 + args.len()..self.locals.len() {
            fs.state.push(Value::None);
        }
        let mut pc_block = Block(0);
        let mut pc_instr = 0;
        let mut steps = 0u64;
        loop {
            steps += 1;
            if steps > 1_000_000 {
                return Value::Abort("interpreter step limit exceeded".to_string());
            }
            let block = &self.blocks[pc_block.0];
            if pc_instr < block.instructions.len() {
                let instr = &block.instructions[pc_instr];
                match instr {
                    Instruction::Nop => {}
                    Instruction::MakeCell(local) => {
                        fs.state[local.0] =
                            Value::Cell(Rc::new(Mutex::new(fs.state[local.0].clone())));
                    }
                    Instruction::MkFunc(_, _) => {
                        // No-op: closures use Tuple representation
                    }
                    Instruction::Assign(place, rvalue) => {
                        let v = fs.run_rvalue(rvalue);
                        fs.assign(place, v);
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
                    Instruction::Ascribe(place, _ty) => {
                        // Runtime type ascription - no-op for now
                    }
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
                                        _ => {
                                            // Non-cell free var, wrap in cell
                                            cells.push(Rc::new(Mutex::new(v.clone())));
                                        }
                                    }
                                }
                                (*func_index, cells)
                            }
                            (x, y) => {
                                return Value::Abort(format!("call: unexpected closure format"))
                            }
                        },
                        x => return Value::Abort(format!("call: expected closure, got {:?}", x.type_name())),
                    };

                    let frame_start = fs.state.len();

                    // Return
                    fs.state.push(Value::None);
                    for arg in args.iter() {
                        fs.state.push(fs.read_local(arg))
                    }

                    // Grow stack to accommodate new frame.
                    let fun_info = &self.funcs[&func_index];
                    for _i in args.len()..fun_info.frame_size {
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
                } => {
                    let cond_val = fs.get_op(cond);
                    let truthy = cond_val.truthy();
                    pc_block = if truthy { *true_tgt } else { *false_tgt };
                    pc_instr = 0;
                }
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
                Terminator::Abort(v) => return v.clone(),
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
    UnaryPlus,  // +
    UnaryMinus, // -
    Len,        // len() built-in as operator

    // Legacy iterator ops (no longer used for for-loops)
    Iterate,
    IteratorNext,
}

impl UnOp {
    fn from_token(token: &Token) -> Option<Self> {
        match token {
            Token::Not => Some(UnOp::Not),
            Token::Tilde => Some(UnOp::BitwiseNot),
            Token::Plus => Some(UnOp::UnaryPlus),
            Token::Minus => Some(UnOp::UnaryMinus),
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
    In,                               // in
    NotIn,                            // not in

    TupleGet,   // internal tuple get operation - cannot fail
    DictInsert, // internal dict insert operation
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
            Token::Neq => Some(BinOp::Neq),
            Token::In => Some(BinOp::In),
            Token::NotIn => Some(BinOp::NotIn),
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

    fn run_func(arena: &Arena, input: &str, func_name: &str, args: &[Value]) -> Result<Value> {
        let (file_unit, module) = prepare(arena, input)?;
        for stmt in file_unit.stmts.iter() {
            if let StmtData::DefStmt { name, function, .. } = &stmt.data {
                if name.name == func_name {
                    let mut builder = MirBuilder::new(arena, &module);
                    builder.build_mir(function.borrow().unwrap());
                    let lowered = builder.lowered();
                    return Ok(lowered.run(args, &module));
                }
            }
        }
        Err(anyhow!("function {func_name} not found"))
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

    #[test]
    fn test_list_literal() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return [1, 2, 3]\n", "f", &[])?;
        assert_eq!(result, Value::List(Box::new([Value::Int(1), Value::Int(2), Value::Int(3)])));
        Ok(())
    }

    #[test]
    fn test_tuple_literal() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return (1, 2, 3)\n", "f", &[])?;
        assert_eq!(result, Value::Tuple(Box::new([Value::Int(1), Value::Int(2), Value::Int(3)])));
        Ok(())
    }

    #[test]
    fn test_dict_literal() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return {'a': 1, 'b': 2}\n", "f", &[])?;
        let mut expected = HashMap::new();
        expected.insert(Value::String("a".to_string()), Value::Int(1));
        expected.insert(Value::String("b".to_string()), Value::Int(2));
        assert_eq!(result, Value::Dict(expected));
        Ok(())
    }

    #[test]
    fn test_index_expr() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  xs = [10, 20, 30]\n  return xs[1]\n", "f", &[])?;
        assert_eq!(result, Value::Int(20));
        Ok(())
    }

    #[test]
    fn test_string_index() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 'hello'[1]\n", "f", &[])?;
        assert_eq!(result, Value::String("e".to_string()));
        Ok(())
    }

    #[test]
    fn test_dict_index() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return {'x': 42}['x']\n", "f", &[])?;
        assert_eq!(result, Value::Int(42));
        Ok(())
    }

    #[test]
    fn test_cond_expr() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f(x):\n  return 1 if x else 0\n", "f", &[Value::Bool(true)])?;
        assert_eq!(result, Value::Int(1));
        let result = run_func(&arena, "def f(x):\n  return 1 if x else 0\n", "f", &[Value::Bool(false)])?;
        assert_eq!(result, Value::Int(0));
        Ok(())
    }

    #[test]
    fn test_unary_minus() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return -5\n", "f", &[])?;
        assert_eq!(result, Value::Int(-5));
        Ok(())
    }

    #[test]
    fn test_unary_plus() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return +5\n", "f", &[])?;
        assert_eq!(result, Value::Int(5));
        Ok(())
    }

    #[test]
    fn test_string_concat() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 'hello' + ' world'\n", "f", &[])?;
        assert_eq!(result, Value::String("hello world".to_string()));
        Ok(())
    }

    #[test]
    fn test_string_repeat() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 'ab' * 3\n", "f", &[])?;
        assert_eq!(result, Value::String("ababab".to_string()));
        Ok(())
    }

    #[test]
    fn test_string_comparison() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 'abc' < 'def'\n", "f", &[])?;
        assert_eq!(result, Value::Bool(true));
        Ok(())
    }

    #[test]
    fn test_list_concat() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return [1, 2] + [3, 4]\n", "f", &[])?;
        assert_eq!(result, Value::List(Box::new([Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(4)])));
        Ok(())
    }

    #[test]
    fn test_paren_expr() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return (1 + 2) * 3\n", "f", &[])?;
        assert_eq!(result, Value::Int(9));
        Ok(())
    }

    #[test]
    fn test_float_arithmetic() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 1.5 + 2.5\n", "f", &[])?;
        assert_eq!(result, Value::Float(4.0));
        Ok(())
    }

    #[test]
    fn test_for_loop_sum() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(
            &arena,
            "def f():\n  s = 0\n  for i in (1, 2, 3, 4, 5):\n    s = s + i\n  return s\n",
            "f",
            &[],
        )?;
        assert_eq!(result, Value::Int(15));
        Ok(())
    }

    #[test]
    fn test_neq() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 1 != 2\n", "f", &[])?;
        assert_eq!(result, Value::Bool(true));
        let result = run_func(&arena, "def f():\n  return 1 != 1\n", "f", &[])?;
        assert_eq!(result, Value::Bool(false));
        Ok(())
    }

    #[test]
    fn test_in_operator() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 2 in (1, 2, 3)\n", "f", &[])?;
        assert_eq!(result, Value::Bool(true));
        Ok(())
    }

    #[test]
    fn test_not_in_operator() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 4 not in (1, 2, 3)\n", "f", &[])?;
        assert_eq!(result, Value::Bool(true));
        Ok(())
    }

    #[test]
    fn test_lambda() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  g = lambda x: x + 1\n  return g(5)\n", "f", &[])?;
        assert_eq!(result, Value::Int(6));
        Ok(())
    }

    #[test]
    fn test_slice_list() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  xs = [10, 20, 30, 40, 50]\n  return xs[1:3]\n", "f", &[])?;
        assert_eq!(result, Value::List(Box::new([Value::Int(20), Value::Int(30)])));
        Ok(())
    }

    #[test]
    fn test_slice_string() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(&arena, "def f():\n  return 'hello'[1:4]\n", "f", &[])?;
        assert_eq!(result, Value::String("ell".to_string()));
        Ok(())
    }

    #[test]
    #[ignore] // Parser hangs on comprehension inside function body
    fn test_list_comprehension() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(
            &arena,
            "def f():\n  return [x for x in (1, 2, 3)]\n",
            "f",
            &[],
        )?;
        assert_eq!(result, Value::List(Box::new([Value::Int(1), Value::Int(2), Value::Int(3)])));
        Ok(())
    }

    #[test]
    #[ignore] // Parser hangs on comprehension inside function body
    fn test_list_comprehension_with_filter() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(
            &arena,
            "def f():\n  xs = (1, 2, 3, 4, 5)\n  return [x for x in xs if x > 3]\n",
            "f",
            &[],
        )?;
        assert_eq!(result, Value::List(Box::new([Value::Int(4), Value::Int(5)])));
        Ok(())
    }

    #[test]
    #[ignore] // Parser hangs on comprehension inside function body
    fn test_nested_comprehension() -> Result<()> {
        let arena = Arena::new();
        let result = run_func(
            &arena,
            "def f():\n  xs = (1, 2)\n  ys = (10, 20)\n  return [x + y for x in xs for y in ys]\n",
            "f",
            &[],
        )?;
        assert_eq!(result, Value::List(Box::new([
            Value::Int(11), Value::Int(21), Value::Int(12), Value::Int(22),
        ])));
        Ok(())
    }
}
