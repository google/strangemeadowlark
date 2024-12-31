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

use std::fmt::Display;

use crate::scan::Position;
use crate::value::{StarlarkType, Value};

use crate::binding::Function;
use crate::{ExprData, ExprRef, Ident, Literal, StmtRef, Token};

use bumpalo::Bump;

/// Lowered representation of a function body.
pub struct Lowered<'a> {
    locals: Vec<LocalDef<'a>>,
    blocks: Vec<BlockData>,
}

/// Index into Vec<BlockData>.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Block(usize);

/// Index into Vec<LocalDef>.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Local(usize);

const LOCAL_RETURN: Local = Local(0);

/// A block is a (possibly empty) list of instructions and a terminator
#[derive(PartialEq, Eq, Debug)]
pub struct BlockData {
    instructions: Vec<Instruction>,
    terminator: Terminator,
}

impl BlockData {
    fn new() -> Self {
        BlockData {
            instructions: vec![],
            terminator: Terminator::Return,
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum Instruction {
    Nop,
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
        target: Option<Block>,
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

#[derive(PartialEq, Eq, Debug)]
pub struct Place {
    local: Local,
    projections: Vec<Projecion>,
}

impl Place {
    fn from_local(local: Local) -> Self {
        Place {
            local,
            projections: vec![],
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum Projecion {
    Index(Local),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Rvalue {
    UnaryOp(UnOp, Operand),
    BinaryOp(BinOp, Operand, Operand),
    Use(Operand),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Operand {
    Local(Local),
    Constant(Value),
}

#[derive(PartialEq, Eq)]
struct LocalDef<'a> {
    name: Option<&'a Ident<'a>>,
}

impl<'a> Display for LocalDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.name {
            Some(Ident { name: id, .. }) => write!(f, "{}", id),
            None => write!(f, "<local>"),
        }
    }
}

impl<'a> std::fmt::Debug for LocalDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

pub struct MirBuilder<'a> {
    bump: &'a Bump,
    locals: Vec<LocalDef<'a>>,
    blocks: Vec<BlockData>,
    nested: Vec<Box<MirBuilder<'a>>>,
    current: Block,
    loop_break: Vec<Block>,
    loop_continue: Vec<Block>,
}

impl<'a> MirBuilder<'a> {
    fn new(bump: &'a Bump) -> Self {
        let b = BlockData::new();
        MirBuilder {
            bump,
            locals: vec![],
            blocks: vec![b],
            nested: vec![],
            current: Block(0),
            loop_break: vec![],
            loop_continue: vec![],
        }
    }

    fn new_nested(&mut self) -> &mut MirBuilder<'a> {
        self.nested.push(Box::new(Self::new(&self.bump)));
        self.nested.last_mut().unwrap()
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
            ExprData::Ident(x) => Operand::Local(self.local(x)),
            ExprData::BinaryExpr { x, y, op, .. } => {
                let res = self.create_tmp();
                let rv = self.rvalue(expr);
                self.push_instr(Instruction::Assign(Place::from_local(res), rv));
                Operand::Local(res)
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
            _ => panic!("token {} cannot be binary op", op),
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
            } => todo!(),
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
                Rvalue::Use(Operand::Local(place.local))
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
        let name = self.bump.alloc_str(format!("_{}", n).as_str());
        self.locals.push(LocalDef {
            name: Some(self.bump.alloc(Ident::new(Position::new(), name))),
        });
        Local(n as _)
    }

    fn local(&self, id: &'a Ident<'a>) -> Local {
        Local(1 + (id.binding.borrow().as_ref().unwrap().index as usize))
    }

    fn create_local(&mut self, id: &'a Ident<'a>) -> Local {
        let n = self.locals.len();
        self.locals.push(LocalDef { name: Some(id) });
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

    fn build_mir(&mut self, func: &'a Function<'a>) {
        // Set up LOCAL_RETURN.
        self.locals.push(LocalDef { name: None });

        for local in func.locals.borrow().iter() {
            self.create_local(local.first.unwrap());
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
        }
    }

    fn debug_string(&self) -> String {
        use std::fmt::Write;
        let mut s = String::new();
        for (i, b) in self.blocks.iter().enumerate() {
            writeln!(s, "Block {}", i).expect("could not write block");
            for instr in &b.instructions {
                writeln!(s, "  {:?}", instr).expect("could not write instruction");
            }
            writeln!(s, "  {:?}", b.terminator).expect("could not write terminator");
        }
        s
    }

    fn place(&mut self, expr: ExprRef<'a>) -> Place {
        match expr.data {
            ExprData::Ident(id) => {
                let b = id.binding().unwrap();
                let local = Local(1 + (b.index as usize));
                Place::from_local(local)
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
            crate::StmtData::AssignStmt {
                op_pos,
                op: Token::Eq,
                lhs,
                rhs,
            } => {
                let place = self.place(lhs);
                let rvalue = self.rvalue(rhs);
                self.push_instr(Instruction::Assign(place, rvalue));
            }
            crate::StmtData::AssignStmt {
                op_pos,
                op,
                lhs,
                rhs,
            } => {
                if let Some(token) = op.augmented() {
                    todo!();
                }
                let place = self.place(lhs);
                let rvalue = self.rvalue(rhs);
                self.push_instr(Instruction::Assign(place, rvalue));
            }
            crate::StmtData::BranchStmt {
                token: Token::Break,
                ..
            } => {
                self.terminate(Terminator::Jump(*self.loop_break.last().unwrap()));
                self.current = self.create_block();
            }
            crate::StmtData::BranchStmt {
                token: Token::Continue,
                ..
            } => {
                self.terminate(Terminator::Jump(*self.loop_continue.last().unwrap()));
                self.current = self.create_block();
            }
            crate::StmtData::BranchStmt {
                token: Token::Pass, ..
            } => {
                self.push_instr(Instruction::Nop);
            }

            crate::StmtData::DefStmt { function: f, .. } => {
                let builder = self.new_nested();
                builder.build_mir(f.borrow().unwrap());
            }

            crate::StmtData::ExprStmt { x } => {
                let rv = self.rvalue(x);
                self.push_instr(Instruction::Eval(rv));
            }

            crate::StmtData::ForStmt { vars, x, body, .. } => {
                let head_next = self.create_block();
                let head_test = self.create_block();
                let body_b = self.create_block();
                let tail = self.create_block();

                let iter = self.create_tmp();
                let iterate = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(iterate),
                    Rvalue::Use(Operand::Constant(Value::ITERATE)),
                ));
                self.terminate(Terminator::Call {
                    func: iterate,
                    args: Box::new([Local::from(iterate)]),
                    destination: Local::from(iter),
                    target: Some(head_next),
                });

                self.current = head_next;
                let next = self.create_tmp();
                let it_next_fn = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(it_next_fn),
                    Rvalue::Use(Operand::Constant(Value::ITERATOR_NEXT)),
                ));
                self.terminate(Terminator::Call {
                    func: it_next_fn,
                    args: Box::new([Local::from(iter)]),
                    destination: Local::from(next),
                    target: Some(head_test),
                });

                self.current = head_test;
                let test = self.create_tmp();
                self.push_instr(Instruction::Assign(
                    Place::from_local(next),
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
            crate::StmtData::WhileStmt { cond, body, .. } => {
                let head = self.create_block();
                let body_b = self.create_block();
                let tail = self.create_block();
                self.terminate(Terminator::Jump(head));

                self.current = head;
                let cond = self.operand(cond);
                println!("while stmt operand: {:?}", cond);
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
            crate::StmtData::IfStmt {
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
            crate::StmtData::ReturnStmt { return_pos, result } => {
                let rvalue = if let Some(result) = result {
                    self.rvalue(result)
                } else {
                    Rvalue::Use(Operand::Constant(Value::None))
                };
                self.push_instr(Instruction::Assign(Place::from_local(LOCAL_RETURN), rvalue));
                self.terminate(Terminator::Return);
            }
            crate::StmtData::BranchStmt { .. } => {
                todo!("cannot happen") // we covered all branch stmt tokens above
            }
            crate::StmtData::LoadStmt { .. } => {
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

impl<'a> Lowered<'a> {
    /// Evaluating just one function. Useful for testing.
    fn run(&self, args: &[Value]) -> Value {
        let mut state: Vec<Value> = Vec::with_capacity(self.locals.len());

        let get_op = |op: &Operand, state: &Vec<Value>| -> Value {
            match op {
                Operand::Constant(c) => c.clone(),
                Operand::Local(local) => state[(*local).0].clone(),
            }
        };
        let run_rvalue = |rv: &Rvalue, state: &Vec<Value>| -> Value {
            match rv {
                Rvalue::UnaryOp(un_op, operand) => {
                    let v = get_op(operand, &state);
                    match un_op {
                        UnOp::Not => Value::not(&v),
                        UnOp::BitwiseNot => Value::bitwise_not(&v),
                        _ => todo!(),
                    }
                }
                Rvalue::BinaryOp(bin_op, left, right) => {
                    let left = get_op(left, &state);
                    let right = get_op(right, &state);
                    match bin_op {
                        BinOp::Plus => Value::plus(&left, &right),
                        BinOp::Minus => Value::minus(&left, &right),
                        BinOp::Times => Value::times(&left, &right),
                        BinOp::Div => Value::div(&left, &right),
                        BinOp::FloorDiv => Value::floor_div(&left, &right),
                        BinOp::RemFloorDivOrStringInterpolation => Value::floor_rem(&left, &right),
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
                Rvalue::Use(operand) => get_op(operand, &state),
            }
        };
        let assign = |place: &Place, v, state: &mut Vec<Value>| {
            let local = place.local;
            if place.projections.is_empty() {
                state[local.0] = v;
            }
        };
        state.push(Value::None); // return value
        for v in args {
            state.push(v.clone());
        }
        for i in 1 + args.len()..self.locals.len() {
            state.push(Value::None);
        }
        let mut pc_block = Block(0);
        let mut pc_instr = 0;
        loop {
            let block = &self.blocks[pc_block.0];
            if pc_instr < block.instructions.len() {
                let instr = &block.instructions[pc_instr];
                match instr {
                    Instruction::Nop => {}
                    Instruction::Assign(place, rvalue) => {
                        assign(place, run_rvalue(rvalue, &state), &mut state);
                    }
                    Instruction::Eval(rvalue) => {
                        run_rvalue(rvalue, &state);
                    }
                    Instruction::Ascribe(place, StarlarkType::Bool)
                        if place.projections.is_empty() =>
                    {
                        let v = &state[place.local.0];
                        if let Value::Bool(_) = v {
                        } else {
                            assign(place, v.bool(), &mut state)
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
                } => todo!(),
                Terminator::ConditionalJump {
                    cond,
                    true_tgt,
                    false_tgt,
                } => match get_op(cond, &state) {
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
                Terminator::Return => return state[0].clone(),
                Terminator::Abort(Value::String(s)) => return Value::Abort(s.clone()),
                _ => todo!(),
            }
        }
    }
}
#[derive(PartialEq, Eq, Debug)]
pub enum UnOp {
    Not,
    Bool,
    Str,
    Type,
    Hash,
    BitwiseNot, // ~
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
///
/// TODO: set up type analysis and typed variants like PlusIntInt,
/// split RemFloorDiv and StringInterpolation.
#[derive(PartialEq, Eq, Debug)]
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
    use crate::{parse, resolve::FileUnitWithModule, resolve_file, Mode, StmtData};

    use super::*;
    use anyhow::{anyhow, Result};

    fn prepare<'a>(bump: &'a Bump, input: &'a str) -> Result<&'a FileUnitWithModule<'a>> {
        let file_unit = parse(&bump, &"test.starlark", input, Mode::Plain)?;
        resolve_file(file_unit, &bump, |s| false, |s| false)
    }

    #[test]
    fn test_empty() -> Result<()> {
        let bump = Bump::new();
        let module = prepare(&bump, "def foo():\n  return\n")?;
        assert_eq!(module.file_unit.stmts.len(), 1);
        match &module.file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&bump);
                builder.build_mir(f.borrow().unwrap());

                assert_eq!(builder.blocks.len(), 1);
                let bb = &builder.blocks[0];
                assert_eq!(bb.instructions.len(), 1);
                assert_eq!(bb.terminator, Terminator::Return);

                let lowered = builder.lowered();
                assert_eq!(lowered.run(&[]), Value::None);
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_basic() -> Result<()> {
        let bump = Bump::new();
        let module = prepare(&bump, "def foo(x):\n  return x + 2\n")?;
        assert_eq!(module.file_unit.stmts.len(), 1);
        match &module.file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&bump);

                builder.build_mir(f.borrow().unwrap());

                assert_eq!(builder.blocks.len(), 1);
                let bb = &builder.blocks[0];
                assert_eq!(bb.instructions.len(), 1);
                assert!(matches!(
                    bb.instructions[0],
                    Instruction::Assign(
                        Place {
                            local: LOCAL_RETURN,
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
                assert_eq!(lowered.run(&[Value::Int(5)]), Value::Int(7));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_body() -> Result<()> {
        let bump = Bump::new();
        let module = prepare(
            &bump,
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
        assert_eq!(module.file_unit.stmts.len(), 1);
        match &module.file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&bump);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();
                assert_eq!(lowered.run(&[Value::Int(4)]), Value::Int(5));
                assert_eq!(lowered.run(&[Value::Int(5)]), Value::Int(8));
                Ok(())
            }
            x => Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_and_sanity() -> Result<()> {
        let bump = Bump::new();
        let module = prepare(&bump, "def fooand(x, y):\n  return x and y\n")?;
        assert_eq!(module.file_unit.stmts.len(), 1);
        match &module.file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&bump);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();

                // Sanity
                assert_eq!(
                    lowered.run(&[Value::Bool(true), Value::Bool(true)]),
                    Value::Bool(true)
                );
                assert_eq!(
                    lowered.run(&[Value::Bool(false), Value::Bool(true)]),
                    Value::Bool(false)
                );
                assert_eq!(
                    lowered.run(&[Value::Bool(true), Value::Bool(false)]),
                    Value::Bool(false)
                );
                assert_eq!(
                    lowered.run(&[Value::Bool(false), Value::Bool(false)]),
                    Value::Bool(false)
                );
                Ok(())
            }
            x => return Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }

    #[test]
    fn test_and_shortcut() -> Result<()> {
        let bump = Bump::new();
        let module = prepare(&bump, "def fooshort(x):\n  return x and 1/0\n")?;
        assert_eq!(module.file_unit.stmts.len(), 1);
        match &module.file_unit.stmts[0].data {
            StmtData::DefStmt { function: f, .. } => {
                let mut builder = MirBuilder::new(&bump);
                builder.build_mir(f.borrow().unwrap());
                let lowered = builder.lowered();

                assert_eq!(lowered.run(&[Value::Bool(false)]), Value::Bool(false));
                assert!(matches!(lowered.run(&[Value::Bool(true)]), Value::Abort(_)));
                Ok(())
            }
            x => return Err(anyhow!("expected defstmt got {:?}", x)),
        }
    }
}
