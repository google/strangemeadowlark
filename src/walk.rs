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

use crate::syntax::{Clause, Expr, ExprData, FileUnit, Stmt, StmtData};

// NodeIterator is a struct representing a path within a
// a (borrowed, read-only) AST node.
//
// For example: A --(i)--> B --(j)--> C with nodes A, B, C where
// B is the i-th child of A and C is the j-th child of B is
// represented as (A,i), (B,j)
// Invariant: the path is always valid. For the root node,
// we use a special sentinel value Init().
#[derive(Debug)]
pub struct NodeIterator<'a> {
    path: Vec<(Node<'a>, usize)>,
    cur: Node<'a>,
}

#[derive(Clone, Copy, Debug)]
pub enum Node<'a> {
    Init(),
    FileUnitRef(&'a FileUnit<'a>),
    StmtRef(&'a Stmt<'a>),
    ExprRef(&'a Expr<'a>),
    ClauseRef(&'a Clause<'a>),
}

impl<'a> NodeIterator<'a> {
    pub fn new(root: Node<'a>) -> Self {
        NodeIterator {
            path: vec![(Node::Init(), 0)],
            cur: root,
        }
    }

    fn next_and_advance(&mut self) {
        let (node, index) = *self.path.last().unwrap();
        let parent_sup = if matches!(node, Node::Init()) {
            self.path.pop();
            let (_, parent_sup) = node_sup(self.cur, index);
            parent_sup
        } else {
            let (cur, parent_sup) = node_sup(node, index);
            let cur = cur.unwrap();
            self.cur = cur;
            parent_sup
        };

        // Now advance (update self.path to next).
        let (peek, _) = node_sup(self.cur, 0);
        if peek.is_some() {
            self.path.push((self.cur, 0)); // self.cur has children
            return;
        }
        let next = index + 1;
        if next < parent_sup {
            // node has more children
            self.path.last_mut().unwrap().1 = next;
            return;
        }
        loop {
            // pop stack
            if self.path.is_empty() {
                break;
            }
            let (parent, index) = self.path.pop().unwrap();
            let (_, sup) = node_sup(parent, index);
            if index + 1 < sup {
                self.path.push((parent, index + 1));
                break;
            }
        }
    }
}

impl<'a> Iterator for NodeIterator<'a> {
    type Item = Node<'a>;

    // Retrieves the node at path, and advances state.
    fn next(&mut self) -> Option<Self::Item> {
        if self.path.is_empty() {
            return None;
        }
        self.next_and_advance();
        Some(self.cur)
    }
}

// Returns index-th child and supremum for given node.
fn node_sup(node: Node, index: usize) -> (Option<Node>, usize) {
    let (node, sup) = match node {
        Node::Init() => unreachable!(),
        Node::FileUnitRef(r) => {
            let stmt = r.stmts.get(index).unwrap();
            (Node::StmtRef(stmt), r.stmts.len())
        }
        Node::StmtRef(r) => match &r.data {
            StmtData::AssignStmt { lhs, rhs, .. } => {
                (Node::ExprRef(if index == 0 { lhs } else { rhs }), 2)
            }
            StmtData::DefStmt { params, body, .. } => (
                if index < params.len() {
                    Node::ExprRef(params[index])
                } else {
                    Node::StmtRef(body.get(index - params.len()).unwrap())
                },
                params.len() + 1,
            ),

            StmtData::ExprStmt { x } => (Node::ExprRef(x), 1),
            StmtData::ForStmt { body, .. } => (Node::StmtRef(body.get(index).unwrap()), body.len()),
            StmtData::WhileStmt { cond, body, .. } => (
                if index == 0 {
                    Node::ExprRef(cond)
                } else {
                    Node::StmtRef(body.get(index - 1).unwrap())
                },
                body.len() + 1,
            ),

            StmtData::IfStmt {
                cond,
                then_arm,
                else_arm,
                ..
            } => (
                if index == 0 {
                    Node::ExprRef(cond)
                } else if index < then_arm.len() {
                    Node::StmtRef(then_arm.get(index - 1).unwrap())
                } else {
                    Node::StmtRef(else_arm.get(index - then_arm.len() - 1).unwrap())
                },
                1 + then_arm.len() + else_arm.len(),
            ),
            StmtData::ReturnStmt { result, .. } => (Node::ExprRef(result.unwrap()), 1),
            StmtData::LoadStmt { module, .. } => (Node::ExprRef(module), 1),
            _ => unreachable!("{:?}", r),
        },
        Node::ExprRef(r) => match r.data {
            ExprData::BinaryExpr { x, y, .. } => (Node::ExprRef(if index == 0 { x } else { y }), 2),
            ExprData::CallExpr { func, args, .. } => (
                Node::ExprRef(if index == 0 {
                    func
                } else {
                    args.get(index - 1).unwrap()
                }),
                1 + args.len(),
            ),
            ExprData::Comprehension { body, clauses, .. } => (
                if index == 0 {
                    Node::ExprRef(body)
                } else {
                    Node::ClauseRef(clauses.get(index - 1).unwrap())
                },
                1 + clauses.len(),
            ),

            ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => (
                Node::ExprRef(if index == 0 {
                    cond
                } else if index == 1 {
                    then_arm
                } else {
                    else_arm
                }),
                3,
            ),
            ExprData::DictEntry { key, value, .. } => {
                (Node::ExprRef(if index == 0 { key } else { value }), 2)
            }
            ExprData::DictExpr { list, .. } => {
                (Node::ExprRef(list.get(index).unwrap()), list.len())
            }

            ExprData::DotExpr { x, .. } => (Node::ExprRef(x), 1),
            ExprData::IndexExpr { x, y, .. } => (Node::ExprRef(if index == 0 { x } else { y }), 2),
            ExprData::LambdaExpr { params, body, .. } => (
                Node::ExprRef(if index < params.len() {
                    params.get(index).unwrap()
                } else {
                    body
                }),
                params.len() + 1,
            ),
            ExprData::ListExpr { list, .. } => {
                (Node::ExprRef(list.get(index).unwrap()), list.len())
            }

            ExprData::ParenExpr { x, .. } => (Node::ExprRef(x), 1),
            ExprData::SliceExpr {
                x, lo, hi, step, ..
            } if index < 4 => (
                Node::ExprRef(match index {
                    0 => x,
                    1 => lo.unwrap(),
                    2 => hi.unwrap(),
                    3 => step.unwrap(),
                    _ => unreachable!(),
                }),
                1 + if lo.is_some() { 1 } else { 0 }
                    + if hi.is_some() { 1 } else { 0 }
                    + if step.is_some() { 1 } else { 0 },
            ),
            ExprData::TupleExpr { list, .. } => {
                (Node::ExprRef(list.get(index).unwrap()), list.len())
            }
            ExprData::UnaryExpr { x, .. } => (Node::ExprRef(x.unwrap()), 1),

            // no children
            _ => return (None, 0),
        },
        Node::ClauseRef(r) => match r {
            Clause::ForClause { vars, x, .. } => {
                (Node::ExprRef(if index == 0 { vars } else { x }), 2)
            }
            Clause::IfClause { cond, .. } => (Node::ExprRef(cond), 1),
        },
    };
    (Some(node), sup)
}

#[cfg(test)]
mod test {

    use crate::Arena;
    use anyhow::Result;
    use std::path::Path;

    use crate::{
        parse,
        scan::Position,
        syntax::{Ident, Span},
        token::Token,
        Literal,
    };

    use super::*;
    struct TestCase<'a> {
        input: &'a str,
        want: Vec<Node<'a>>,
    }

    #[test]
    fn test_walk() -> Result<()> {
        let fake_pos = Position { line: 1, col: 1 };
        let span = Span {
            start: fake_pos,
            end: fake_pos,
        };
        let foobar_ident = Ident::new(fake_pos, "foobar");
        let foobar = Expr {
            span: span,
            data: ExprData::Ident(&foobar_ident),
        };
        let x_ident = Ident::new(fake_pos, "x");
        let x = Expr {
            span: span,
            data: ExprData::Ident(&x_ident),
        };
        let y_ident = Ident::new(fake_pos, "y");
        let y = Expr {
            span: span,
            data: ExprData::Ident(&y_ident),
        };
        let three = Expr {
            span: span,
            data: ExprData::Literal {
                token_pos: fake_pos,
                token: &Literal::Int(3),
            },
        };
        let y_expr = Expr {
            span: span,
            data: ExprData::BinaryExpr {
                x: &y,
                op_pos: fake_pos,
                op: Token::Eq,
                y: &three,
            },
        };
        let foobar_expr = Expr {
            span: span,
            data: ExprData::CallExpr {
                func: &foobar,
                lparen: fake_pos,
                args: &[&x, &y_expr],
                rparen: fake_pos,
            },
        };
        let foobar_stmt = Stmt {
            span: span,
            data: StmtData::ExprStmt { x: &foobar_expr },
        };
        let file_unit = FileUnit {
            path: Path::new("unknown"),
            stmts: &[&foobar_stmt],
            line_comments: &[],
            suffix_comments: &[],
        };
        let test_cases = vec![TestCase {
            input: "foobar(x, y=3)",
            want: vec![
                Node::FileUnitRef(&file_unit),
                Node::StmtRef(&foobar_stmt),
                Node::ExprRef(&foobar_expr),
                Node::ExprRef(&foobar),
                Node::ExprRef(&x),
                Node::ExprRef(&y_expr),
                Node::ExprRef(&y),
                Node::ExprRef(&three),
            ],
        }];
        let arena = Arena::new();
        for test_case in test_cases {
            let res = parse(&arena, test_case.input)?;
            let mut it = NodeIterator::new(Node::FileUnitRef(&res));

            let mut want_it = test_case.want.iter();
            loop {
                let next = it.next();
                let next_want = want_it.next();
                assert_eq!(
                    next.is_some(),
                    next_want.is_some(),
                    "\nnext:{:?}\nnext_want:{:?}",
                    next,
                    next_want
                );
                if next.is_none() {
                    break;
                }
                match (next.unwrap(), *next_want.unwrap()) {
                    (Node::FileUnitRef(x), Node::FileUnitRef(y)) => assert_eq!(x, y),
                    (Node::StmtRef(x), Node::StmtRef(y)) => assert_eq!(x.data, y.data),
                    (Node::ExprRef(x), Node::ExprRef(y)) => assert_eq!(x.data, y.data),
                    (Node::ClauseRef(x), Node::ClauseRef(y)) => assert_eq!(x, y),
                    (x, y) => assert!(false, "LEFT {:?} RIGHT {:?}", x, y),
                }
            }
        }
        Ok(())
    }
}
