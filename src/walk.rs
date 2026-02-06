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

use crate::syntax::{Clause, Expr, ExprData, FileUnit, Span, Stmt, StmtData};

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
    cur: Option<Node<'a>>,
}

#[derive(Clone, Copy, Debug)]
pub enum Node<'a> {
    Init(&'a [&'a Stmt<'a>]),
    FileUnitRef(&'a FileUnit<'a>),
    StmtRef(&'a Stmt<'a>),
    ExprRef(&'a Expr<'a>),
    ClauseRef(&'a Clause<'a>),
}

impl<'a> std::fmt::Display for Node<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Init(stmts) => {
                write!(f, "Init([")?;
                for (i, stmt) in stmts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "<stmt>")?;
                }
                write!(f, "])")
            }
            Node::FileUnitRef(file_unit) => write!(f, "FileUnitRef(...)"),
            Node::StmtRef(stmt) => write!(f, "StmtRef(...)"),
            Node::ExprRef(expr) => write!(f, "ExprRef(...)"),
            Node::ClauseRef(clause) => write!(f, "ClauseRef(...)"),
        }
    }
}
impl Node<'_> {
    pub fn id(&self) -> Option<usize> {
        match self {
            Node::StmtRef(s) => Some(s.id.0),
            Node::ExprRef(e) => Some(e.id.0),
            _ => None,
        }
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            Node::StmtRef(s) => Some(s.span),
            Node::ExprRef(e) => Some(e.span),
            _ => None,
        }
    }
}

impl<'a> NodeIterator<'a> {
    pub fn new(stmts: &'a [&'a Stmt<'a>]) -> Self {
        NodeIterator {
            path: if stmts.is_empty() {
                vec![]
            } else {
                vec![(Node::Init(stmts), 0)]
            },
            cur: None,
        }
    }

    fn next_and_advance(&mut self) {
        let (node, index) = *self.path.last().unwrap();
        let (cur, parent_sup) = node_sup(node, index);
        self.cur = cur;
        let cur = cur.unwrap();
        // Now advance (prepare self.path to next).
        // Case 1: `self.cur` has children.
        let (peek, _) = node_sup(cur, 0);
        if peek.is_some() {
            self.path.push((cur, 0));
            return;
        }
        let next = index + 1;
        // Case 2: `node` has more children
        if next < parent_sup {
            self.path.last_mut().unwrap().1 = next;
            return;
        }
        // Case 3: `self.cur` was the last child.
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
        self.cur
    }
}

// Returns index-th child and supremum for given node.
fn node_sup(node: Node, index: usize) -> (Option<Node>, usize) {
    match node {
        Node::Init(stmts) => (stmts.get(index).map(|&s| Node::StmtRef(s)), stmts.len()),
        Node::FileUnitRef(r) => (r.stmts.get(index).map(|&s| Node::StmtRef(s)), r.stmts.len()),
        Node::StmtRef(r) => match &r.data {
            StmtData::AssignStmt { lhs, rhs, .. } => (
                Some(Node::ExprRef(if index == 0 { lhs } else { rhs })),
                2,
            ),
            StmtData::BranchStmt { .. } => (None, 0),
            StmtData::DefStmt { params, body, .. } => (
                if index < params.len() {
                    Some(Node::ExprRef(params[index]))
                } else if index < params.len() + body.len() {
                    Some(Node::StmtRef(body[index - params.len()]))
                } else {
                    None
                },
                params.len() + body.len(),
            ),

            StmtData::ExprStmt { x } => (Some(Node::ExprRef(x)), 1),
            StmtData::ForStmt { vars, x, body, .. } => (
                if index == 0 {
                    Some(Node::ExprRef(vars))
                } else if index == 1 {
                    Some(Node::ExprRef(x))
                } else if index < 2 + body.len() {
                    Some(Node::StmtRef(body[index - 2]))
                } else {
                    None
                },
                2 + body.len(),
            ),
            StmtData::WhileStmt { cond, body, .. } => (
                if index == 0 {
                    Some(Node::ExprRef(cond))
                } else if index < 1 + body.len() {
                    Some(Node::StmtRef(body[index - 1]))
                } else {
                    None
                },
                1 + body.len(),
            ),

            StmtData::IfStmt {
                cond,
                then_arm,
                else_arm,
                ..
            } => (
                if index == 0 {
                    Some(Node::ExprRef(cond))
                } else if index < 1 + then_arm.len() {
                    Some(Node::StmtRef(then_arm[index - 1]))
                } else if index < 1 + then_arm.len() + else_arm.len() {
                    Some(Node::StmtRef(else_arm[index - then_arm.len() - 1]))
                } else {
                    None
                },
                1 + then_arm.len() + else_arm.len(),
            ),
            StmtData::ReturnStmt { result, .. } => {
                (result.map(Node::ExprRef), if result.is_some() { 1 } else { 0 })
            }
            StmtData::LoadStmt { module, .. } => (Some(Node::ExprRef(module)), 1),
        },
        Node::ExprRef(r) => match &r.data {
            ExprData::BinaryExpr { x, y, .. } => (Some(Node::ExprRef(if index == 0 { x } else { y })), 2),
            ExprData::CallExpr { func, args, .. } => (
                if index == 0 {
                    Some(Node::ExprRef(func))
                } else {
                    args.get(index - 1).map(|&a| Node::ExprRef(a))
                },
                1 + args.len(),
            ),
            ExprData::Comprehension { body, clauses, .. } => (
                if index == 0 {
                    Some(Node::ExprRef(body))
                } else {
                    clauses.get(index - 1).map(|&c| Node::ClauseRef(c))
                },
                1 + clauses.len(),
            ),

            ExprData::CondExpr {
                cond,
                then_arm,
                else_arm,
                ..
            } => (
                Some(Node::ExprRef(if index == 0 {
                    cond
                } else if index == 1 {
                    then_arm
                } else {
                    else_arm
                })),
                3,
            ),
            ExprData::DictEntry { key, value, .. } => {
                (Some(Node::ExprRef(if index == 0 { key } else { value })), 2)
            }
            ExprData::DictExpr { list, .. } => {
                (list.get(index).map(|&e| Node::ExprRef(e)), list.len())
            }

            ExprData::DotExpr { x, .. } => (Some(Node::ExprRef(x)), 1),
            ExprData::IndexExpr { x, y, .. } => (Some(Node::ExprRef(if index == 0 { x } else { y })), 2),
            ExprData::LambdaExpr { params, body, .. } => (
                if index < params.len() {
                    params.get(index).map(|&p| Node::ExprRef(p))
                } else if index == params.len() {
                    Some(Node::ExprRef(body))
                } else {
                    None
                },
                params.len() + 1,
            ),
            ExprData::ListExpr { list, .. } => {
                (list.get(index).map(|&e| Node::ExprRef(e)), list.len())
            }

            ExprData::ParenExpr { x, .. } => (Some(Node::ExprRef(x)), 1),
            ExprData::SliceExpr {
                x, lo, hi, step, ..
            } => {
                let children = [
                    Some(Node::ExprRef(x)),
                    lo.map(Node::ExprRef),
                    hi.map(Node::ExprRef),
                    step.map(Node::ExprRef),
                ];
                let valid_children: Vec<Node> = children.iter().filter_map(|&c| c).collect();
                (valid_children.get(index).copied(), valid_children.len())
            }
            ExprData::TupleExpr { list, .. } => {
                (list.get(index).map(|&e| Node::ExprRef(e)), list.len())
            }
            ExprData::UnaryExpr { x, .. } => (x.map(Node::ExprRef), if x.is_some() { 1 } else { 0 }),

            // no children
            _ => (None, 0),
        },
        Node::ClauseRef(r) => match r {
            Clause::ForClause { vars, x, .. } => {
                (Some(Node::ExprRef(if index == 0 { vars } else { x })), 2)
            }
            Clause::IfClause { cond, .. } => (Some(Node::ExprRef(cond)), 1),
        },
    }
}

#[cfg(test)]
mod test {

    use crate::{Arena, ID_GEN};
    use anyhow::Result;
    use std::collections::HashMap;
    use std::path::Path;

    use crate::{
        Literal, parse,
        scan::Position,
        syntax::{Ident, Span},
        token::Token,
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
            id: ID_GEN.next_expr_id(),
            span: span,
            data: ExprData::Ident(&foobar_ident),
        };
        let x_ident = Ident::new(fake_pos, "x");
        let x = Expr {
            id: ID_GEN.next_expr_id(),
            span: span,
            data: ExprData::Ident(&x_ident),
        };
        let y_ident = Ident::new(fake_pos, "y");
        let y = Expr {
            id: ID_GEN.next_expr_id(),
            span: span,
            data: ExprData::Ident(&y_ident),
        };
        let three = Expr {
            id: ID_GEN.next_expr_id(),
            span: span,
            data: ExprData::Literal {
                token_pos: fake_pos,
                token: &Literal::Int(3),
            },
        };
        let y_expr = Expr {
            id: ID_GEN.next_expr_id(),
            span: span,
            data: ExprData::BinaryExpr {
                x: &y,
                op_pos: fake_pos,
                op: Token::Eq,
                y: &three,
            },
        };
        let foobar_expr = Expr {
            id: ID_GEN.next_expr_id(),
            span: span,
            data: ExprData::CallExpr {
                func: &foobar,
                lparen: fake_pos,
                args: &[&x, &y_expr],
                rparen: fake_pos,
            },
        };
        let foobar_stmt = Stmt {
            id: ID_GEN.next_stmt_id(),
            span: span,
            data: StmtData::ExprStmt { x: &foobar_expr },
        };
        let _file_unit = FileUnit {
            path: Path::new("unknown"),
            stmts: &[&foobar_stmt],
            line_comments: &[],
            suffix_comments: &[],
            comments_before: HashMap::new(),
            comments_suffix: HashMap::new(),
            comments_after: HashMap::new(),
        };
        let test_cases = vec![TestCase {
            input: "foobar(x, y=3)",
            want: vec![
                //              Node::FileUnitRef(&file_unit),
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
            let mut it = NodeIterator::new(&res.stmts);

            let mut index = 0;
            let mut want_it = test_case.want.iter();
            loop {
                let next = it.next();
                let next_want = want_it.next();
                if next.is_none() && next_want.is_none() {
                    break;
                }
                assert_eq!(
                    next.is_some(),
                    next_want.is_some(),
                    "\nnext:{:?}\nnext_want:{:?}",
                    next,
                    next_want
                );
                let actual = next.unwrap();
                let expected = *next_want.unwrap();
                match (actual, expected) {
                    (Node::FileUnitRef(x), Node::FileUnitRef(y)) => assert_eq!(x, y),
                    (Node::StmtRef(x), Node::StmtRef(y)) => assert_eq!(x.data, y.data),
                    (Node::ExprRef(x), Node::ExprRef(y)) => assert_eq!(x.data, y.data),
                    (Node::ClauseRef(x), Node::ClauseRef(y)) => assert_eq!(x, y),
                    (x, y) => assert!(false, "index {index} \n LEFT {:?} \n\nRIGHT {:?}", x, y),
                }
                index += 1;
            }
        }
        Ok(())
    }
}
