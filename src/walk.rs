use crate::syntax::{Expr, ExprData, FileUnit, Stmt, StmtData};

// NodeIterator is a struct representing a path within a
// a (borrowed, read-only) AST node.
//
// For example: A --(i)--> B --(j)--> C with nodes A, B, C where
// B is the i-th child of A and C is the j-th child of B is
// represented as (A,i), (B,j)
// Invariant: the path is always valid.
pub struct NodeIterator<'a> {
    path: Vec<(Node<'a>, usize)>,
}

#[derive(Clone, Copy)]
pub enum Node<'a> {
    FileUnitRef(&'a FileUnit<'a>),
    StmtRef(&'a Stmt<'a>),
    ExprRef(&'a Expr<'a>),
}

impl<'a> NodeIterator<'a> {
    fn advance(&mut self, cur: &Node, index: usize) {}
}

impl<'a> Iterator for NodeIterator<'a> {
    type Item = Node<'a>;

    // Retrieves the node at path, and advances state.
    fn next(&mut self) -> Option<Self::Item> {
        if self.path.is_empty() {
            return None;
        }
        let x = self.path.pop().unwrap();
        match x {
            (f @ Node::FileUnitRef(r), index) => {
                let stmt = r.stmts.iter().nth(index).unwrap();
                self.advance(&f, index);
                return Some(Node::StmtRef(stmt));
            }
            (s @ Node::StmtRef(r), index) => 
                let cur = match &r.data {
                StmtData::AssignStmt { lhs, rhs, .. } => 
                Node::ExprRef(if index == 0 { lhs } else { rhs }),
                StmtData::BranchStmt { .. } => unreachable!(),
                StmtData::DefStmt { params, body, .. } => {
                    if index < params.len() {
                        Node::ExprRef(params[index])
                    } else {
                        Node::StmtRef(body.iter().nth(index - params.len()).unwrap())
                    }
                }
                StmtData::ExprStmt { x } => {
                    Node::ExprRef(x);
                }
                StmtData::ForStmt { body, .. } => {
                    StmtRef(body.iter().nth(index).unwrap());
                }
                StmtData::WhileStmt { cond, body, .. } => {
                    if index == 0 {
                        Node::ExprRef(cond)
                    } else {
                        Node::StmtRef(body.iter().nth(index - 1).unwrap())
                    }
                }
                StmtData::IfStmt {
                    cond,
                    then_arm,
                    else_arm,
                    ..
                } => 
                    if index == 0 {
                        Node::ExprRef(cond)
                    } else if index < then_arm.len() {
                        Node::StmtRef(then_arm.iter().nth(index - 1).unwrap())
                    } else {
                        Node::StmtRef(else_arm.iter().nth(index - then_arm.len() - 1).unwrap())
                    },
                StmtData::LoadStmt {
                    from,
                    to,
                    ..
                } => unreachable!(),
                StmtData::ReturnStmt { result } => 
                    ExprRef(result.unwrap()),
            }
            self.advance(&s, index);
            Some(cur)
        },
            (Node::ExprRef(r), index) => None,
        }
    }
}
