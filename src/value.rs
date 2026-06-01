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

// Starlark values are represented by the Value interface.
// The following built-in Value types are known to the evaluator:
//
//	NoneType        -- NoneType
//	Bool            -- bool
//	Bytes           -- bytes
//	Int             -- int
//	Float           -- float
//	String          -- string
//	*List           -- list
//	Tuple           -- tuple
//	*Dict           -- dict
//	*Set            -- set
//	*Function       -- function (implemented in Starlark)
//	*Builtin        -- builtin_function_or_method (function or method implemented in Go)

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Mutex;

use num_bigint::BigInt;

use crate::binding::BindingIndex;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum StarlarkType {
    NoneType,
    Bool,
    Int,
    BigInt,
    Float,
    String,
    Bytes,
    List,
    Tuple,
    Dict,
    Function,
}

#[derive(Debug, Clone)]
pub enum Reference {
    // Placeholder that only exists teporarily in MIR translation
    FreeVar(BindingIndex),
    Local(usize),
}

#[derive(Debug, Clone)]
pub enum Value {
    None,
    Bool(bool),
    Bytes(Box<[u8]>),
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    String(String),
    List(Box<[Value]>),
    Tuple(Box<[Value]>),
    Dict(HashMap<Value, Value>),
    //Set
    Function {
        func_index: usize,
        env: Box<[Rc<Mutex<Value>>]>,
    }, //Builtin

    Cell(Rc<Mutex<Value>>),
    // Code pointer
    FuncRef(usize),
    // Special value used for trap.
    Abort(String),
}

impl Value {
    pub fn deref(cell: &Rc<Mutex<Value>>) -> Value {
        cell.lock().unwrap().clone()
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            Value::None => "NoneType",
            Value::Bool(_) => "bool",
            Value::Int(_) => "int",
            Value::BigInt(_) => "int",
            Value::Float(_) => "float",
            Value::String(_) => "str",
            Value::Bytes(_) => "bytes",
            Value::List(_) => "list",
            Value::Tuple(_) => "tuple",
            Value::Dict(_) => "dict",
            Value::Function { .. } | Value::FuncRef(_) => "function",
            Value::Cell(_) => "cell",
            Value::Abort(_) => "abort",
        }
    }

    pub fn bool(&self) -> Self {
        Value::Bool(match self {
            Value::None => false,
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0,
            Value::String(s) => s.is_empty(),
            Value::Bytes(b) => b.is_empty(),
            Value::BigInt(big_int) => {
                use num_traits::identities::Zero;
                big_int.is_zero()
            }
            Value::List(l) => l.is_empty(),
            Value::Tuple(t) => t.is_empty(),
            Value::Dict(m) => m.is_empty(),
            Value::Function { .. } => true,

            Value::FuncRef(_) | Value::Cell(_) => return Value::Abort("cannot happen".to_string()),
            Value::Abort(_) => return self.clone(),
        })
    }

    pub fn truthy(&self) -> bool {
        match self {
            Value::None => false,
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0,
            Value::String(s) => !s.is_empty(),
            Value::Bytes(b) => !b.is_empty(),
            Value::BigInt(big_int) => {
                use num_traits::identities::Zero;
                !big_int.is_zero()
            }
            Value::List(l) => !l.is_empty(),
            Value::Tuple(t) => !t.is_empty(),
            Value::Dict(m) => !m.is_empty(),
            Value::Function { .. } => true,
            Value::FuncRef(_) => true,
            Value::Cell(_) => true,
            Value::Abort(_) => false,
        }
    }

    pub fn equals(left: &Value, right: &Value) -> Self {
        Value::Bool(left == right)
    }

    pub fn not_equals(left: &Value, right: &Value) -> Self {
        Value::Bool(left != right)
    }

    pub fn less_than(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (Value::Int(a), Value::Float(b)) => Value::Bool((*a as f64) < *b),
            (Value::Float(a), Value::Int(b)) => Value::Bool(*a < (*b as f64)),
            (Value::String(a), Value::String(b)) => Value::Bool(a < b),
            _ => Value::Abort(format!("cannot compare {:?} < {:?}", left.type_name(), right.type_name())),
        }
    }

    pub fn less_than_or_equals(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(a), Value::Int(b)) => Value::Bool(a <= b),
            (Value::Float(a), Value::Float(b)) => Value::Bool(a <= b),
            (Value::Int(a), Value::Float(b)) => Value::Bool((*a as f64) <= *b),
            (Value::Float(a), Value::Int(b)) => Value::Bool(*a <= (*b as f64)),
            (Value::String(a), Value::String(b)) => Value::Bool(a <= b),
            _ => Value::Abort(format!("cannot compare {:?} <= {:?}", left.type_name(), right.type_name())),
        }
    }

    pub fn greater_than(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(a), Value::Int(b)) => Value::Bool(a > b),
            (Value::Float(a), Value::Float(b)) => Value::Bool(a > b),
            (Value::Int(a), Value::Float(b)) => Value::Bool((*a as f64) > *b),
            (Value::Float(a), Value::Int(b)) => Value::Bool(*a > (*b as f64)),
            (Value::String(a), Value::String(b)) => Value::Bool(a > b),
            _ => Value::Abort(format!("cannot compare {:?} > {:?}", left.type_name(), right.type_name())),
        }
    }

    pub fn greater_than_or_equals(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(a), Value::Int(b)) => Value::Bool(a >= b),
            (Value::Float(a), Value::Float(b)) => Value::Bool(a >= b),
            (Value::Int(a), Value::Float(b)) => Value::Bool((*a as f64) >= *b),
            (Value::Float(a), Value::Int(b)) => Value::Bool(*a >= (*b as f64)),
            (Value::String(a), Value::String(b)) => Value::Bool(a >= b),
            _ => Value::Abort(format!("cannot compare {:?} >= {:?}", left.type_name(), right.type_name())),
        }
    }

    pub fn plus(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left + right),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 + right),
            (Value::Float(left), Value::Int(right)) => Value::Float(left + *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left + right),
            (Value::String(a), Value::String(b)) => {
                let mut s = String::with_capacity(a.len() + b.len());
                s.push_str(a);
                s.push_str(b);
                Value::String(s)
            }
            (Value::List(a), Value::List(b)) => {
                let mut v = Vec::with_capacity(a.len() + b.len());
                v.extend_from_slice(a);
                v.extend_from_slice(b);
                Value::List(v.into_boxed_slice())
            }
            (Value::Tuple(a), Value::Tuple(b)) => {
                let mut v = Vec::with_capacity(a.len() + b.len());
                v.extend_from_slice(a);
                v.extend_from_slice(b);
                Value::Tuple(v.into_boxed_slice())
            }
            _ => Value::Abort(format!("cannot add {} + {}", left.type_name(), right.type_name())),
        }
    }

    pub fn minus(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left - right),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 - right),
            (Value::Float(left), Value::Int(right)) => Value::Float(left - *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left - right),
            _ => Value::Abort(format!("cannot subtract {} - {}", left.type_name(), right.type_name())),
        }
    }

    pub fn times(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left * right),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 * right),
            (Value::Float(left), Value::Int(right)) => Value::Float(left * *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left * right),
            (Value::String(s), Value::Int(n)) | (Value::Int(n), Value::String(s)) => {
                if *n <= 0 {
                    Value::String(String::new())
                } else {
                    Value::String(s.repeat(*n as usize))
                }
            }
            (Value::List(l), Value::Int(n)) | (Value::Int(n), Value::List(l)) => {
                if *n <= 0 {
                    Value::List(Box::new([]))
                } else {
                    let mut v = Vec::with_capacity(l.len() * (*n as usize));
                    for _ in 0..*n {
                        v.extend_from_slice(l);
                    }
                    Value::List(v.into_boxed_slice())
                }
            }
            _ => Value::Abort(format!("cannot multiply {} * {}", left.type_name(), right.type_name())),
        }
    }

    pub fn div(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Float(*left as f64 / *right as f64),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 / *right),
            (Value::Float(left), Value::Int(right)) => Value::Float(*left / *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left / right),
            _ => Value::Abort(format!("cannot divide {} / {}", left.type_name(), right.type_name())),
        }
    }

    pub fn floor_div(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left.div_euclid(*right)),
            (Value::Int(left), Value::Float(right)) => {
                Value::Float((*left as f64).div_euclid(*right))
            }
            (Value::Float(left), Value::Int(right)) => Value::Float(left.div_euclid(*right as f64)),
            (Value::Float(left), Value::Float(right)) => Value::Float(left.div_euclid(*right)),
            _ => Value::Abort(format!("cannot floor-divide {} // {}", left.type_name(), right.type_name())),
        }
    }

    pub fn floor_rem(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left.rem_euclid(*right)),
            (Value::Int(left), Value::Float(right)) => {
                Value::Float((*left as f64).rem_euclid(*right))
            }
            (Value::Float(left), Value::Int(right)) => Value::Float(left.rem_euclid(*right as f64)),
            (Value::Float(left), Value::Float(right)) => Value::Float(left.rem_euclid(*right)),
            _ => Value::Abort(format!("cannot rem {} % {}", left.type_name(), right.type_name())),
        }
    }

    pub fn power(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(a), Value::Int(b)) if *b >= 0 => Value::Int(a.pow(*b as u32)),
            (Value::Int(a), Value::Int(b)) => Value::Float((*a as f64).powf(*b as f64)),
            (Value::Float(a), Value::Int(b)) => Value::Float(a.powf(*b as f64)),
            (Value::Int(a), Value::Float(b)) => Value::Float((*a as f64).powf(*b)),
            (Value::Float(a), Value::Float(b)) => Value::Float(a.powf(*b)),
            _ => Value::Abort(format!("cannot power {} ** {}", left.type_name(), right.type_name())),
        }
    }

    pub fn bitwise_and(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left & right),
            _ => Value::Abort(format!("cannot bitwise-and {} & {}", left.type_name(), right.type_name())),
        }
    }

    pub fn bitwise_or(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left | right),
            _ => Value::Abort(format!("cannot bitwise-or {} | {}", left.type_name(), right.type_name())),
        }
    }

    pub fn bitwise_xor(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left ^ right),
            _ => Value::Abort(format!("cannot bitwise-xor {} ^ {}", left.type_name(), right.type_name())),
        }
    }

    pub fn shift_left(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left << right),
            _ => Value::Abort(format!("cannot shift-left {} << {}", left.type_name(), right.type_name())),
        }
    }

    pub fn shift_right(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left >> right),
            _ => Value::Abort(format!("cannot shift-right {} >> {}", left.type_name(), right.type_name())),
        }
    }

    pub fn not(op: &Value) -> Value {
        match op {
            Value::Bool(v) => Value::Bool(!v),
            _ => Value::Abort(format!("cannot apply 'not' to {}", op.type_name())),
        }
    }

    pub fn bitwise_not(op: &Value) -> Value {
        match op {
            Value::Int(v) => Value::Int(!v),
            _ => Value::Abort(format!("cannot apply '~' to {}", op.type_name())),
        }
    }

    pub fn unary_plus(op: &Value) -> Value {
        match op {
            Value::Int(v) => Value::Int(*v),
            Value::Float(v) => Value::Float(*v),
            _ => Value::Abort(format!("cannot apply unary '+' to {}", op.type_name())),
        }
    }

    pub fn unary_minus(op: &Value) -> Value {
        match op {
            Value::Int(v) => Value::Int(-v),
            Value::Float(v) => Value::Float(-v),
            _ => Value::Abort(format!("cannot apply unary '-' to {}", op.type_name())),
        }
    }

    pub fn len(&self) -> Value {
        match self {
            Value::List(l) => Value::Int(l.len() as i64),
            Value::Tuple(t) => Value::Int(t.len() as i64),
            Value::String(s) => Value::Int(s.len() as i64),
            Value::Dict(d) => Value::Int(d.len() as i64),
            _ => Value::Abort(format!("object of type '{}' has no len()", self.type_name())),
        }
    }

    pub fn index_get(&self, idx: &Value) -> Value {
        match (self, idx) {
            (Value::List(l), Value::Int(i)) => {
                let i = *i as usize;
                if i < l.len() {
                    l[i].clone()
                } else {
                    Value::Abort(format!("index {} out of range for list of length {}", i, l.len()))
                }
            }
            (Value::Tuple(t), Value::Int(i)) => {
                let i = *i as usize;
                if i < t.len() {
                    t[i].clone()
                } else {
                    Value::Abort(format!("index {} out of range for tuple of length {}", i, t.len()))
                }
            }
            (Value::String(s), Value::Int(i)) => {
                let i = *i as usize;
                if i < s.len() {
                    Value::String(s[i..i + 1].to_string())
                } else {
                    Value::Abort(format!("index {} out of range for string of length {}", i, s.len()))
                }
            }
            (Value::Dict(d), key) => {
                match d.get(key) {
                    Some(v) => v.clone(),
                    None => Value::Abort(format!("key not found in dict")),
                }
            }
            _ => Value::Abort(format!("cannot index {} with {}", self.type_name(), idx.type_name())),
        }
    }

    pub fn index_set(&mut self, idx: Value, val: Value) -> Value {
        match self {
            Value::Dict(d) => {
                d.insert(idx, val);
                Value::None
            }
            Value::List(l) => {
                if let Value::Int(i) = idx {
                    let i = i as usize;
                    if i < l.len() {
                        l[i] = val;
                        Value::None
                    } else {
                        Value::Abort(format!("index {} out of range for list of length {}", i, l.len()))
                    }
                } else {
                    Value::Abort(format!("list indices must be int, not {}", idx.type_name()))
                }
            }
            _ => Value::Abort(format!("{} does not support item assignment", self.type_name())),
        }
    }

    pub fn slice(&self, lo: Option<&Value>, hi: Option<&Value>, step: Option<&Value>) -> Value {
        let lo_idx = lo.map(|v| match v {
            Value::Int(i) => *i as isize,
            Value::None => 0,
            _ => 0,
        }).unwrap_or(0);
        let hi_idx = hi.map(|v| match v {
            Value::Int(i) => *i as isize,
            Value::None => isize::MAX,
            _ => isize::MAX,
        }).unwrap_or(isize::MAX);

        match self {
            Value::List(l) => {
                let len = l.len() as isize;
                let lo = lo_idx.max(0).min(len) as usize;
                let hi = hi_idx.max(0).min(len) as usize;
                if lo >= hi {
                    Value::List(Box::new([]))
                } else {
                    Value::List(l[lo..hi].into())
                }
            }
            Value::Tuple(t) => {
                let len = t.len() as isize;
                let lo = lo_idx.max(0).min(len) as usize;
                let hi = hi_idx.max(0).min(len) as usize;
                if lo >= hi {
                    Value::Tuple(Box::new([]))
                } else {
                    Value::Tuple(t[lo..hi].into())
                }
            }
            Value::String(s) => {
                let len = s.len() as isize;
                let lo = lo_idx.max(0).min(len) as usize;
                let hi = hi_idx.max(0).min(len) as usize;
                if lo >= hi {
                    Value::String(String::new())
                } else {
                    Value::String(s[lo..hi].to_string())
                }
            }
            _ => Value::Abort(format!("cannot slice {}", self.type_name())),
        }
    }

    pub fn field_get(&self, name: &str) -> Value {
        match self {
            Value::Dict(d) => {
                // Dict fields via string key
                let key = Value::String(name.to_string());
                match d.get(&key) {
                    Some(v) => v.clone(),
                    None => Value::Abort(format!("dict has no key '{}'", name)),
                }
            }
            _ => Value::Abort(format!("{} has no field '{}'", self.type_name(), name)),
        }
    }

    pub fn is_in(container: &Value, element: &Value) -> Value {
        match container {
            Value::List(l) => Value::Bool(l.iter().any(|v| v == element)),
            Value::Tuple(t) => Value::Bool(t.iter().any(|v| v == element)),
            Value::String(s) => match element {
                Value::String(sub) => Value::Bool(s.contains(sub.as_str())),
                _ => Value::Abort("'in' requires string on left side for string container".to_string()),
            },
            Value::Dict(d) => Value::Bool(d.contains_key(element)),
            _ => Value::Abort(format!("cannot use 'in' with {}", container.type_name())),
        }
    }

    pub fn not_in(container: &Value, element: &Value) -> Value {
        match Self::is_in(container, element) {
            Value::Bool(b) => Value::Bool(!b),
            other => other,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::None, Value::None) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            // Starlark: True == 1, False == 0
            (Value::Bool(b), Value::Int(i)) | (Value::Int(i), Value::Bool(b)) => {
                *i == if *b { 1 } else { 0 }
            }
            (Value::Bytes(left), Value::Bytes(right)) => *left == *right,
            (Value::Int(left), Value::Int(right)) => left == right,
            (Value::BigInt(left), Value::BigInt(right)) => left == right,
            (Value::Float(left), Value::Float(right)) => left == right,
            (Value::String(left), Value::String(right)) => left == right,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                for (k, v) in a.iter() {
                    match b.get(k) {
                        Some(bv) if bv == v => {}
                        _ => return false,
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::None => {}
            Value::Bool(b) => b.hash(state),
            Value::Int(i) => i.hash(state),
            Value::BigInt(bi) => bi.hash(state),
            Value::Float(f) => f.to_bits().hash(state),
            Value::String(s) => s.hash(state),
            Value::Bytes(b) => b.hash(state),
            Value::Tuple(t) => {
                for v in t.iter() {
                    v.hash(state);
                }
            }
            Value::FuncRef(i) => i.hash(state),
            // Lists and Dicts are not hashable in Starlark
            _ => {}
        }
    }
}
