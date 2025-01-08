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

use num_bigint::BigInt;

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
    Function, //Builtin

    // Special value used for trap.
    Abort(String),
}

impl Value {
    pub const ITERATE: Value = Value::Function;
    pub const ITERATOR_NEXT: Value = Value::Function;
    pub const INDEX_GET: Value = Value::Function;

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
            Value::Function => true,

            // Trap
            Value::Abort(_) => return self.clone(),
        })
    }

    pub fn equals(left: &Value, right: &Value) -> Self {
        Value::Bool(left == right)
    }

    pub fn not_equals(left: &Value, right: &Value) -> Self {
        Value::Bool(left != right)
    }

    pub fn less_than(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(left), Value::Int(right)) => Value::Bool(left < right),
            _ => todo!("< {:?} {:?}", &left, &right),
        }
    }

    pub fn less_than_or_equals(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(left), Value::Int(right)) => Value::Bool(left <= right),
            _ => todo!("< {:?} {:?}", &left, &right),
        }
    }

    pub fn greater_than(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(left), Value::Int(right)) => Value::Bool(left > right),
            _ => todo!("< {:?} {:?}", &left, &right),
        }
    }

    pub fn greater_than_or_equals(left: &Value, right: &Value) -> Value {
        match (&left, &right) {
            (Value::Int(left), Value::Int(right)) => Value::Bool(left >= right),
            _ => todo!("< {:?} {:?}", &left, &right),
        }
    }

    pub fn plus(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left + right),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 + right),
            (Value::Float(left), Value::Int(right)) => Value::Float(left + *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left + right),
            _ => todo!(),
        }
    }
    pub fn minus(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left - right),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 - right),
            (Value::Float(left), Value::Int(right)) => Value::Float(left - *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left - right),
            _ => todo!(),
        }
    }

    pub fn times(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left * right),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 * right),
            (Value::Float(left), Value::Int(right)) => Value::Float(left * *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left * right),
            _ => todo!(),
        }
    }

    pub fn div(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Float(*left as f64 / *right as f64),
            (Value::Int(left), Value::Float(right)) => Value::Float(*left as f64 / *right),
            (Value::Float(left), Value::Int(right)) => Value::Float(*left / *right as f64),
            (Value::Float(left), Value::Float(right)) => Value::Float(left / right),
            _ => todo!(),
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
            _ => todo!(),
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
            _ => todo!(),
        }
    }

    pub fn bitwise_and(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left & right),
            _ => todo!(),
        }
    }
    pub fn bitwise_or(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left | right),
            _ => todo!(),
        }
    }
    pub fn bitwise_xor(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left ^ right),
            _ => todo!(),
        }
    }
    pub fn shift_left(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left << right),
            _ => todo!(),
        }
    }
    pub fn shift_right(left: &Value, right: &Value) -> Value {
        match (left, right) {
            (Value::Int(left), Value::Int(right)) => Value::Int(left >> right),
            _ => todo!(),
        }
    }

    pub fn not(op: &Value) -> Value {
        match op {
            Value::Bool(v) => Value::Bool(!v),
            _ => todo!(),
        }
    }

    pub fn bitwise_not(op: &Value) -> Value {
        match op {
            Value::Int(v) => Value::Int(!v),
            _ => todo!(),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::None, Value::None) => true,
            (Value::Bool(left), Value::Bool(right)) => left == right,
            (Value::Bytes(left), Value::Bytes(right)) => *left == *right,
            (Value::Int(left), Value::Int(right)) => left == right,
            (Value::BigInt(left), Value::BigInt(right)) => left == right,
            (Value::Float(left), Value::Float(right)) => left == right,
            (Value::String(left), Value::String(right)) => left == right,
            _ => false,
        }
    }
}

impl Eq for Value {}

//trait Iterator {
//    fn next() bool
//}