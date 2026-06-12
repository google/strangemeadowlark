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

//! Static types for the gradual typing system.
//!
//! StaticType represents the compile-time type of a local variable.
//! The typing pass (Phase 2) assigns StaticType to each LocalDef after
//! resolution. Unannotated locals default to Any.
//!
//! The consistency relation (∼) follows Siek & Taha 2006:
//!   T ∼ Any  for all T (both directions)
//!   T ∼ T    for all T (reflexivity)
//!   T1 ≁ T2  if T1 ≠ T2 and neither is Any

use std::fmt::Display;

use crate::syntax::TypeExpr;

/// The static type of a local variable, as determined by the typing pass.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StaticType {
    NoneType,
    Bool,
    Int,
    Float,
    Str,
    Label,
    List(Box<StaticType>),
    Dict(Box<StaticType>, Box<StaticType>),
    Tuple(Vec<StaticType>),
    Record(String), // name reference to a record definition
    Function,
    Any, // typing.Any — the gradual type boundary
}

impl StaticType {
    /// The default type for unannotated locals.
    pub fn any() -> Self {
        StaticType::Any
    }

    /// Convert a TypeExpr (from the parser) to a StaticType.
    /// This is used during the typing pass to resolve annotations.
    pub fn from_type_expr(expr: &TypeExpr) -> Self {
        match expr {
            TypeExpr::NoneType => StaticType::NoneType,
            TypeExpr::Bool => StaticType::Bool,
            TypeExpr::Int => StaticType::Int,
            TypeExpr::Float => StaticType::Float,
            TypeExpr::Str => StaticType::Str,
            TypeExpr::Label => StaticType::Label,
            TypeExpr::List(elem) => StaticType::List(Box::new(StaticType::from_type_expr(elem))),
            TypeExpr::Dict(key, val) => {
                StaticType::Dict(Box::new(StaticType::from_type_expr(key)), Box::new(StaticType::from_type_expr(val)))
            }
            TypeExpr::Tuple(elems) => {
                StaticType::Tuple(elems.iter().map(|e| StaticType::from_type_expr(e)).collect())
            }
            TypeExpr::Any => StaticType::Any,
            TypeExpr::Name(ident) => StaticType::Record(ident.name.to_string()),
        }
    }

    /// Consistency relation (∼) following Siek & Taha 2006.
    ///   T ∼ Any  for all T (both directions)
    ///   T ∼ T    for all T (reflexivity)
    ///   T1 ≁ T2  if T1 ≠ T2 and neither is Any
    pub fn is_consistent_with(&self, other: &StaticType) -> bool {
        if *self == StaticType::Any || *other == StaticType::Any {
            return true;
        }
        match (self, other) {
            (StaticType::List(a), StaticType::List(b)) => a.is_consistent_with(b),
            (StaticType::Dict(ak, av), StaticType::Dict(bk, bv)) => {
                ak.is_consistent_with(bk) && av.is_consistent_with(bv)
            }
            (StaticType::Tuple(a), StaticType::Tuple(b)) => {
                a.len() == b.len()
                    && a.iter().zip(b.iter()).all(|(x, y)| x.is_consistent_with(y))
            }
            (StaticType::Record(a), StaticType::Record(b)) => a == b,
            _ => self == other,
        }
    }

    /// Returns true if this is a concrete (non-Any) type.
    pub fn is_concrete(&self) -> bool {
        !matches!(self, StaticType::Any)
    }

    /// Returns the type of a literal value, for inference.
    pub fn from_literal_value(value: &crate::value::Value) -> Option<StaticType> {
        match value {
            crate::value::Value::None => Some(StaticType::NoneType),
            crate::value::Value::Bool(_) => Some(StaticType::Bool),
            crate::value::Value::Int(_) => Some(StaticType::Int),
            crate::value::Value::BigInt(_) => Some(StaticType::Int),
            crate::value::Value::Float(_) => Some(StaticType::Float),
            crate::value::Value::String(s) => {
                // Heuristic: strings matching a label pattern infer as Label
                if looks_like_label(s) {
                    Some(StaticType::Label)
                } else {
                    Some(StaticType::Str)
                }
            }
            _ => None,
        }
    }
}

/// Heuristic: a string that looks like a Bazel label (//pkg:target).
fn looks_like_label(s: &str) -> bool {
    s.starts_with("//") && s.contains(':')
}

impl Display for StaticType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StaticType::NoneType => write!(f, "None"),
            StaticType::Bool => write!(f, "bool"),
            StaticType::Int => write!(f, "int"),
            StaticType::Float => write!(f, "float"),
            StaticType::Str => write!(f, "str"),
            StaticType::Label => write!(f, "label"),
            StaticType::List(elem) => write!(f, "list[{}]", elem),
            StaticType::Dict(key, val) => write!(f, "dict[{}, {}]", key, val),
            StaticType::Tuple(elems) => {
                write!(f, "tuple[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "]")
            }
            StaticType::Record(name) => write!(f, "{}", name),
            StaticType::Function => write!(f, "Function"),
            StaticType::Any => write!(f, "Any"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_consistency_basic() {
        // Any ∼ T for all T
        assert!(StaticType::Any.is_consistent_with(&StaticType::Int));
        assert!(StaticType::Int.is_consistent_with(&StaticType::Any));
        assert!(StaticType::Any.is_consistent_with(&StaticType::Any));

        // Reflexivity
        assert!(StaticType::Int.is_consistent_with(&StaticType::Int));
        assert!(StaticType::Str.is_consistent_with(&StaticType::Str));
        assert!(StaticType::Label.is_consistent_with(&StaticType::Label));

        // Different concrete types are NOT consistent
        assert!(!StaticType::Int.is_consistent_with(&StaticType::Float));
        assert!(!StaticType::Label.is_consistent_with(&StaticType::Str));
        assert!(!StaticType::Int.is_consistent_with(&StaticType::Bool));
    }

    #[test]
    fn test_consistency_structural() {
        let list_int = StaticType::List(Box::new(StaticType::Int));
        let list_any = StaticType::List(Box::new(StaticType::Any));
        let list_str = StaticType::List(Box::new(StaticType::Str));

        assert!(list_int.is_consistent_with(&list_any));
        assert!(list_any.is_consistent_with(&list_int));
        assert!(!list_int.is_consistent_with(&list_str));

        let dict_str_int = StaticType::Dict(Box::new(StaticType::Str), Box::new(StaticType::Int));
        let dict_any_any = StaticType::Dict(Box::new(StaticType::Any), Box::new(StaticType::Any));
        assert!(dict_str_int.is_consistent_with(&dict_any_any));
    }

    #[test]
    fn test_from_type_expr() {
        use crate::scan::Position;
        use crate::syntax::Ident;

        assert_eq!(StaticType::from_type_expr(&TypeExpr::Int), StaticType::Int);
        assert_eq!(StaticType::from_type_expr(&TypeExpr::Label), StaticType::Label);
        assert_eq!(StaticType::from_type_expr(&TypeExpr::Any), StaticType::Any);
        assert_eq!(
            StaticType::from_type_expr(&TypeExpr::List(&TypeExpr::Int)),
            StaticType::List(Box::new(StaticType::Int))
        );

        let ident = Ident::new(Position::new(), "Point");
        assert_eq!(
            StaticType::from_type_expr(&TypeExpr::Name(&ident)),
            StaticType::Record("Point".to_string())
        );
    }

    #[test]
    fn test_label_inference() {
        assert!(looks_like_label("//src/main:app"));
        assert!(looks_like_label("//pkg:target"));
        assert!(!looks_like_label("hello world"));
        assert!(!looks_like_label("just_a_string"));
    }
}
