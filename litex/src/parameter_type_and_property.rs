use std::fmt;
use crate::atom::{IdentifierOrIdentifierWithMod};
use crate::keywords::STRUCT;
use crate::helper::vec_to_string_join_by_comma;
use crate::obj::Obj;
use crate::keywords::{FINITE_SET, NONEMPTY_SET, SET};

#[derive(Clone)]
pub enum ParamDefWithParamSet {
    ParamAndItsSetPair(String, Obj),
    ParamsAndTheirSetsPair(Vec<String>, Obj),
}

#[derive(Clone)]
pub enum ParamDefWithParamType {
    ParamAndItsTypePair(String, ParamType),
    ParamsAndTheirTypePair(Vec<String>, ParamType),
}

#[derive(Clone)]
pub enum ParamType {
    Set(Set),
    NonemptySet(NonemptySet),
    FiniteSet(FiniteSet),
    Obj(Obj),
    Struct(StructParamType),
}

#[derive(Clone)]
pub struct StructParamType {
    pub name: IdentifierOrIdentifierWithMod,
}

impl StructParamType {
    pub fn new(name: IdentifierOrIdentifierWithMod) -> Self {
        StructParamType { name }
    }
}

#[derive(Clone)]
pub struct Set {}

#[derive(Clone)]
pub struct NonemptySet {}

#[derive(Clone)]
pub struct FiniteSet {}

impl Set {
    pub fn new() -> Self {
        Set {}
    }
}

impl NonemptySet {
    pub fn new() -> Self {
        NonemptySet {}
    }
}

impl FiniteSet {
    pub fn new() -> Self {
        FiniteSet {}
    }
}

impl fmt::Display for ParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamType::Set(set) => write!(f, "{}", set.to_string()),
            ParamType::NonemptySet(nonempty_set) => write!(f, "{}", nonempty_set.to_string()),
            ParamType::FiniteSet(finite_set) => write!(f, "{}", finite_set.to_string()),
            ParamType::Obj(obj) => write!(f, "{}", obj),
            ParamType::Struct(struct_param_type) => write!(f, "{}", struct_param_type),
        }
    }
}

impl fmt::Display for StructParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", STRUCT, self.name)
    }
}

impl fmt::Display for Set {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", SET)
    }
}

impl fmt::Display for NonemptySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", NONEMPTY_SET)
    }
}

impl fmt::Display for FiniteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", FINITE_SET)
    }
}

impl fmt::Display for ParamDefWithParamSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamDefWithParamSet::ParamAndItsSetPair(param, param_set) => write!(f, "{} {}", param, param_set),
            ParamDefWithParamSet::ParamsAndTheirSetsPair(params, param_set) => write!(f, "{} {}", vec_to_string_join_by_comma(params), param_set),
        }
    }
}

impl fmt::Display for ParamDefWithParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamDefWithParamType::ParamAndItsTypePair(param, param_type) => write!(f, "{} {}", param, param_type),
            ParamDefWithParamType::ParamsAndTheirTypePair(params, param_type) => write!(f, "{} {}", vec_to_string_join_by_comma(params), param_type),
        }
    }
}

impl ParamDefWithParamType {
    pub fn new(param: String, param_type: ParamType) -> Self {
        ParamDefWithParamType::ParamAndItsTypePair(param, param_type)
    }
}