use std::fmt;
use crate::keywords::NOT;
use crate::helper::vec_to_string_join_by_comma;
use crate::obj::Obj;
use crate::atom::Atom;
use crate::keywords::{FINITE_SET, LEFT_BRACKET, NONEMPTY_SET, RIGHT_BRACKET, SET};

#[derive(Clone)]
pub enum ParamDefWithParamSet {
    ParamAndItsSetPair(String, Obj),
    ParamsAndTheirSetsPair(Vec<String>, Obj),
}

#[derive(Clone)]
pub enum ParamDefWithParamTypeAndProperty {
    ParamAndItsTypePair(String, ParameterType),
    ParamsAndTheirTypePair(Vec<String>, ParameterType),
    ParamsPropertyPair(Vec<String>, bool, Atom),
}

#[derive(Clone)]
pub enum ParameterType {
    Set(SetAsParamSet),
    NonemptySet(NonemptySetAsParamSet),
    FiniteSet(FiniteSetAsParamSet),
    Obj(Obj),
}

#[derive(Clone)]
pub struct SetAsParamSet {}

#[derive(Clone)]
pub struct NonemptySetAsParamSet {}

#[derive(Clone)]
pub struct FiniteSetAsParamSet {}

impl SetAsParamSet {
    pub fn new() -> Self {
        SetAsParamSet {}
    }
}

impl NonemptySetAsParamSet {
    pub fn new() -> Self {
        NonemptySetAsParamSet {}
    }
}

impl FiniteSetAsParamSet {
    pub fn new() -> Self {
        FiniteSetAsParamSet {}
    }
}

impl fmt::Display for ParameterType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParameterType::Set(set) => write!(f, "{}", set.to_string()),
            ParameterType::NonemptySet(nonempty_set) => write!(f, "{}", nonempty_set.to_string()),
            ParameterType::FiniteSet(finite_set) => write!(f, "{}", finite_set.to_string()),
            ParameterType::Obj(obj) => write!(f, "{}", obj),
        }
    }
}

impl fmt::Display for SetAsParamSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", SET)
    }
}

impl fmt::Display for NonemptySetAsParamSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", NONEMPTY_SET)
    }
}

impl fmt::Display for FiniteSetAsParamSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", FINITE_SET)
    }
}

impl fmt::Display for ParamDefWithParamTypeAndProperty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamDefWithParamTypeAndProperty::ParamAndItsTypePair(param, param_type) => write!(f, "{} {}", param, param_type),
            ParamDefWithParamTypeAndProperty::ParamsAndTheirTypePair(params, param_type) => write!(f, "{} {}", vec_to_string_join_by_comma(params), param_type),
            ParamDefWithParamTypeAndProperty::ParamsPropertyPair(params, is_true, property) => if *is_true { write!(f, "{}{}{} {}", LEFT_BRACKET, vec_to_string_join_by_comma(params), RIGHT_BRACKET, property) } else { write!(f, "{}{}{} {} {}", LEFT_BRACKET, vec_to_string_join_by_comma(params), RIGHT_BRACKET, format!(" {} ", NOT), property) },
        }
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