use std::fmt;
use crate::obj::Obj;
use crate::consts::{SET, NONEMPTY_SET, FINITE_SET};

pub enum ParameterSet {
    Set(SetAsParamSet),
    NonemptySet(NonemptySetAsParamSet),
    FiniteSet(FiniteSetAsParamSet),
    Obj(Obj),
}

pub struct SetAsParamSet {}

pub struct NonemptySetAsParamSet {}

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

// impl ParameterSet {
//     pub fn box_set() -> box_ParameterSet {
//         Box::new(ParameterSet::Set(SetAsParamSet::new()))
//     }
//     pub fn box_nonempty_set() -> box_ParameterSet {
//         Box::new(ParameterSet::NonemptySet(NonemptySetAsParamSet::new()))
//     }
//     pub fn box_finite_set() -> box_ParameterSet {
//         Box::new(ParameterSet::FiniteSet(FiniteSetAsParamSet::new()))
//     }
//     pub fn box_obj(obj: box_Obj) -> box_ParameterSet {
//         Box::new(ParameterSet::Obj(obj))
//     }
// }


impl fmt::Display for ParameterSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParameterSet::Set(set) => write!(f, "{}", set.to_string()),
            ParameterSet::NonemptySet(nonempty_set) => write!(f, "{}", nonempty_set.to_string()),
            ParameterSet::FiniteSet(finite_set) => write!(f, "{}", finite_set.to_string()),
            ParameterSet::Obj(obj) => write!(f, "{}", obj),
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