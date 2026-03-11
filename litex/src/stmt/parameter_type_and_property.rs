use std::fmt;
use crate::fact::{AtomicFact, Fact, InFact, IsSetFact, IsNonemptySetFact, IsFiniteSetFact};
use crate::common::helper::vec_to_string_join_by_comma;
use crate::obj::{Identifier, Obj};
use crate::common::keywords::{FINITE_SET, NONEMPTY_SET, SET};

/// 参数名列表（长度 1 表示单参数）与对应的 Obj（set）
#[derive(Clone)]
pub struct ParamDefWithParamSet(pub Vec<String>, pub Obj);

/// 参数名列表（长度 1 表示单参数）与对应的 ParamType
#[derive(Clone)]
pub struct ParamDefWithParamType(pub Vec<String>, pub ParamType);

#[derive(Clone)]
pub enum ParamType {
    Set(Set),
    NonemptySet(NonemptySet),
    FiniteSet(FiniteSet),
    Obj(Obj),
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
        }
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
        write!(f, "{} {}", vec_to_string_join_by_comma(&self.0), self.1)
    }
}

impl fmt::Display for ParamDefWithParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", vec_to_string_join_by_comma(&self.0), self.1)
    }
}

impl ParamDefWithParamType {
    pub fn facts(&self) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.0.len());
        for name in self.0.iter() {
            let fact = match &self.1 {
                ParamType::Obj(obj) => Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    Obj::Identifier(Identifier::new(name)),
                    obj.clone(),
                    None,
                ))),
                ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
                    Obj::Identifier(Identifier::new(name)),
                    None,
                ))),
                ParamType::NonemptySet(_) => Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                    Obj::Identifier(Identifier::new(name)),
                    None,
                ))),
                ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                    Obj::Identifier(Identifier::new(name)),
                    None,
                ))),
            };
            facts.push(fact);
        }
        facts
    }
}

impl ParamDefWithParamSet {
    pub fn facts(&self) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.0.len());
        for name in self.0.iter() {
            let fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(name)),
                self.1.clone(),
                None,
            )));
            facts.push(fact);
        }
        facts
    }
}

impl ParamDefWithParamSet {
    pub fn new(param: Vec<String>, param_set: Obj) -> Self {
        ParamDefWithParamSet(param, param_set)
    }
}