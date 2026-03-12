use std::fmt;
use std::collections::HashMap;
use crate::error::{ExecError, StmtError};
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

pub fn instantiate_param_def_with_type_one_by_one(param_defs: &Vec<ParamDefWithParamType>, args: &Vec<Obj>) -> Result<Vec<ParamType>, StmtError> {
    let mut total_param_count: usize = 0;
    for p in param_defs.iter() {
        total_param_count += p.0.len();
    }
    if total_param_count != args.len() {
        return Err(StmtError::ExecError(ExecError::new(
            &format!(
                "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                total_param_count,
                args.len()
            ),
            vec![],
            None,
        )));
    }

    let mut param_arg_map: HashMap<String, Obj> = HashMap::new();
    let mut arg_index: usize = 0;
    let mut new_types: Vec<ParamType> = vec![];
    for param_def in param_defs.iter() {
        let new_type =  if arg_index != 0 {
            param_def.1.instantiate(&param_arg_map)
        } else {
            param_def.1.clone()
        };
        new_types.push(new_type);
        
        for param_name in param_def.0.iter() {
            param_arg_map.insert(param_name.clone(), args[arg_index].clone());
            arg_index += 1;
        }
    }
    
    Ok(new_types)
}

impl ParamType {
    fn instantiate(&self, param_arg_map: &HashMap<String, Obj>) -> ParamType {
        panic!("")
    }
}