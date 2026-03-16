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

impl ParamType {
    /// Builds the fact that an identifier with the given name satisfies this param type.
    pub fn param_satisfy_param_type_fact(param_name: &str, param_type: &ParamType) -> Fact {
        match param_type {
            ParamType::Obj(obj) => Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(param_name.to_string())),
                obj.clone(),
                None,
            ))),
            ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
                Obj::Identifier(Identifier::new(param_name.to_string())),
                None,
            ))),
            ParamType::NonemptySet(_) => Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                Obj::Identifier(Identifier::new(param_name.to_string())),
                None,
            ))),
            ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                Obj::Identifier(Identifier::new(param_name.to_string())),
                None,
            ))),
        }
    }

    /// Builds the fact that the given object satisfies this param type.
    pub fn fact_for_obj(obj: Obj, param_type: &ParamType) -> Fact {
        match param_type {
            ParamType::Obj(set_obj) => Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                obj,
                set_obj.clone(),
                None,
            ))),
            ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
                obj,
                None,
            ))),
            ParamType::NonemptySet(_) => Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                obj,
                None,
            ))),
            ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                obj,
                None,
            ))),
        }
    }
}

impl ParamDefWithParamType {
    pub fn _facts(&self) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.0.len());
        for name in self.0.iter() {
            let fact = ParamType::param_satisfy_param_type_fact(name, &self.1);
            facts.push(fact);
        }
        facts
    }

    pub fn number_of_params(defs: &Vec<ParamDefWithParamType>) -> usize {
        let mut total_param_count: usize = 0;
        for p in defs.iter() {
            total_param_count += p.0.len();
        }
        return total_param_count
    }
}

impl ParamDefWithParamSet {
    pub fn facts(&self) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.0.len());
        for name in self.0.iter() {
            let fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(name.clone())),
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

impl ParamDefWithParamType {
    pub fn facts_for_boxed_args_satisfy_param_def_with_type_vec(param_defs: &Vec<ParamDefWithParamType>, args: &Vec<Box<Obj>>) -> Result<Vec<Fact>, StmtError> {
        let instantiated_types = ParamDefWithParamType::instantiate_param_def_with_type_one_by_one_boxed(param_defs, args)?;
        let flat_types = ParamDefWithParamType::flat_instantiated_types_for_args(param_defs, &instantiated_types);
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let arg_obj = (**arg).clone();
            facts.push(ParamType::fact_for_obj(arg_obj, param_type));
        }
        Ok(facts)
    }

    pub fn facts_for_args_satisfy_param_def_with_type_vec(param_defs: &Vec<ParamDefWithParamType>, args: &Vec<Obj>) -> Result<Vec<Fact>, StmtError> {
        let args_vec: Vec<Box<Obj>> = args.iter().map(|arg| Box::new(arg.clone())).collect();
        Self::facts_for_boxed_args_satisfy_param_def_with_type_vec(param_defs, &args_vec)
    }

    
    fn number_of_params_in_param_def_with_type_def(param_defs: &Vec<ParamDefWithParamType>) -> usize {
        let mut total_param_count: usize = 0;
        for p in param_defs.iter() {
            total_param_count += p.0.len();
        }
        return total_param_count
    }

    pub fn flat_instantiated_types_for_args(param_defs: &Vec<ParamDefWithParamType>, instantiated_types: &Vec<ParamType>) -> Vec<ParamType> {
        let mut result = Vec::with_capacity(Self::number_of_params_in_param_def_with_type_def(param_defs));
        for (param_def, param_type) in param_defs.iter().zip(instantiated_types.iter()) {
            for _ in param_def.0.iter() {
                result.push(param_type.clone());
            }
        }
        result
    }

    
    fn instantiate_param_def_with_type_one_by_one(param_defs: &Vec<ParamDefWithParamType>, args: &Vec<Obj>) -> Result<Vec<ParamType>, StmtError> {
        let total_param_count = Self::number_of_params_in_param_def_with_type_def(param_defs);
        if total_param_count != args.len() {
            return Err(StmtError::ExecError(ExecError::new(
                format!(
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

    fn instantiate_param_def_with_type_one_by_one_boxed(param_defs: &Vec<ParamDefWithParamType>, args: &Vec<Box<Obj>>) -> Result<Vec<ParamType>, StmtError> {
        let args_as_obj: Vec<Obj> = args.iter().map(|b| (**b).clone()).collect();
        Self::instantiate_param_def_with_type_one_by_one(param_defs, &args_as_obj)
    }
}

impl ParamType {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ParamType {
        match &self {
            ParamType::Set(_) => self.clone(),
            ParamType::FiniteSet(_) => self.clone(),
            ParamType::NonemptySet(_) => self.clone(),
            ParamType::Obj(obj) => ParamType::Obj(obj.instantiate(param_to_arg_map))
        }
    }
}

impl ParamDefWithParamType {
    pub fn param_names(&self) -> &Vec<String> {
        &self.0
    }

    pub fn collect_param_names(param_defs: &Vec<ParamDefWithParamType>) -> Vec<String> {
        let mut names: Vec<String> = vec![];
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    /// Builds param_name -> Obj map from param_defs and args. Returns Some(map) if arg count matches
    /// total param count, else None.
    pub fn param_defs_and_args_to_param_to_arg_map(
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
    ) -> Option<HashMap<String, Obj>> {
        let param_names = Self::collect_param_names(param_defs);
        if param_names.len() != args.len() {
            return None;
        }
        let mut map = HashMap::new();
        for (param_name, arg) in param_names.iter().zip(args.iter()) {
            map.insert(param_name.clone(), arg.clone());
        }
        Some(map)
    }

    /// Builds param_name -> Obj map from param_defs and arg_map (param_name -> Vec<Obj>).
    /// Returns Some(map) if every param has exactly one Obj (or we take first from non-empty vec),
    /// and param count matches. Else None.
    pub fn param_def_params_to_arg_map(
        param_defs: &Vec<ParamDefWithParamType>,
        arg_map: &HashMap<String, Vec<Obj>>,
    ) -> Option<HashMap<String, Obj>> {
        let param_names = Self::collect_param_names(param_defs);
        let mut result = HashMap::new();
        for param_name in param_names.iter() {
            let objs_option = arg_map.get(param_name);
            let objs = match objs_option {
                Some(v) => v,
                None => return None,
            };
            let first_obj = objs.first();
            let obj = match first_obj {
                Some(o) => o.clone(),
                None => return None,
            };
            result.insert(param_name.clone(), obj);
        }
        Some(result)
    }
}

impl ParamDefWithParamSet {
    pub fn param_names(&self) -> &Vec<String> {
        &self.0
    }

    pub fn collect_param_names(param_defs: &Vec<ParamDefWithParamSet>) -> Vec<String> {
        let mut names: Vec<String> = vec![];
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

}

