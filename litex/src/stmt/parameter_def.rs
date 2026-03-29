use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

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
    pub fn get_all_param_names(param_def: &Vec<ParamDefWithParamType>) -> Vec<String> {
        let mut names = vec![];
        for param_def in param_def.iter() {
            for name in param_def.0.iter() {
                names.push(name.clone());
            }
        }
        names
    }

    /// Builds the fact that an identifier with the given name satisfies this param type.
    pub fn param_satisfy_param_type_fact(param_name: &str, param_type: &ParamType) -> Fact {
        match param_type {
            ParamType::Obj(obj) => Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(param_name.to_string())),
                obj.clone(),
                DEFAULT_LINE_FILE.clone(),
            ))),
            ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
                Obj::Identifier(Identifier::new(param_name.to_string())),
                DEFAULT_LINE_FILE.clone(),
            ))),
            ParamType::NonemptySet(_) => {
                Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                    Obj::Identifier(Identifier::new(param_name.to_string())),
                    DEFAULT_LINE_FILE.clone(),
                )))
            }
            ParamType::FiniteSet(_) => {
                Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                    Obj::Identifier(Identifier::new(param_name.to_string())),
                    DEFAULT_LINE_FILE.clone(),
                )))
            }
        }
    }

    /// Builds the fact that the given object satisfies this param type.
    pub fn fact_for_obj(obj: Obj, param_type: &ParamType) -> AtomicFact {
        match param_type {
            ParamType::Obj(set_obj) => {
                AtomicFact::InFact(InFact::new(obj, set_obj.clone(), DEFAULT_LINE_FILE.clone()))
            }
            ParamType::Set(_) => {
                AtomicFact::IsSetFact(IsSetFact::new(obj, DEFAULT_LINE_FILE.clone()))
            }
            ParamType::NonemptySet(_) => AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                obj,
                DEFAULT_LINE_FILE.clone(),
            )),
            ParamType::FiniteSet(_) => {
                AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(obj, DEFAULT_LINE_FILE.clone()))
            }
        }
    }
}

impl ParamDefWithParamType {
    pub fn number_of_params(defs: &Vec<ParamDefWithParamType>) -> usize {
        let mut total_param_count: usize = 0;
        for p in defs.iter() {
            total_param_count += p.0.len();
        }
        return total_param_count;
    }
}

impl ParamDefWithParamSet {
    pub fn facts(&self) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.0.len());
        for name in self.0.iter() {
            let fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(name.clone())),
                self.1.clone(),
                DEFAULT_LINE_FILE.clone(),
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

    pub fn fact_for_obj(obj: Obj, param_set: &Obj) -> AtomicFact {
        AtomicFact::InFact(InFact::new(
            obj,
            param_set.clone(),
            DEFAULT_LINE_FILE.clone(),
        ))
    }

    // Example: given fn(x R, y Q), we want to verify x = 1, y = 2 can be used as argument to this function. This function returns the facts that 1 $in R, 2 $in Q.
    // Unlike facts_for_args_satisfy_param_def_with_type_vec, this function requires each later parameter to belong to a concrete, fixed set (not syntactic sugar like set/nonempty_set/finite_set), and that set must not depend on earlier parameters. For example, in a ParamSet definition, `x R, y f(x)` is not allowed: mathematically, y's set membership must be specified in advance, rather than chosen only after x is determined.
    pub fn facts_for_args_satisfy_param_def_with_set_vec(
        param_defs: &Vec<ParamDefWithParamSet>,
        args: &Vec<Obj>,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let instantiated_param_sets =
            Self::instantiate_param_def_with_set_one_by_one(param_defs, args)?;
        let flat_param_sets =
            Self::flat_instantiated_param_sets_for_args(param_defs, &instantiated_param_sets);
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_set) in args.iter().zip(flat_param_sets.iter()) {
            facts.push(Self::fact_for_obj(arg.clone(), param_set));
        }
        Ok(facts)
    }

    fn number_of_params_in_param_def_with_set_def(param_defs: &Vec<ParamDefWithParamSet>) -> usize {
        let mut total_param_count: usize = 0;
        for param_def in param_defs.iter() {
            total_param_count += param_def.0.len();
        }
        total_param_count
    }

    fn flat_instantiated_param_sets_for_args(
        param_defs: &Vec<ParamDefWithParamSet>,
        instantiated_param_sets: &Vec<Obj>,
    ) -> Vec<Obj> {
        let mut result =
            Vec::with_capacity(Self::number_of_params_in_param_def_with_set_def(param_defs));
        for (param_def, param_set) in param_defs.iter().zip(instantiated_param_sets.iter()) {
            for _ in param_def.0.iter() {
                result.push(param_set.clone());
            }
        }
        result
    }

    fn instantiate_param_def_with_set_one_by_one(
        param_defs: &Vec<ParamDefWithParamSet>,
        args: &Vec<Obj>,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let total_param_count = Self::number_of_params_in_param_def_with_set_def(param_defs);
        if total_param_count != args.len() {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                DEFAULT_LINE_FILE.clone(),
                None,
            )));
        }

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut instantiated_param_sets: Vec<Obj> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            let instantiated_param_set = if arg_index != 0 {
                param_def.1.instantiate(&param_to_arg_map)
            } else {
                param_def.1.clone()
            };
            instantiated_param_sets.push(instantiated_param_set);

            for param_name in param_def.0.iter() {
                param_to_arg_map.insert(param_name.clone(), args[arg_index].clone());
                arg_index += 1;
            }
        }

        Ok(instantiated_param_sets)
    }
}

impl ParamDefWithParamType {
    // Example: given forall x, y R, z f(x, y), s set. We want to verify when "x" = obj1, "y" = obj2, "z" = obj3, "s" = obj4, they satisfy definition requirement or not. This function returns the facts that obj1 $in R, obj2 $in R, obj3 = f(obj1, obj2), obj4 $in set.
    pub fn boxed_args_satisfy_param_def_facts(
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Box<Obj>>,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let instantiated_types =
            ParamDefWithParamType::instantiate_param_def_with_type_one_by_one_boxed(
                param_defs, args,
            )?;
        let flat_types = ParamDefWithParamType::flat_instantiated_types_for_args(
            param_defs,
            &instantiated_types,
        );
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let arg_obj = (**arg).clone();
            facts.push(ParamType::fact_for_obj(arg_obj, param_type));
        }
        Ok(facts)
    }

    pub fn facts_for_args_satisfy_param_def_with_type_vec(
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let instantiated_types =
            ParamDefWithParamType::instantiate_param_def_with_type_one_by_one(param_defs, args)?;
        let flat_types = ParamDefWithParamType::flat_instantiated_types_for_args(
            param_defs,
            &instantiated_types,
        );
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            facts.push(ParamType::fact_for_obj(arg.clone(), param_type));
        }
        Ok(facts)
    }

    fn number_of_params_in_param_def_with_type_def(
        param_defs: &Vec<ParamDefWithParamType>,
    ) -> usize {
        let mut total_param_count: usize = 0;
        for p in param_defs.iter() {
            total_param_count += p.0.len();
        }
        return total_param_count;
    }

    pub fn flat_instantiated_types_for_args(
        param_defs: &Vec<ParamDefWithParamType>,
        instantiated_types: &Vec<ParamType>,
    ) -> Vec<ParamType> {
        let mut result = Vec::with_capacity(Self::number_of_params_in_param_def_with_type_def(
            param_defs,
        ));
        for (param_def, param_type) in param_defs.iter().zip(instantiated_types.iter()) {
            for _ in param_def.0.iter() {
                result.push(param_type.clone());
            }
        }
        result
    }

    fn instantiate_param_def_with_type_one_by_one(
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
    ) -> Result<Vec<ParamType>, RuntimeError> {
        let total_param_count = Self::number_of_params_in_param_def_with_type_def(param_defs);
        if total_param_count != args.len() {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                DEFAULT_LINE_FILE.clone(),
                None,
            )));
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut new_types: Vec<ParamType> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            let new_type = if arg_index != 0 {
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

    fn instantiate_param_def_with_type_one_by_one_boxed(
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Box<Obj>>,
    ) -> Result<Vec<ParamType>, RuntimeError> {
        let total_param_count = Self::number_of_params_in_param_def_with_type_def(param_defs);
        if total_param_count != args.len() {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "argument count mismatch: expected {} parameter(s), got {} argument(s)",
                    total_param_count,
                    args.len()
                ),
                DEFAULT_LINE_FILE.clone(),
                None,
            )));
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::with_capacity(total_param_count);
        let mut arg_index: usize = 0;
        let mut new_types: Vec<ParamType> = Vec::with_capacity(param_defs.len());
        for param_def in param_defs.iter() {
            let new_type = if arg_index != 0 {
                param_def.1.instantiate(&param_arg_map)
            } else {
                param_def.1.clone()
            };
            new_types.push(new_type);

            for param_name in param_def.0.iter() {
                let arg_obj = match args.get(arg_index) {
                    Some(boxed_arg) => (**boxed_arg).clone(),
                    None => {
                        return Err(RuntimeError::UnknownError(UnknownError::new(
                            "internal error: argument index out of range for boxed args"
                                .to_string(),
                            DEFAULT_LINE_FILE.clone(),
                            None,
                        )));
                    }
                };
                param_arg_map.insert(param_name.clone(), arg_obj);
                arg_index += 1;
            }
        }

        Ok(new_types)
    }
}

impl ParamType {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ParamType {
        match &self {
            ParamType::Set(_) => self.clone(),
            ParamType::FiniteSet(_) => self.clone(),
            ParamType::NonemptySet(_) => self.clone(),
            ParamType::Obj(obj) => ParamType::Obj(obj.instantiate(param_to_arg_map)),
        }
    }
}

impl ParamDefWithParamType {
    pub fn param_names(&self) -> &Vec<String> {
        &self.0
    }

    pub fn collect_param_names(param_defs: &Vec<ParamDefWithParamType>) -> Vec<String> {
        let mut names: Vec<String> = Vec::with_capacity(
            Self::number_of_params_in_param_def_with_type_def(param_defs),
        );
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    pub fn param_def_params_to_arg_map(
        param_defs: &Vec<ParamDefWithParamType>,
        arg_map: &HashMap<String, Obj>,
    ) -> Option<HashMap<String, Obj>> {
        let param_names = Self::collect_param_names(param_defs);
        let mut result = HashMap::new();
        for param_name in param_names.iter() {
            let objs_option = arg_map.get(param_name);
            let objs = match objs_option {
                Some(v) => v,
                None => return None,
            };
            result.insert(param_name.clone(), objs.clone());
        }
        Some(result)
    }

    pub fn param_defs_and_args_to_param_to_arg_map(
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
    ) -> HashMap<String, Obj> {
        let param_names = Self::collect_param_names(param_defs);
        if param_names.len() != args.len() {
            unreachable!();
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        let mut index = 0;
        while index < param_names.len() {
            let param_name = &param_names[index];
            let arg = &args[index];
            result.insert(param_name.clone(), arg.clone());
            index += 1;
        }
        result
    }
}

impl ParamDefWithParamSet {
    pub fn param_names(&self) -> &Vec<String> {
        &self.0
    }

    pub fn collect_param_names(param_defs: &Vec<ParamDefWithParamSet>) -> Vec<String> {
        let mut names: Vec<String> = Vec::with_capacity(Self::number_of_params(param_defs));
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    pub fn number_of_params(param_defs: &Vec<ParamDefWithParamSet>) -> usize {
        let mut total_param_count: usize = 0;
        for p in param_defs.iter() {
            total_param_count += p.0.len();
        }
        return total_param_count;
    }

    pub fn param_defs_and_args_to_param_to_arg_map(
        param_defs: &Vec<ParamDefWithParamSet>,
        args: &Vec<Obj>,
    ) -> HashMap<String, Obj> {
        let param_names = Self::collect_param_names(param_defs);
        if param_names.len() != args.len() {
            unreachable!();
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        let mut index = 0;
        while index < param_names.len() {
            let param_name = &param_names[index];
            let arg = &args[index];
            result.insert(param_name.clone(), arg.clone());
            index += 1;
        }
        result
    }
}
