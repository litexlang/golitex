use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone)]
pub enum ParamType {
    Set(Set),
    NonemptySet(NonemptySet),
    FiniteSet(FiniteSet),
    Obj(Obj),
}

/// Full parameter list with types, e.g. `a, b T, c E` as a sequence of [`ParamGroupWithParamType`].
#[derive(Clone)]
pub struct ParamDefWithType {
    pub groups: Vec<ParamGroupWithParamType>,
}

impl ParamDefWithType {
    pub fn new(groups: Vec<ParamGroupWithParamType>) -> Self {
        ParamDefWithType { groups }
    }

    pub fn len(&self) -> usize {
        self.groups.len()
    }

    pub fn is_empty(&self) -> bool {
        self.groups.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, ParamGroupWithParamType> {
        self.groups.iter()
    }

    pub fn as_slice(&self) -> &[ParamGroupWithParamType] {
        self.groups.as_slice()
    }

    pub fn number_of_params(&self) -> usize {
        let mut total_param_count: usize = 0;
        for p in self.groups.iter() {
            total_param_count += p.params.len();
        }
        total_param_count
    }

    pub fn collect_param_names(&self) -> Vec<String> {
        let mut names: Vec<String> = Vec::with_capacity(self.number_of_params());
        for def in self.groups.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    pub fn collect_param_names_with_types(&self) -> Vec<(String, ParamType)> {
        let mut out: Vec<(String, ParamType)> = Vec::with_capacity(self.number_of_params());
        for def in self.groups.iter() {
            for name in def.param_names().iter() {
                out.push((name.clone(), def.param_type.clone()));
            }
        }
        out
    }

    pub fn flat_instantiated_types_for_args(
        &self,
        instantiated_types: &[ParamType],
    ) -> Vec<ParamType> {
        if instantiated_types.len() == self.number_of_params() {
            return instantiated_types.to_vec();
        }

        let mut result = Vec::with_capacity(self.number_of_params());
        for (param_def, param_type) in self.groups.iter().zip(instantiated_types.iter()) {
            for _ in param_def.params.iter() {
                result.push(param_type.clone());
            }
        }
        result
    }

    pub fn param_def_params_to_arg_map(
        &self,
        arg_map: &HashMap<String, Obj>,
    ) -> Option<HashMap<String, Obj>> {
        let param_names = self.collect_param_names();
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

    pub fn param_defs_and_args_to_param_to_arg_map(&self, args: &[Obj]) -> HashMap<String, Obj> {
        let param_names = self.collect_param_names();
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

    pub fn param_defs_and_boxed_args_to_param_to_arg_map(
        &self,
        args: &[Box<Obj>],
    ) -> HashMap<String, Obj> {
        let param_names = self.collect_param_names();
        if param_names.len() != args.len() {
            unreachable!();
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        let mut index = 0;
        while index < param_names.len() {
            let param_name = &param_names[index];
            let arg = &args[index];
            result.insert(param_name.clone(), (**arg).clone());
            index += 1;
        }
        result
    }
}

impl fmt::Display for ParamDefWithType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_join_by_comma(&self.groups))
    }
}

impl From<Vec<ParamGroupWithParamType>> for ParamDefWithType {
    fn from(groups: Vec<ParamGroupWithParamType>) -> Self {
        ParamDefWithType::new(groups)
    }
}

#[derive(Clone)]
pub struct ParamGroupWithSet {
    pub params: Vec<String>,
    pub param_type: Box<Obj>,
}

#[derive(Clone)]
pub struct ParamGroupWithParamType {
    pub params: Vec<String>,
    pub param_type: ParamType,
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

impl fmt::Display for ParamGroupWithSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}",
            comma_separated_stored_fn_params_as_user_source(&self.params),
            self.param_type
        )
    }
}

impl fmt::Display for ParamGroupWithParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}",
            vec_to_string_join_by_comma(&self.params),
            self.param_type
        )
    }
}

impl ParamGroupWithParamType {
    pub fn new(params: Vec<String>, param_type: ParamType) -> Self {
        ParamGroupWithParamType { params, param_type }
    }

    pub fn param_names(&self) -> &Vec<String> {
        &self.params
    }
}

impl ParamGroupWithSet {
    pub fn new(params: Vec<String>, set: Obj) -> Self {
        ParamGroupWithSet {
            params,
            param_type: Box::new(set),
        }
    }

    pub fn set_obj(&self) -> &Obj {
        self.param_type.as_ref()
    }

    /// Membership facts for parameters; element tagging must match [`define_params_with_set_in_scope`]'s `binding_scope` (e.g. `FnSet` ~5 for `fn` and `'` anonymous heads).
    pub fn facts_for_binding_scope(&self, binding_scope: ParamObjType) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.params.len());
        for name in self.params.iter() {
            let fact = InFact::new(
                obj_for_bound_param_in_scope(name.clone(), binding_scope),
                self.set_obj().clone(),
                default_line_file(),
            )
            .into();
            facts.push(fact);
        }
        facts
    }

    pub fn facts(&self) -> Vec<Fact> {
        self.facts_for_binding_scope(ParamObjType::FnSet)
    }

    // Example: given fn(x R, y Q), we want to verify x = 1, y = 2 can be used as argument to this function. This function returns the facts that 1 $in R, 2 $in Q.
    // 与 [`ParamGroupWithParamType`] 不同：此处每个参数必须属于**事先确定**的集合（不能用 `set` / `nonempty_set` / `finite_set` 等语法糖），且该集合不能依赖更早的参数。例如 `x R, y f(x)` 不允许。
    pub fn facts_for_args_satisfy_param_def_with_set_vec(
        runtime: &Runtime,
        param_defs: &Vec<ParamGroupWithSet>,
        args: &Vec<Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let instantiated_param_sets =
            runtime.inst_param_def_with_set_one_by_one(param_defs, args, param_obj_type)?;
        let flat_param_sets =
            Self::flat_instantiated_param_sets_for_args(param_defs, &instantiated_param_sets);
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_set) in args.iter().zip(flat_param_sets.iter()) {
            facts.push(InFact::new(arg.clone(), param_set.clone(), default_line_file()).into());
        }
        Ok(facts)
    }

    fn flat_instantiated_param_sets_for_args(
        param_defs: &Vec<ParamGroupWithSet>,
        instantiated_param_sets: &Vec<Obj>,
    ) -> Vec<Obj> {
        let mut result = Vec::with_capacity(Self::number_of_params(param_defs));
        for (param_def, param_set) in param_defs.iter().zip(instantiated_param_sets.iter()) {
            for _ in param_def.params.iter() {
                result.push(param_set.clone());
            }
        }
        result
    }

    pub fn param_names(&self) -> &Vec<String> {
        &self.params
    }

    pub fn collect_param_names(param_defs: &Vec<ParamGroupWithSet>) -> Vec<String> {
        let mut names: Vec<String> = Vec::with_capacity(Self::number_of_params(param_defs));
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    pub fn number_of_params(param_defs: &Vec<ParamGroupWithSet>) -> usize {
        let mut total_param_count: usize = 0;
        for p in param_defs.iter() {
            total_param_count += p.params.len();
        }
        return total_param_count;
    }

    pub fn param_defs_and_args_to_param_to_arg_map(
        param_defs: &Vec<ParamGroupWithSet>,
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
