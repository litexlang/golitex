use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone)]
pub struct ParamGroupWithSet {
    pub params: Vec<String>,
    pub set: Obj,
}

#[derive(Clone)]
pub struct ParamGroupWithParamType {
    pub params: Vec<String>,
    pub param_type: ParamType,
}

#[derive(Clone)]
pub struct ParamGroupWithStructFieldType {
    pub params: Vec<String>,
    pub struct_field_type: StructFieldType,
}

#[derive(Clone)]
pub enum StructFieldType {
    Obj(Obj),
    Set(Set),
    FiniteSet(FiniteSet),
    NonemptySet(NonemptySet),
    Family(FamilyParamType),
    /// 函数空间类型（仅出现在字段 / 参数类型位置，不由 `ParamType::Obj` 包装）。
    FnSet(FnSet),
    SetBuilder(SetBuilder),
}

impl StructFieldType {
    pub fn to_param_type(&self) -> ParamType {
        match self {
            StructFieldType::Obj(o) => ParamType::Obj(o.clone()),
            StructFieldType::Set(s) => ParamType::Set(s.clone()),
            StructFieldType::FiniteSet(f) => ParamType::FiniteSet(f.clone()),
            StructFieldType::NonemptySet(n) => ParamType::NonemptySet(n.clone()),
            StructFieldType::Family(f) => ParamType::Family(f.clone()),
            StructFieldType::FnSet(f) => ParamType::FnSet(f.clone()),
            StructFieldType::SetBuilder(s) => ParamType::SetBuilder(s.clone()),
        }
    }
}

impl fmt::Display for StructFieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_param_type())
    }
}

impl fmt::Display for ParamGroupWithStructFieldType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}",
            vec_to_string_join_by_comma(&self.params),
            self.struct_field_type
        )
    }
}

impl ParamGroupWithStructFieldType {
    pub fn new(params: Vec<String>, struct_field_type: StructFieldType) -> Self {
        ParamGroupWithStructFieldType {
            params,
            struct_field_type,
        }
    }

    pub fn number_of_params(defs: &Vec<ParamGroupWithStructFieldType>) -> usize {
        let mut total_param_count: usize = 0;
        for p in defs.iter() {
            total_param_count += p.params.len();
        }
        total_param_count
    }

    pub fn to_param_group_with_param_type(&self) -> ParamGroupWithParamType {
        ParamGroupWithParamType::new(self.params.clone(), self.struct_field_type.to_param_type())
    }

    pub fn to_param_groups_with_param_type(
        defs: &[ParamGroupWithStructFieldType],
    ) -> Vec<ParamGroupWithParamType> {
        defs.iter()
            .map(|d| d.to_param_group_with_param_type())
            .collect()
    }

    pub fn param_names(&self) -> &Vec<String> {
        &self.params
    }

    pub fn collect_param_names(param_defs: &Vec<ParamGroupWithStructFieldType>) -> Vec<String> {
        let mut names: Vec<String> = Vec::with_capacity(Self::number_of_params(param_defs));
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    pub fn param_defs_and_args_to_param_to_arg_map(
        param_defs: &Vec<ParamGroupWithStructFieldType>,
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

#[derive(Clone)]
pub enum ParamType {
    Set(Set),
    NonemptySet(NonemptySet),
    FiniteSet(FiniteSet),
    Obj(Obj),
    Family(FamilyParamType),
    Struct(StructParamType),
    /// 函数空间类型（仅出现在参数 / 字段类型位置）。
    FnSet(FnSet),
    /// 内涵集 `{x S : ...}`（仅出现在参数 / 字段类型位置）。
    SetBuilder(SetBuilder),
}

/// Instantiated family type: `family` name followed by argument objects (often sets).
#[derive(Clone)]
pub struct FamilyParamType {
    pub name: IdentifierOrIdentifierWithMod,
    pub params: Vec<Obj>,
}

/// Instantiated struct type: `struct` name followed by argument objects (field types / indices).
#[derive(Clone)]
pub struct StructParamType {
    pub name: IdentifierOrIdentifierWithMod,
    pub args: Vec<Obj>,
}

impl StructParamType {
    pub fn new(name: IdentifierOrIdentifierWithMod, args: Vec<Obj>) -> Self {
        StructParamType { name, args }
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
            ParamType::Family(family) => {
                write!(
                    f,
                    "{} {}({})",
                    FAMILY,
                    family.name,
                    vec_to_string_join_by_comma(&family.params)
                )
            }
            ParamType::Struct(struct_ty) => {
                write!(
                    f,
                    "{} {}({})",
                    STRUCT,
                    struct_ty.name,
                    vec_to_string_join_by_comma(&struct_ty.args)
                )
            }
            ParamType::FnSet(fn_set) => write!(f, "{}", fn_set),
            ParamType::SetBuilder(sb) => write!(f, "{}", sb),
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
            self.set
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

impl ParamType {
    pub fn get_all_param_names(param_def: &Vec<ParamGroupWithParamType>) -> Vec<String> {
        let mut names = vec![];
        for param_def in param_def.iter() {
            for name in param_def.params.iter() {
                names.push(name.clone());
            }
        }
        names
    }
}

impl ParamGroupWithParamType {
    pub fn new(params: Vec<String>, param_type: ParamType) -> Self {
        ParamGroupWithParamType { params, param_type }
    }

    pub fn number_of_params(defs: &Vec<ParamGroupWithParamType>) -> usize {
        let mut total_param_count: usize = 0;
        for p in defs.iter() {
            total_param_count += p.params.len();
        }
        return total_param_count;
    }

    pub fn flat_instantiated_types_for_args(
        param_defs: &Vec<ParamGroupWithParamType>,
        instantiated_types: &Vec<ParamType>,
    ) -> Vec<ParamType> {
        let mut result = Vec::with_capacity(Self::number_of_params(param_defs));
        for (param_def, param_type) in param_defs.iter().zip(instantiated_types.iter()) {
            for _ in param_def.params.iter() {
                result.push(param_type.clone());
            }
        }
        result
    }

    pub fn param_names(&self) -> &Vec<String> {
        &self.params
    }

    pub fn collect_param_names(param_defs: &Vec<ParamGroupWithParamType>) -> Vec<String> {
        let mut names: Vec<String> = Vec::with_capacity(Self::number_of_params(param_defs));
        for def in param_defs.iter() {
            for name in def.param_names().iter() {
                names.push(name.clone());
            }
        }
        names
    }

    pub fn param_def_params_to_arg_map(
        param_defs: &Vec<ParamGroupWithParamType>,
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
        param_defs: &Vec<ParamGroupWithParamType>,
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

impl ParamGroupWithSet {
    pub fn new(params: Vec<String>, set: Obj) -> Self {
        ParamGroupWithSet { params, set }
    }

    pub fn facts(&self) -> Vec<Fact> {
        let mut facts = Vec::with_capacity(self.params.len());
        for name in self.params.iter() {
            let fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(name.clone())),
                self.set.clone(),
                default_line_file(),
            )));
            facts.push(fact);
        }
        facts
    }

    // Example: given fn(x R, y Q), we want to verify x = 1, y = 2 can be used as argument to this function. This function returns the facts that 1 $in R, 2 $in Q.
    // 与 [`ParamGroupWithParamType`] 不同：此处每个参数必须属于**事先确定**的集合（不能用 `set` / `nonempty_set` / `finite_set` 等语法糖），且该集合不能依赖更早的参数。例如 `x R, y f(x)` 不允许。
    pub fn facts_for_args_satisfy_param_def_with_set_vec(
        runtime: &Runtime,
        param_defs: &Vec<ParamGroupWithSet>,
        args: &Vec<Obj>,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let instantiated_param_sets =
            runtime.inst_param_def_with_set_one_by_one(param_defs, args)?;
        let flat_param_sets =
            Self::flat_instantiated_param_sets_for_args(param_defs, &instantiated_param_sets);
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_set) in args.iter().zip(flat_param_sets.iter()) {
            facts.push(AtomicFact::InFact(InFact::new(
                arg.clone(),
                param_set.clone(),
                default_line_file(),
            )));
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
