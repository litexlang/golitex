use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;

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
    /// For each parameter group, the flat indices of earlier parameters cited by that group's type.
    pub param_type_cited_param_indices: Vec<Vec<usize>>,
}

impl ParamDefWithType {
    pub fn new(groups: Vec<ParamGroupWithParamType>) -> Self {
        let param_type_cited_param_indices = cited_param_indices_for_param_type_groups(&groups);
        ParamDefWithType {
            groups,
            param_type_cited_param_indices,
        }
    }

    pub fn store_reason() -> &'static str {
        "parameter definition"
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", vec_to_string_join_by_comma(&self.groups))
    }
}

impl From<Vec<ParamGroupWithParamType>> for ParamDefWithType {
    fn from(groups: Vec<ParamGroupWithParamType>) -> Self {
        ParamDefWithType::new(groups)
    }
}

/// Full function parameter list with set-valued parameter domains.
#[derive(Clone)]
pub struct ParamDefWithSet {
    pub groups: Vec<ParamGroupWithSet>,
    /// For each parameter group, the flat indices of earlier parameters cited by that group's set.
    ///
    /// Later parameter sets may depend on earlier arguments, e.g.
    /// `fn(n N_pos, x closed_range(1, n)) R`; function return sets are intentionally outside this
    /// dependent parameter list and must not cite these parameters.
    pub param_set_cited_param_indices: Vec<Vec<usize>>,
}

impl ParamDefWithSet {
    pub fn new(groups: Vec<ParamGroupWithSet>) -> Self {
        let param_set_cited_param_indices = cited_param_indices_for_param_set_groups(&groups);
        ParamDefWithSet {
            groups,
            param_set_cited_param_indices,
        }
    }

    pub fn len(&self) -> usize {
        self.groups.len()
    }

    pub fn is_empty(&self) -> bool {
        self.groups.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, ParamGroupWithSet> {
        self.groups.iter()
    }

    pub fn as_slice(&self) -> &[ParamGroupWithSet] {
        self.groups.as_slice()
    }

    pub fn number_of_params(&self) -> usize {
        ParamGroupWithSet::number_of_params(&self.groups)
    }

    pub fn collect_param_names(&self) -> Vec<String> {
        ParamGroupWithSet::collect_param_names(&self.groups)
    }

    pub fn param_defs_and_args_to_param_to_arg_map(&self, args: &Vec<Obj>) -> HashMap<String, Obj> {
        ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(&self.groups, args)
    }

    pub fn flat_instantiated_param_sets_for_args(
        &self,
        instantiated_param_sets: &Vec<Obj>,
    ) -> Vec<Obj> {
        let mut result = Vec::with_capacity(self.number_of_params());
        for (param_def, param_set) in self.groups.iter().zip(instantiated_param_sets.iter()) {
            for _ in param_def.params.iter() {
                result.push(param_set.clone());
            }
        }
        result
    }

    pub fn cited_param_indices_in_obj_from_params(&self, obj: &Obj) -> Vec<usize> {
        let mut param_indices: HashMap<String, usize> = HashMap::new();
        let mut flat_index = 0;
        for group in self.groups.iter() {
            for param_name in group.params.iter() {
                param_indices.insert(param_name.clone(), flat_index);
                flat_index += 1;
            }
        }
        cited_param_indices_in_obj(obj, &param_indices)
    }

    pub fn has_dependent_param_set(&self) -> bool {
        self.param_set_cited_param_indices
            .iter()
            .any(|indices| !indices.is_empty())
    }

    pub fn validate_obj_does_not_cite_params(
        &self,
        obj: &Obj,
        context: &str,
    ) -> Result<(), RuntimeError> {
        let cited_indices = self.cited_param_indices_in_obj_from_params(obj);
        if cited_indices.is_empty() {
            return Ok(());
        }

        let names = self.collect_param_names();
        let cited_names: Vec<String> = cited_indices
            .iter()
            .filter_map(|index| names.get(*index).cloned())
            .collect();
        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "{} cannot depend on function parameters [{}]",
                context,
                cited_names.join(", ")
            )),
        )))
    }
}

impl Deref for ParamDefWithSet {
    type Target = Vec<ParamGroupWithSet>;

    fn deref(&self) -> &Self::Target {
        &self.groups
    }
}

impl IntoIterator for ParamDefWithSet {
    type Item = ParamGroupWithSet;
    type IntoIter = std::vec::IntoIter<ParamGroupWithSet>;

    fn into_iter(self) -> Self::IntoIter {
        self.groups.into_iter()
    }
}

impl From<Vec<ParamGroupWithSet>> for ParamDefWithSet {
    fn from(groups: Vec<ParamGroupWithSet>) -> Self {
        ParamDefWithSet::new(groups)
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ParamType::Set(set) => write!(f, "{}", set.to_string()),
            ParamType::NonemptySet(nonempty_set) => write!(f, "{}", nonempty_set.to_string()),
            ParamType::FiniteSet(finite_set) => write!(f, "{}", finite_set.to_string()),
            ParamType::Obj(obj) => write!(f, "{}", obj),
        }
    }
}

impl fmt::Display for Set {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", SET)
    }
}

impl fmt::Display for NonemptySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", NONEMPTY_SET)
    }
}

impl fmt::Display for FiniteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", FINITE_SET)
    }
}

impl fmt::Display for ParamGroupWithSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}",
            comma_separated_stored_fn_params_as_user_source(&self.params),
            self.param_type
        )
    }
}

impl fmt::Display for ParamGroupWithParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

    // Example: given fn(x R, y Q(x)), we want to verify x = 1, y = 2 can be used as argument to this function. This function returns the facts that 1 $in R, 2 $in Q(1).
    pub fn facts_for_args_satisfy_param_def_with_set_vec(
        runtime: &Runtime,
        param_defs: &ParamDefWithSet,
        args: &Vec<Obj>,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let instantiated_param_sets =
            runtime.inst_param_def_with_set_one_by_one(param_defs, args, param_obj_type)?;
        let flat_param_sets =
            param_defs.flat_instantiated_param_sets_for_args(&instantiated_param_sets);
        let mut facts = Vec::with_capacity(args.len());
        for (arg, param_set) in args.iter().zip(flat_param_sets.iter()) {
            facts.push(InFact::new(arg.clone(), param_set.clone(), default_line_file()).into());
        }
        Ok(facts)
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

fn cited_param_indices_for_param_type_groups(
    groups: &[ParamGroupWithParamType],
) -> Vec<Vec<usize>> {
    let mut previous_param_indices: HashMap<String, usize> = HashMap::new();
    let mut result = Vec::with_capacity(groups.len());
    let mut flat_index: usize = 0;
    for group in groups.iter() {
        result.push(cited_param_indices_in_param_type(
            &group.param_type,
            &previous_param_indices,
        ));
        for param_name in group.params.iter() {
            previous_param_indices.insert(param_name.clone(), flat_index);
            flat_index += 1;
        }
    }
    result
}

fn cited_param_indices_for_param_set_groups(groups: &[ParamGroupWithSet]) -> Vec<Vec<usize>> {
    let mut previous_param_indices: HashMap<String, usize> = HashMap::new();
    let mut result = Vec::with_capacity(groups.len());
    let mut flat_index: usize = 0;
    for group in groups.iter() {
        result.push(cited_param_indices_in_obj(
            group.set_obj(),
            &previous_param_indices,
        ));
        for param_name in group.params.iter() {
            previous_param_indices.insert(param_name.clone(), flat_index);
            flat_index += 1;
        }
    }
    result
}

fn cited_param_indices_in_param_type(
    param_type: &ParamType,
    previous_param_indices: &HashMap<String, usize>,
) -> Vec<usize> {
    match param_type {
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => Vec::new(),
        ParamType::Obj(obj) => cited_param_indices_in_obj(obj, previous_param_indices),
    }
}

fn cited_param_indices_in_obj(
    obj: &Obj,
    previous_param_indices: &HashMap<String, usize>,
) -> Vec<usize> {
    let mut result = Vec::new();
    let mut shadowed_names = Vec::new();
    collect_cited_param_indices_from_obj(
        obj,
        previous_param_indices,
        &mut shadowed_names,
        &mut result,
    );
    result
}

fn collect_cited_param_indices_from_obj(
    obj: &Obj,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    match obj {
        Obj::Atom(atom) => {
            collect_cited_param_indices_from_atom(atom, previous_param_indices, shadowed_names, out)
        }
        Obj::FnObj(fn_obj) => {
            collect_cited_param_indices_from_fn_head(
                &fn_obj.head,
                previous_param_indices,
                shadowed_names,
                out,
            );
            for group in fn_obj.body.iter() {
                for arg in group.iter() {
                    collect_cited_param_indices_from_obj(
                        arg,
                        previous_param_indices,
                        shadowed_names,
                        out,
                    );
                }
            }
        }
        Obj::Number(_) | Obj::StandardSet(_) => {}
        Obj::Add(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Sub(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Mul(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Div(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Mod(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::IntegerQuotient(x) => collect_cited_param_indices_from_two_objs(
            &x.dividend,
            &x.divisor,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Pow(x) => collect_cited_param_indices_from_two_objs(
            &x.base,
            &x.exponent,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Abs(x) => collect_cited_param_indices_from_obj(
            &x.arg,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Sqrt(x) => collect_cited_param_indices_from_obj(
            &x.arg,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Log(x) => collect_cited_param_indices_from_two_objs(
            &x.base,
            &x.arg,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Union(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Intersect(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::SetMinus(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::SetDiff(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::BigUnion(x) => collect_cited_param_indices_from_obj(
            &x.left,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::BigIntersect(x) => collect_cited_param_indices_from_obj(
            &x.left,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::PowerSet(x) => collect_cited_param_indices_from_obj(
            &x.set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::ListSet(x) => {
            for item in x.list.iter() {
                collect_cited_param_indices_from_obj(
                    item,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
        Obj::SetBuilder(x) => {
            collect_cited_param_indices_from_obj(
                &x.param_set,
                previous_param_indices,
                shadowed_names,
                out,
            );
            shadowed_names.push(x.param.clone());
            for fact in x.facts.iter() {
                collect_cited_param_indices_from_exist_body_fact(
                    fact,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
            shadowed_names.pop();
        }
        Obj::GeneralCart(x) => {
            collect_cited_param_indices_from_obj(
                &x.index_set,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.family_set,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.family_fn,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::FnSet(x) => collect_cited_param_indices_from_fn_set_body(
            &x.body,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::AnonymousFn(x) => {
            collect_cited_param_indices_from_fn_set_body(
                &x.body,
                previous_param_indices,
                shadowed_names,
                out,
            );
            let added = push_param_names_to_shadow(&x.body.params_def_with_set, shadowed_names);
            collect_cited_param_indices_from_obj(
                &x.equal_to,
                previous_param_indices,
                shadowed_names,
                out,
            );
            pop_shadowed_names(shadowed_names, added);
        }
        Obj::Cart(x) => {
            for arg in x.args.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
        Obj::CartDim(x) => collect_cited_param_indices_from_obj(
            &x.set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Proj(x) => collect_cited_param_indices_from_two_objs(
            &x.set,
            &x.dim,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::TupleDim(x) => collect_cited_param_indices_from_obj(
            &x.arg,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Tuple(x) => {
            for arg in x.args.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
        Obj::FiniteSetSize(x) => collect_cited_param_indices_from_obj(
            &x.set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::FiniteSetMax(x) => collect_cited_param_indices_from_obj(
            &x.set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::FiniteSetMin(x) => collect_cited_param_indices_from_obj(
            &x.set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::FnRange(x) => collect_cited_param_indices_from_obj(
            &x.function,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Replacement(x) => collect_cited_param_indices_from_obj(
            &x.source_set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::Sum(x) => {
            collect_cited_param_indices_from_obj(
                &x.start,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.end,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.func,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::SumOfFiniteSet(x) => {
            collect_cited_param_indices_from_obj(
                &x.set,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.func,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::ProductOfFiniteSet(x) => {
            collect_cited_param_indices_from_obj(
                &x.set,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.func,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::Product(x) => {
            collect_cited_param_indices_from_obj(
                &x.start,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.end,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.func,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::Range(x) => collect_cited_param_indices_from_two_objs(
            &x.start,
            &x.end,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::ClosedRange(x) => collect_cited_param_indices_from_two_objs(
            &x.start,
            &x.end,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::IntervalObj(x) => collect_cited_param_indices_from_two_objs(
            x.interval_struct().start.as_ref(),
            x.interval_struct().end.as_ref(),
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::OneSideInfinityIntervalObj(x) => collect_cited_param_indices_from_obj(
            x.interval_struct().start.as_ref(),
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::FiniteSeqSet(x) => collect_cited_param_indices_from_two_objs(
            &x.set,
            &x.n,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::SeqSet(x) => collect_cited_param_indices_from_obj(
            &x.set,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::FiniteSeqListObj(x) => {
            for arg in x.objs.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
        Obj::ObjAtIndex(x) => collect_cited_param_indices_from_two_objs(
            &x.obj,
            &x.index,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::MatrixSet(x) => {
            collect_cited_param_indices_from_obj(
                &x.set,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.row_len,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.col_len,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::MatrixListObj(x) => {
            for row in x.rows.iter() {
                for item in row.iter() {
                    collect_cited_param_indices_from_obj(
                        item,
                        previous_param_indices,
                        shadowed_names,
                        out,
                    );
                }
            }
        }
        Obj::MatrixAdd(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::MatrixSub(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::MatrixMul(x) => collect_cited_param_indices_from_two_objs(
            &x.left,
            &x.right,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::MatrixScalarMul(x) => collect_cited_param_indices_from_two_objs(
            &x.scalar,
            &x.matrix,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::MatrixPow(x) => collect_cited_param_indices_from_two_objs(
            &x.base,
            &x.exponent,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        Obj::StructObj(x) => {
            for arg in x.params.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
        Obj::ObjAsStructInstanceWithFieldAccess(x) => {
            for arg in x.struct_obj.params.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
            collect_cited_param_indices_from_obj(
                &x.obj,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        Obj::InstantiatedTemplateObj(x) => {
            for arg in x.args.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
    }
}

fn collect_cited_param_indices_from_two_objs(
    left: &Obj,
    right: &Obj,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    collect_cited_param_indices_from_obj(left, previous_param_indices, shadowed_names, out);
    collect_cited_param_indices_from_obj(right, previous_param_indices, shadowed_names, out);
}

fn collect_cited_param_indices_from_atom(
    atom: &AtomObj,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    match atom {
        AtomObj::Identifier(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::IdentifierWithMod(_) => {}
        AtomObj::Forall(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::Def(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::Exist(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::SetBuilder(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::FnSet(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::Induc(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::DefAlgo(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::DefStructField(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::TupleIndex(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        AtomObj::CartIndex(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
    }
}

fn collect_cited_param_indices_from_fn_head(
    head: &FnObjHead,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    match head {
        FnObjHead::Identifier(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::IdentifierWithMod(_) => {}
        FnObjHead::Forall(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::DefHeader(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::Exist(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::SetBuilder(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::FnSet(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::DefStructField(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::AnonymousFnLiteral(x) => collect_cited_param_indices_from_anonymous_fn(
            x,
            previous_param_indices,
            shadowed_names,
            out,
        ),
        FnObjHead::FiniteSeqListObj(x) => {
            for arg in x.objs.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
        FnObjHead::ObjAtIndex(x) => {
            collect_cited_param_indices_from_obj(
                &x.obj,
                previous_param_indices,
                shadowed_names,
                out,
            );
            collect_cited_param_indices_from_obj(
                &x.index,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        FnObjHead::ObjAsStructInstanceWithFieldAccess(x) => {
            for arg in x.struct_obj.params.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
            collect_cited_param_indices_from_obj(
                &x.obj,
                previous_param_indices,
                shadowed_names,
                out,
            );
        }
        FnObjHead::Induc(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::DefAlgo(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::TupleIndex(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::CartIndex(x) => {
            push_cited_param_index(&x.name, previous_param_indices, shadowed_names, out)
        }
        FnObjHead::InstantiatedTemplateObj(x) => {
            for arg in x.args.iter() {
                collect_cited_param_indices_from_obj(
                    arg,
                    previous_param_indices,
                    shadowed_names,
                    out,
                );
            }
        }
    }
}

fn collect_cited_param_indices_from_anonymous_fn(
    anonymous_fn: &AnonymousFn,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    collect_cited_param_indices_from_fn_set_body(
        &anonymous_fn.body,
        previous_param_indices,
        shadowed_names,
        out,
    );
    let added = push_param_names_to_shadow(&anonymous_fn.body.params_def_with_set, shadowed_names);
    collect_cited_param_indices_from_obj(
        &anonymous_fn.equal_to,
        previous_param_indices,
        shadowed_names,
        out,
    );
    pop_shadowed_names(shadowed_names, added);
}

fn collect_cited_param_indices_from_fn_set_body(
    body: &FnSetBody,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    let original_shadow_len = shadowed_names.len();
    for group in body.params_def_with_set.iter() {
        collect_cited_param_indices_from_obj(
            group.set_obj(),
            previous_param_indices,
            shadowed_names,
            out,
        );
        for param_name in group.params.iter() {
            shadowed_names.push(param_name.clone());
        }
    }
    for fact in body.dom_facts.iter() {
        collect_cited_param_indices_from_or_and_chain(
            fact,
            previous_param_indices,
            shadowed_names,
            out,
        );
    }
    collect_cited_param_indices_from_obj(
        &body.ret_set,
        previous_param_indices,
        shadowed_names,
        out,
    );
    while shadowed_names.len() > original_shadow_len {
        shadowed_names.pop();
    }
}

fn collect_cited_param_indices_from_or_and_chain(
    fact: &OrAndChainAtomicFact,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    for arg in fact.get_args_from_fact().iter() {
        collect_cited_param_indices_from_obj(arg, previous_param_indices, shadowed_names, out);
    }
}

fn collect_cited_param_indices_from_exist_body_fact(
    fact: &ExistBodyFact,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &mut Vec<String>,
    out: &mut Vec<usize>,
) {
    for arg in fact.get_args_from_fact().iter() {
        collect_cited_param_indices_from_obj(arg, previous_param_indices, shadowed_names, out);
    }
}

fn push_param_names_to_shadow(
    param_defs: &ParamDefWithSet,
    shadowed_names: &mut Vec<String>,
) -> usize {
    let mut count = 0;
    for group in param_defs.iter() {
        for param_name in group.params.iter() {
            shadowed_names.push(param_name.clone());
            count += 1;
        }
    }
    count
}

fn pop_shadowed_names(shadowed_names: &mut Vec<String>, count: usize) {
    for _ in 0..count {
        shadowed_names.pop();
    }
}

fn push_cited_param_index(
    name: &str,
    previous_param_indices: &HashMap<String, usize>,
    shadowed_names: &Vec<String>,
    out: &mut Vec<usize>,
) {
    if shadowed_names
        .iter()
        .any(|shadowed_name| shadowed_name == name)
    {
        return;
    }
    if let Some(index) = previous_param_indices.get(name) {
        if !out.contains(index) {
            out.push(*index);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn param_def_with_type_records_flat_cited_param_indices() {
        let cited_type = Tuple::new(vec![
            ForallFreeParamObj::new("a".to_string()).into(),
            ForallFreeParamObj::new("b".to_string()).into(),
        ])
        .into();
        let param_def = ParamDefWithType::new(vec![
            ParamGroupWithParamType::new(
                vec!["a".to_string(), "b".to_string()],
                ParamType::Set(Set::new()),
            ),
            ParamGroupWithParamType::new(vec!["f".to_string()], ParamType::Obj(cited_type)),
        ]);

        assert_eq!(
            param_def.param_type_cited_param_indices[0],
            Vec::<usize>::new()
        );
        assert_eq!(param_def.param_type_cited_param_indices[1], vec![0, 1]);
    }

    #[test]
    fn param_def_with_set_records_flat_cited_param_indices() {
        let dependent_set = ClosedRange::new(
            Number::new("1".to_string()).into(),
            FnSetFreeParamObj::new("n".to_string()).into(),
        )
        .into();
        let param_def = ParamDefWithSet::new(vec![
            ParamGroupWithSet::new(vec!["n".to_string()], StandardSet::NPos.into()),
            ParamGroupWithSet::new(vec!["x".to_string()], dependent_set),
        ]);

        assert_eq!(
            param_def.param_set_cited_param_indices[0],
            Vec::<usize>::new()
        );
        assert_eq!(param_def.param_set_cited_param_indices[1], vec![0]);
    }

    #[test]
    fn dependent_param_set_instantiates_with_previous_arg() {
        let dependent_set = ClosedRange::new(
            Number::new("1".to_string()).into(),
            FnSetFreeParamObj::new("n".to_string()).into(),
        )
        .into();
        let param_def = ParamDefWithSet::new(vec![
            ParamGroupWithSet::new(vec!["n".to_string()], StandardSet::NPos.into()),
            ParamGroupWithSet::new(vec!["x".to_string()], dependent_set),
        ]);
        let args = vec![
            Number::new("3".to_string()).into(),
            Number::new("2".to_string()).into(),
        ];
        let runtime = Runtime::new();

        let instantiated = runtime
            .inst_param_def_with_set_one_by_one(&param_def, &args, ParamObjType::FnSet)
            .unwrap();

        assert_eq!(instantiated[1].to_string(), "closed_range(1, 3)");
    }
}
