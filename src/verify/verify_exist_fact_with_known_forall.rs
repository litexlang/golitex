use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

// Same ∀-instantiation strategy as `verify_atomic_fact_with_known_forall`, plus exist-internal params.

impl Runtime {
    pub fn verify_exist_fact_with_known_forall(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_exist_fact_with_known_forall_facts_in_envs(exist_fact, verify_state)?
        {
            return Ok((fact_verified).into());
        }
        Ok((StmtUnknown::new()).into())
    }

    fn get_matched_exist_fact_in_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_exist_fact: &ExistFactEnum,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let lookup_keys = known_exist_lookup_keys_for_forall_bucket(given_exist_fact);

        let envs_count = self.environment_count();
        for i in iterate_from_env_index..envs_count {
            let env = self
                .environment_by_top_index(i)
                .expect("environment index should be valid");
            let mut merged_bucket: Vec<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)> =
                Vec::new();
            for lk in lookup_keys.iter() {
                if let Some(known_forall_facts_in_env) =
                    env.known_exist_facts_in_forall_facts.get(lk.as_str())
                {
                    merged_bucket.extend(known_forall_facts_in_env.iter().cloned());
                }
            }
            merged_bucket.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));
            merged_bucket.dedup_by(|a, b| a.0.to_string() == b.0.to_string());
            if !merged_bucket.is_empty() {
                let known_forall_facts_count = merged_bucket.len();
                let start_index = if i == iterate_from_env_index {
                    iterate_from_known_forall_fact_index
                } else {
                    0
                };
                for j in start_index..known_forall_facts_count {
                    let entry_idx = known_forall_facts_count - 1 - j;
                    let (fact_args_in_known_forall, given_fact_args, current_known_forall) = {
                        let current_known_forall = &merged_bucket[entry_idx];
                        (
                            current_known_forall.0.get_args_from_fact_ref(),
                            given_exist_fact.get_args_from_fact_ref(),
                            current_known_forall.clone(),
                        )
                    };
                    if Runtime::_verify_exist_fact_the_same_type_and_return_matched_args(
                        &current_known_forall.0,
                        given_exist_fact,
                    )?
                    .is_none()
                    {
                        continue;
                    }
                    let match_result = self
                        .match_args_in_fact_in_known_forall_fact_with_given_args(
                            &fact_args_in_known_forall,
                            &given_fact_args,
                        )?;
                    if let Some(arg_map) = match_result {
                        let exist_in_forall = &current_known_forall.0;
                        if !exist_in_forall.can_be_used_to_verify_goal(given_exist_fact) {
                            continue;
                        }
                        return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                    }
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_exist_fact_with_known_forall_facts_in_envs(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_exist_fact_in_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                exist_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((exist_fact_in_known_forall, forall_rc))) => {
                    if let Some(fact_verified) = self
                        .verify_exist_fact_args_satisfy_forall_requirements(
                            &exist_fact_in_known_forall,
                            &forall_rc,
                            arg_map,
                            exist_fact,
                            verify_state,
                        )?
                    {
                        return Ok(Some(fact_verified));
                    }
                    iterate_from_env_index = i;
                    iterate_from_known_forall_fact_index = j + 1;
                }
                _ => return Ok(None),
            }
        }
    }

    fn verify_exist_fact_args_satisfy_forall_requirements(
        &mut self,
        exist_fact_in_known_forall: &ExistFactEnum,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        if !exist_fact_in_known_forall.can_be_used_to_verify_goal(given_exist_fact) {
            return Ok(None);
        }
        // exist param matches exist param
        let given_exist_param_names = given_exist_fact
            .params_def_with_type()
            .collect_param_names();

        let known_exist_param_names = exist_fact_in_known_forall
            .params_def_with_type()
            .collect_param_names();
        if !known_exist_param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        if given_exist_param_names.len() != known_exist_param_names.len() {
            return Ok(None);
        }

        let mut known_exist_params_to_given_exist_params_map: Vec<Obj> = Vec::new();
        for (known_param_name, given_param_name) in known_exist_param_names
            .iter()
            .zip(given_exist_param_names.iter())
        {
            let obj = match arg_map.get(known_param_name) {
                Some(v) => {
                    if !Self::obj_matches_exist_forall_binding_name(v, given_param_name) {
                        return Ok(None);
                    }
                    v
                }
                None => return Ok(None),
            };
            known_exist_params_to_given_exist_params_map.push(obj.clone());
        }

        // given exist param can only match known exist param, it can not match other params
        for (key, obj) in arg_map.iter() {
            if let Some(spine) = Self::obj_binding_spine_name_for_arg_map(obj) {
                if given_exist_param_names.iter().any(|n| n == spine) {
                    if !known_exist_param_names.contains(key) {
                        return Ok(None);
                    }
                }
            }
        }

        let param_names = known_forall.params_def.collect_param_names();
        for param_name in param_names.iter() {
            let Some(obj) = arg_map.get(param_name) else {
                return Ok(None);
            };
            if Self::obj_depends_on_given_exist_param(obj, &given_exist_param_names) {
                return Ok(None);
            }
        }

        let Some((instantiation, requirements)) = self
            .verify_known_forall_requirements_and_build_evidence(
                known_forall.as_ref(),
                &arg_map,
                given_exist_fact.clone().into(),
                verify_state,
            )?
        else {
            return Ok(None);
        };

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![exist_fact_in_known_forall.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_exist_fact.clone().into(),
            VerifiedByResult::known_forall_instantiation(
                verified_by_known_forall_fact.clone().into(),
                instantiation,
                requirements,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    fn obj_binding_spine_name_for_arg_map(obj: &Obj) -> Option<&str> {
        match obj {
            Obj::Atom(AtomObj::Exist(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Forall(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::FnSet(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Def(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::SetBuilder(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Induc(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::DefAlgo(p)) => Some(p.name.as_str()),
            _ => None,
        }
    }

    fn obj_matches_exist_forall_binding_name(obj: &Obj, name: &str) -> bool {
        match obj {
            Obj::Atom(AtomObj::Exist(p)) => p.name == name,
            Obj::Atom(AtomObj::Forall(p)) => p.name == name,
            Obj::Atom(AtomObj::FnSet(p)) => p.name == name,
            Obj::Atom(AtomObj::Def(p)) => p.name == name,
            Obj::Atom(AtomObj::SetBuilder(p)) => p.name == name,
            Obj::Atom(AtomObj::Induc(p)) => p.name == name,
            Obj::Atom(AtomObj::DefAlgo(p)) => p.name == name,
            _ => obj.to_string() == name,
        }
    }

    pub(crate) fn obj_depends_on_given_exist_param(obj: &Obj, names: &[String]) -> bool {
        match obj {
            Obj::Atom(AtomObj::Exist(p)) => names.iter().any(|name| name == &p.name),
            Obj::Atom(_) | Obj::Number(_) | Obj::StandardSet(_) => false,
            Obj::Add(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::Sub(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::Mul(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::Div(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::Mod(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::IntegerQuotient(x) => Self::obj_pair_depends_on_given_exist_param(
                x.dividend.as_ref(),
                x.divisor.as_ref(),
                names,
            ),
            Obj::Pow(x) => Self::obj_pair_depends_on_given_exist_param(
                x.base.as_ref(),
                x.exponent.as_ref(),
                names,
            ),
            Obj::Union(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::Intersect(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::SetMinus(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::SetDiff(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::MatrixAdd(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::MatrixSub(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::MatrixMul(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                names,
            ),
            Obj::MatrixScalarMul(x) => Self::obj_pair_depends_on_given_exist_param(
                x.scalar.as_ref(),
                x.matrix.as_ref(),
                names,
            ),
            Obj::MatrixPow(x) => Self::obj_pair_depends_on_given_exist_param(
                x.base.as_ref(),
                x.exponent.as_ref(),
                names,
            ),
            Obj::Log(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.base.as_ref(), x.arg.as_ref(), names)
            }
            Obj::Range(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.start.as_ref(), x.end.as_ref(), names)
            }
            Obj::ClosedRange(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.start.as_ref(), x.end.as_ref(), names)
            }
            Obj::IntervalObj(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.start(), x.end(), names)
            }
            Obj::OneSideInfinityIntervalObj(x) => {
                Self::obj_depends_on_given_exist_param(x.start(), names)
            }
            Obj::Proj(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.set.as_ref(), x.dim.as_ref(), names)
            }
            Obj::FiniteSeqSet(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.set.as_ref(), x.n.as_ref(), names)
            }
            Obj::MatrixSet(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.row_len.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.col_len.as_ref(), names)
            }
            Obj::ObjAtIndex(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.obj.as_ref(), x.index.as_ref(), names)
            }
            Obj::Abs(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), names),
            Obj::Sqrt(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), names),
            Obj::BigUnion(x) => Self::obj_depends_on_given_exist_param(x.left.as_ref(), names),
            Obj::BigIntersect(x) => Self::obj_depends_on_given_exist_param(x.left.as_ref(), names),
            Obj::PowerSet(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), names),
            Obj::CartDim(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), names),
            Obj::TupleDim(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), names),
            Obj::FiniteSetSize(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), names),
            Obj::FiniteSetMax(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), names),
            Obj::FiniteSetMin(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), names),
            Obj::FnRange(x) => Self::obj_depends_on_given_exist_param(x.function.as_ref(), names),
            Obj::Replacement(x) => {
                Self::obj_depends_on_given_exist_param(x.source_set.as_ref(), names)
            }
            Obj::SeqSet(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), names),
            Obj::Sum(x) => {
                Self::obj_depends_on_given_exist_param(x.start.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.end.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), names)
            }
            Obj::SumOfFiniteSet(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), names)
            }
            Obj::Product(x) => {
                Self::obj_depends_on_given_exist_param(x.start.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.end.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), names)
            }
            Obj::ProductOfFiniteSet(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), names)
            }
            Obj::ListSet(x) => Self::obj_list_depends_on_given_exist_param(&x.list, names),
            Obj::Cart(x) => Self::obj_list_depends_on_given_exist_param(&x.args, names),
            Obj::Tuple(x) => Self::obj_list_depends_on_given_exist_param(&x.args, names),
            Obj::FiniteSeqListObj(x) => Self::obj_list_depends_on_given_exist_param(&x.objs, names),
            Obj::MatrixListObj(x) => x.rows.iter().any(|row| {
                row.iter()
                    .any(|obj| Self::obj_depends_on_given_exist_param(obj.as_ref(), names))
            }),
            Obj::StructObj(x) => x
                .params
                .iter()
                .any(|obj| Self::obj_depends_on_given_exist_param(obj, names)),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                x.struct_obj
                    .params
                    .iter()
                    .any(|obj| Self::obj_depends_on_given_exist_param(obj, names))
                    || Self::obj_depends_on_given_exist_param(x.obj.as_ref(), names)
            }
            Obj::InstantiatedTemplateObj(x) => x
                .args
                .iter()
                .any(|obj| Self::obj_depends_on_given_exist_param(obj, names)),
            Obj::SetBuilder(x) => {
                Self::obj_depends_on_given_exist_param(x.param_set.as_ref(), names)
                    || x.facts
                        .iter()
                        .any(|fact| Self::exist_body_fact_depends_on_given_exist_param(fact, names))
            }
            Obj::GeneralCart(x) => {
                Self::obj_depends_on_given_exist_param(x.index_set.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.family_set.as_ref(), names)
                    || Self::obj_depends_on_given_exist_param(x.family_fn.as_ref(), names)
            }
            Obj::FnSet(x) => Self::fn_set_body_depends_on_given_exist_param(&x.body, names),
            Obj::AnonymousFn(x) => {
                Self::fn_set_body_depends_on_given_exist_param(&x.body, names)
                    || Self::obj_depends_on_given_exist_param(x.equal_to.as_ref(), names)
            }
            Obj::FnObj(x) => {
                Self::fn_obj_head_depends_on_given_exist_param(x.head.as_ref(), names)
                    || x.body.iter().any(|args| {
                        args.iter()
                            .any(|arg| Self::obj_depends_on_given_exist_param(arg.as_ref(), names))
                    })
            }
        }
    }

    fn obj_pair_depends_on_given_exist_param(left: &Obj, right: &Obj, names: &[String]) -> bool {
        Self::obj_depends_on_given_exist_param(left, names)
            || Self::obj_depends_on_given_exist_param(right, names)
    }

    fn obj_list_depends_on_given_exist_param(objs: &[Box<Obj>], names: &[String]) -> bool {
        objs.iter()
            .any(|obj| Self::obj_depends_on_given_exist_param(obj.as_ref(), names))
    }

    fn fn_set_body_depends_on_given_exist_param(body: &FnSetBody, names: &[String]) -> bool {
        body.params_def_with_set.iter().any(|param_group| {
            Self::param_group_with_set_depends_on_given_exist_param(param_group, names)
        }) || body
            .dom_facts
            .iter()
            .any(|fact| Self::or_and_chain_fact_depends_on_given_exist_param(fact, names))
            || Self::obj_depends_on_given_exist_param(body.ret_set.as_ref(), names)
    }

    fn fn_obj_head_depends_on_given_exist_param(head: &FnObjHead, names: &[String]) -> bool {
        match head {
            FnObjHead::Exist(p) => names.iter().any(|name| name == &p.name),
            FnObjHead::AnonymousFnLiteral(x) => {
                Self::fn_set_body_depends_on_given_exist_param(&x.body, names)
                    || Self::obj_depends_on_given_exist_param(x.equal_to.as_ref(), names)
            }
            FnObjHead::ObjAtIndex(x) => {
                Self::obj_depends_on_given_exist_param(&Obj::ObjAtIndex(x.clone()), names)
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(x) => {
                Self::obj_depends_on_given_exist_param(
                    &Obj::ObjAsStructInstanceWithFieldAccess(x.clone()),
                    names,
                )
            }
            FnObjHead::InstantiatedTemplateObj(x) => Self::obj_depends_on_given_exist_param(
                &Obj::InstantiatedTemplateObj(x.clone()),
                names,
            ),
            _ => false,
        }
    }

    fn param_group_with_set_depends_on_given_exist_param(
        param_group: &ParamGroupWithSet,
        names: &[String],
    ) -> bool {
        Self::obj_depends_on_given_exist_param(param_group.set_obj(), names)
    }

    fn or_and_chain_fact_depends_on_given_exist_param(
        fact: &OrAndChainAtomicFact,
        names: &[String],
    ) -> bool {
        fact.get_args_from_fact_ref()
            .into_iter()
            .any(|obj| Self::obj_depends_on_given_exist_param(obj, names))
    }

    fn exist_body_fact_depends_on_given_exist_param(
        fact: &ExistBodyFact,
        names: &[String],
    ) -> bool {
        fact.get_args_from_fact_ref()
            .into_iter()
            .any(|obj| Self::obj_depends_on_given_exist_param(obj, names))
    }
}

fn known_exist_lookup_keys_for_forall_bucket(goal: &ExistFactEnum) -> Vec<String> {
    let mut keys = vec![goal.alpha_normalized_key(), goal.key()];
    if let ExistFactEnum::ExistFact(body) = goal {
        let unique = ExistFactEnum::ExistUniqueFact(body.clone());
        keys.push(unique.alpha_normalized_key());
        keys.push(unique.key());
    }
    keys.sort();
    keys.dedup();
    keys
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_nested_exist_witness_dependency() {
        let names = vec!["x".to_string()];
        let witness: Obj = ExistFreeParamObj::new("x".to_string()).into();
        let external: Obj = Identifier::new("a".to_string()).into();
        let nested: Obj = Union::new(witness, external.clone()).into();

        assert!(Runtime::obj_depends_on_given_exist_param(&nested, &names));
        assert!(!Runtime::obj_depends_on_given_exist_param(
            &external, &names
        ));
    }

    #[test]
    fn detects_function_call_on_exist_witness() {
        let names = vec!["x".to_string()];
        let head: FnObjHead = ExistFreeParamObj::new("x".to_string()).into();
        let arg: Obj = Number::new("1".to_string()).into();
        let fn_obj: Obj = FnObj::new(head, vec![vec![Box::new(arg)]]).into();

        assert!(Runtime::obj_depends_on_given_exist_param(&fn_obj, &names));
    }
}
