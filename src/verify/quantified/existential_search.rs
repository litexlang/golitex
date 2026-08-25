//! Existential verification through known universal facts.

use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

// Same ∀-instantiation strategy as `verify_atomic_fact_with_known_forall`, plus exist-internal params.

impl Runtime {
    pub fn verify_exist_fact_with_known_forall(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &ProofSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_exist_fact_with_known_forall_facts_in_envs(exist_fact, verify_state)?
        {
            return Ok((fact_verified).into());
        }
        Ok((UnknownGenericStmtResult::new()).into())
    }

    fn get_matched_exist_fact_in_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_exist_fact: &ExistFactEnum,
    ) -> Result<
        (
            (usize, usize),
            Option<(HashMap<String, Obj>, HashMap<String, Obj>)>,
            Option<(ExistFactEnum, Rc<StoredForallConclusionReference>)>,
        ),
        RuntimeError,
    > {
        let lookup_keys = known_exist_lookup_keys_for_forall_bucket(given_exist_fact);

        let envs_count = self.environment_count();
        for i in iterate_from_env_index..envs_count {
            let env = self
                .environment_by_top_index(i)
                .expect("environment index should be valid");
            let mut merged_bucket: Vec<(ExistFactEnum, Rc<StoredForallConclusionReference>)> =
                Vec::new();
            for lk in lookup_keys.iter() {
                if let Some(known_forall_facts_in_env) =
                    env.facts.known_exist_facts_in_forall_facts.get(lk.as_str())
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
                    let current_known_forall = merged_bucket[entry_idx].clone();
                    let Some(matched_args) = self
                        ._verify_exist_fact_the_same_type_and_return_matched_args(
                            &current_known_forall.0,
                            given_exist_fact,
                        )?
                    else {
                        continue;
                    };
                    let fact_args_in_known_forall: Vec<&Obj> =
                        matched_args.iter().map(|(known, _)| known).collect();
                    let given_fact_args: Vec<&Obj> =
                        matched_args.iter().map(|(_, given)| given).collect();
                    let match_result = self.match_args_in_fact_with_known_forall_bindings(
                        &fact_args_in_known_forall,
                        &given_fact_args,
                        &current_known_forall.1.params_def,
                        Some(current_known_forall.0.typed_parameters()),
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
        verify_state: &ProofSearchState,
    ) -> Result<Option<SuccessFactStmtResult>, RuntimeError> {
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
                (
                    Some((forall_arg_map, exist_arg_map)),
                    Some((exist_fact_in_known_forall, forall_rc)),
                ) => {
                    if let Some(fact_verified) = self
                        .verify_exist_fact_args_satisfy_forall_requirements(
                            &exist_fact_in_known_forall,
                            &forall_rc,
                            forall_arg_map,
                            exist_arg_map,
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
        known_forall: &Rc<StoredForallConclusionReference>,
        forall_arg_map: HashMap<String, Obj>,
        exist_arg_map: HashMap<String, Obj>,
        given_exist_fact: &ExistFactEnum,
        verify_state: &ProofSearchState,
    ) -> Result<Option<SuccessFactStmtResult>, RuntimeError> {
        if !exist_fact_in_known_forall.can_be_used_to_verify_goal(given_exist_fact) {
            return Ok(None);
        }
        // exist param matches exist param
        let given_exist_param_bindings =
            given_exist_fact.typed_parameters().collect_param_bindings();

        let known_exist_param_names = exist_fact_in_known_forall
            .typed_parameters()
            .collect_param_names();
        if !known_exist_param_names
            .iter()
            .all(|param_name| exist_arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        if given_exist_param_bindings.len() != known_exist_param_names.len() {
            return Ok(None);
        }

        for (known_param_name, given_param_binding) in known_exist_param_names
            .iter()
            .zip(given_exist_param_bindings.iter())
        {
            let Some(obj) = exist_arg_map.get(known_param_name) else {
                return Ok(None);
            };
            if !Self::obj_matches_exist_forall_binding(obj, given_param_binding.id()) {
                return Ok(None);
            }
        }

        let given_exist_param_ids = given_exist_param_bindings
            .iter()
            .map(SymbolBinding::id)
            .collect::<Vec<_>>();
        let param_names = known_forall.params_def.collect_param_names();
        for param_name in param_names.iter() {
            let Some(obj) = forall_arg_map.get(param_name) else {
                return Ok(None);
            };
            if Self::obj_depends_on_given_exist_param(obj, &given_exist_param_ids) {
                return Ok(None);
            }
        }

        let Some((instantiation, requirements)) = self
            .verify_known_forall_requirements_and_build_evidence(
                known_forall.as_ref(),
                &forall_arg_map,
                given_exist_fact.clone().into(),
                verify_state,
            )?
        else {
            return Ok(None);
        };

        let source_fact = known_forall.source_fact();
        let source_fact_id = known_forall.source_fact_id;
        let fact_verified = SuccessFactStmtResult::new_with_verified_by_known_fact(
            given_exist_fact.clone().into(),
            SuccessFactProofResult::known_forall_instantiation(
                source_fact,
                source_fact_id,
                known_forall.conclusion_location,
                instantiation,
                requirements,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    fn obj_matches_exist_forall_binding(obj: &Obj, symbol_id: SymbolId) -> bool {
        matches!(obj, Obj::Atom(AtomObj::Bound(p)) if p.symbol.id() == symbol_id)
    }

    pub fn obj_depends_on_given_exist_param(obj: &Obj, symbol_ids: &[SymbolId]) -> bool {
        match obj {
            Obj::Atom(AtomObj::Bound(p)) => symbol_ids.contains(&p.symbol.id()),
            Obj::Atom(_)
            | Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_) => false,
            Obj::Add(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Sub(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Mul(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Div(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Mod(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Quot(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Gcd(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Lcm(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Min(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Max(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Pow(x) => Self::obj_pair_depends_on_given_exist_param(
                x.base.as_ref(),
                x.exponent.as_ref(),
                symbol_ids,
            ),
            Obj::Union(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::Intersect(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::SetMinus(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::MatrixAdd(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::MatrixSub(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::MatrixMul(x) => Self::obj_pair_depends_on_given_exist_param(
                x.left.as_ref(),
                x.right.as_ref(),
                symbol_ids,
            ),
            Obj::MatrixScalarMul(x) => Self::obj_pair_depends_on_given_exist_param(
                x.scalar.as_ref(),
                x.matrix.as_ref(),
                symbol_ids,
            ),
            Obj::MatrixPow(x) => Self::obj_pair_depends_on_given_exist_param(
                x.base.as_ref(),
                x.exponent.as_ref(),
                symbol_ids,
            ),
            Obj::Log(x) => Self::obj_pair_depends_on_given_exist_param(
                x.base.as_ref(),
                x.arg.as_ref(),
                symbol_ids,
            ),
            Obj::Exp(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Ln(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Sign(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Factorial(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Range(x) => Self::obj_pair_depends_on_given_exist_param(
                x.start.as_ref(),
                x.end.as_ref(),
                symbol_ids,
            ),
            Obj::ClosedRange(x) => Self::obj_pair_depends_on_given_exist_param(
                x.start.as_ref(),
                x.end.as_ref(),
                symbol_ids,
            ),
            Obj::IntervalObj(x) => {
                Self::obj_pair_depends_on_given_exist_param(x.start(), x.end(), symbol_ids)
            }
            Obj::OneSideInfinityIntervalObj(x) => {
                Self::obj_depends_on_given_exist_param(x.start(), symbol_ids)
            }
            Obj::Proj(x) => Self::obj_pair_depends_on_given_exist_param(
                x.set.as_ref(),
                x.dim.as_ref(),
                symbol_ids,
            ),
            Obj::FiniteSeqSet(x) => Self::obj_pair_depends_on_given_exist_param(
                x.set.as_ref(),
                x.n.as_ref(),
                symbol_ids,
            ),
            Obj::MatrixSet(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.row_len.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.col_len.as_ref(), symbol_ids)
            }
            Obj::ObjAtIndex(x) => Self::obj_pair_depends_on_given_exist_param(
                x.obj.as_ref(),
                x.index.as_ref(),
                symbol_ids,
            ),
            Obj::Abs(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Floor(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Ceil(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Sin(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Arcsin(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Cos(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Tan(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::Cot(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::RealPart(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::ImaginaryPart(x) => {
                Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids)
            }
            Obj::ComplexAbs(x) => {
                Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids)
            }
            Obj::Sqrt(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::BigUnion(x) => Self::obj_depends_on_given_exist_param(x.left.as_ref(), symbol_ids),
            Obj::BigIntersect(x) => {
                Self::obj_depends_on_given_exist_param(x.left.as_ref(), symbol_ids)
            }
            Obj::IndexUnion(x) => {
                Self::obj_depends_on_given_exist_param(x.index_set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.ambient_set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.family_fn.as_ref(), symbol_ids)
            }
            Obj::IndexIntersect(x) => {
                Self::obj_depends_on_given_exist_param(x.index_set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.ambient_set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.family_fn.as_ref(), symbol_ids)
            }
            Obj::PowerSet(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids),
            Obj::CartDim(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids),
            Obj::TupleDim(x) => Self::obj_depends_on_given_exist_param(x.arg.as_ref(), symbol_ids),
            Obj::FiniteSetSize(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
            }
            Obj::FiniteSetMax(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
            }
            Obj::FiniteSetMin(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
            }
            Obj::FnRange(x) => {
                Self::obj_depends_on_given_exist_param(x.function.as_ref(), symbol_ids)
            }
            Obj::Replacement(x) => {
                Self::obj_depends_on_given_exist_param(x.source_set.as_ref(), symbol_ids)
            }
            Obj::SeqSet(x) => Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids),
            Obj::Sum(x) => {
                Self::obj_depends_on_given_exist_param(x.start.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.end.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), symbol_ids)
            }
            Obj::SumOfFiniteSet(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), symbol_ids)
            }
            Obj::Product(x) => {
                Self::obj_depends_on_given_exist_param(x.start.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.end.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), symbol_ids)
            }
            Obj::ProductOfFiniteSet(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), symbol_ids)
            }
            Obj::Reduce(x) => {
                Self::obj_depends_on_given_exist_param(x.start.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.end.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.op.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.seed.as_ref(), symbol_ids)
            }
            Obj::FiniteSetReduce(x) => {
                Self::obj_depends_on_given_exist_param(x.set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.func.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.op.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.seed.as_ref(), symbol_ids)
            }
            Obj::ListSet(x) => Self::obj_list_depends_on_given_exist_param(&x.list, symbol_ids),
            Obj::Cart(x) => Self::obj_list_depends_on_given_exist_param(&x.args, symbol_ids),
            Obj::Tuple(x) => Self::obj_list_depends_on_given_exist_param(&x.args, symbol_ids),
            Obj::FiniteSeqListObj(x) => {
                Self::obj_list_depends_on_given_exist_param(&x.objs, symbol_ids)
            }
            Obj::MatrixListObj(x) => x.rows.iter().any(|row| {
                row.iter()
                    .any(|obj| Self::obj_depends_on_given_exist_param(obj.as_ref(), symbol_ids))
            }),
            Obj::StructObj(x) => x
                .params
                .iter()
                .any(|obj| Self::obj_depends_on_given_exist_param(obj, symbol_ids)),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                x.struct_obj
                    .params
                    .iter()
                    .any(|obj| Self::obj_depends_on_given_exist_param(obj, symbol_ids))
                    || Self::obj_depends_on_given_exist_param(x.obj.as_ref(), symbol_ids)
            }
            Obj::InstantiatedTemplateObj(x) => x
                .args
                .iter()
                .any(|obj| Self::obj_depends_on_given_exist_param(obj, symbol_ids)),
            Obj::SetBuilder(x) => {
                Self::obj_depends_on_given_exist_param(x.param_set.as_ref(), symbol_ids)
                    || x.facts.iter().any(|fact| {
                        Self::quantifier_free_fact_depends_on_given_exist_param(fact, symbol_ids)
                    })
            }
            Obj::GeneralCart(x) => {
                Self::obj_depends_on_given_exist_param(x.index_set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.family_set.as_ref(), symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.family_fn.as_ref(), symbol_ids)
            }
            Obj::FnSet(x) => Self::fn_set_body_depends_on_given_exist_param(&x.body, symbol_ids),
            Obj::AnonymousFn(x) => {
                Self::fn_set_body_depends_on_given_exist_param(&x.body, symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.equal_to.as_ref(), symbol_ids)
            }
            Obj::FnObj(x) => {
                Self::fn_obj_head_depends_on_given_exist_param(x.head.as_ref(), symbol_ids)
                    || x.body.iter().any(|args| {
                        args.iter().any(|arg| {
                            Self::obj_depends_on_given_exist_param(arg.as_ref(), symbol_ids)
                        })
                    })
            }
        }
    }

    fn obj_pair_depends_on_given_exist_param(
        left: &Obj,
        right: &Obj,
        symbol_ids: &[SymbolId],
    ) -> bool {
        Self::obj_depends_on_given_exist_param(left, symbol_ids)
            || Self::obj_depends_on_given_exist_param(right, symbol_ids)
    }

    fn obj_list_depends_on_given_exist_param(objs: &[Box<Obj>], symbol_ids: &[SymbolId]) -> bool {
        objs.iter()
            .any(|obj| Self::obj_depends_on_given_exist_param(obj.as_ref(), symbol_ids))
    }

    fn fn_set_body_depends_on_given_exist_param(body: &FnSetBody, symbol_ids: &[SymbolId]) -> bool {
        body.set_bound_parameters.iter().any(|param_group| {
            Self::param_group_with_set_depends_on_given_exist_param(param_group, symbol_ids)
        }) || body
            .dom_facts
            .iter()
            .any(|fact| Self::or_and_chain_fact_depends_on_given_exist_param(fact, symbol_ids))
            || Self::obj_depends_on_given_exist_param(body.ret_set.as_ref(), symbol_ids)
    }

    fn fn_obj_head_depends_on_given_exist_param(head: &FnObjHead, symbol_ids: &[SymbolId]) -> bool {
        match head {
            FnObjHead::Bound(p) => symbol_ids.contains(&p.symbol.id()),
            FnObjHead::AnonymousFnLiteral(x) => {
                Self::fn_set_body_depends_on_given_exist_param(&x.body, symbol_ids)
                    || Self::obj_depends_on_given_exist_param(x.equal_to.as_ref(), symbol_ids)
            }
            FnObjHead::ObjAtIndex(x) => {
                Self::obj_depends_on_given_exist_param(&Obj::ObjAtIndex(x.clone()), symbol_ids)
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(x) => {
                Self::obj_depends_on_given_exist_param(
                    &Obj::ObjAsStructInstanceWithFieldAccess(x.clone()),
                    symbol_ids,
                )
            }
            FnObjHead::InstantiatedTemplateObj(x) => Self::obj_depends_on_given_exist_param(
                &Obj::InstantiatedTemplateObj(x.clone()),
                symbol_ids,
            ),
            _ => false,
        }
    }

    fn param_group_with_set_depends_on_given_exist_param(
        param_group: &SetBoundParameterGroup,
        symbol_ids: &[SymbolId],
    ) -> bool {
        Self::obj_depends_on_given_exist_param(param_group.set_obj(), symbol_ids)
    }

    fn or_and_chain_fact_depends_on_given_exist_param(
        fact: &QuantifierFreeFact,
        symbol_ids: &[SymbolId],
    ) -> bool {
        fact.get_args_from_fact_ref()
            .into_iter()
            .any(|obj| Self::obj_depends_on_given_exist_param(obj, symbol_ids))
    }

    fn quantifier_free_fact_depends_on_given_exist_param(
        fact: &QuantifierFreeFact,
        symbol_ids: &[SymbolId],
    ) -> bool {
        fact.get_args_from_fact_ref()
            .into_iter()
            .any(|obj| Self::obj_depends_on_given_exist_param(obj, symbol_ids))
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
#[path = "../../../tests/unit/verify/quantified/existential_search.rs"]
mod tests;
