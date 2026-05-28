use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl Runtime {
    pub fn verify_atomic_fact_with_known_forall(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_with_known_forall_facts_in_envs(atomic_fact, verify_state)?
        {
            return Ok((fact_verified).into());
        }

        if let AtomicFact::EqualFact(equal_fact) = atomic_fact {
            let fact_with_reversed_args = EqualFact::new(
                equal_fact.right.clone(),
                equal_fact.left.clone(),
                equal_fact.line_file.clone(),
            );
            let fact_with_reversed_args: AtomicFact = fact_with_reversed_args.into();
            if let Some(fact_verified) = self.try_verify_with_known_forall_facts_in_envs(
                &fact_with_reversed_args,
                verify_state,
            )? {
                return Ok((fact_verified).into());
            }

            return Ok((StmtUnknown::new()).into());
        }

        Ok((StmtUnknown::new()).into())
    }

    fn get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_fact: &AtomicFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let key = given_fact.key();
        let is_true = given_fact.is_true();

        let envs_count = self.environment_stack.len();
        let lookup_key = (key.clone(), is_true);
        for i in iterate_from_env_index..envs_count {
            let stack_idx = envs_count - 1 - i;
            let known_forall_facts_count = {
                let env = &self.environment_stack[stack_idx];
                match env.known_atomic_facts_in_forall_facts.get(&lookup_key) {
                    Some(v) => v.len(),
                    None => continue,
                }
            };
            let start_index = if i == iterate_from_env_index {
                iterate_from_known_forall_fact_index
            } else {
                0
            };
            for j in start_index..known_forall_facts_count {
                let entry_idx = known_forall_facts_count - 1 - j;
                let (atomic_fact_in_known_forall, current_known_forall) = {
                    let env = &self.environment_stack[stack_idx];
                    let Some(known_forall_facts_in_env) =
                        env.known_atomic_facts_in_forall_facts.get(&lookup_key)
                    else {
                        continue;
                    };
                    let Some(current_known_forall) = known_forall_facts_in_env.get(entry_idx)
                    else {
                        continue;
                    };
                    (current_known_forall.0.clone(), current_known_forall.clone())
                };
                let match_result = self.match_atomic_fact_args_against_known_forall_ordered_args(
                    &atomic_fact_in_known_forall,
                    given_fact,
                )?;
                if let Some(arg_map) = match_result {
                    return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_with_fallback_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                atomic_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((atomic_fact_in_known_forall_fact, forall_rc))) => {
                    if let Some(fact_verified) = self.verify_args_satisfy_forall_requirements(
                        &atomic_fact_in_known_forall_fact,
                        &forall_rc,
                        arg_map,
                        atomic_fact,
                        verify_state,
                    )? {
                        return Ok(Some(fact_verified));
                    }
                    iterate_from_env_index = i;
                    iterate_from_known_forall_fact_index = j + 1;
                }
                _ => return Ok(None),
            }
        }
    }

    fn try_verify_with_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let arg_shape_lookup_keys = atomic_fact_in_forall_lookup_arg_shape_keys(atomic_fact);
        if let Some(fact_verified) = self.try_verify_with_arg_shape_known_forall_facts_in_envs(
            atomic_fact,
            &arg_shape_lookup_keys,
            verify_state,
        )? {
            return Ok(Some(fact_verified));
        }

        if let Some(fact_verified) =
            self.try_verify_with_fallback_known_forall_facts_in_envs(atomic_fact, verify_state)?
        {
            return Ok(Some(fact_verified));
        }

        self.try_verify_with_other_arg_shape_known_forall_facts_in_envs(
            atomic_fact,
            &arg_shape_lookup_keys,
            verify_state,
        )
    }

    fn try_verify_known_forall_candidate(
        &mut self,
        atomic_fact_in_known_forall_fact: AtomicFact,
        forall_rc: Rc<KnownForallFactParamsAndDom>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let match_result = self.match_atomic_fact_args_against_known_forall_ordered_args(
            &atomic_fact_in_known_forall_fact,
            given_atomic_fact,
        )?;
        if let Some(arg_map) = match_result {
            return self.verify_args_satisfy_forall_requirements(
                &atomic_fact_in_known_forall_fact,
                &forall_rc,
                arg_map,
                given_atomic_fact,
                verify_state,
            );
        }
        Ok(None)
    }

    fn try_verify_with_arg_shape_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        arg_shape_lookup_keys: &[AtomicFactInForallArgShapeKey],
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
        let envs_count = self.environment_stack.len();
        for i in 0..envs_count {
            let stack_idx = envs_count - 1 - i;
            for arg_shape_lookup_key in arg_shape_lookup_keys.iter() {
                if let Some(fact_verified) = self.try_verify_with_arg_shape_key_in_env(
                    stack_idx,
                    &lookup_key,
                    arg_shape_lookup_key,
                    atomic_fact,
                    verify_state,
                )? {
                    return Ok(Some(fact_verified));
                }
            }
        }
        Ok(None)
    }

    fn try_verify_with_other_arg_shape_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        arg_shape_lookup_keys: &[AtomicFactInForallArgShapeKey],
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
        let envs_count = self.environment_stack.len();
        for i in 0..envs_count {
            let stack_idx = envs_count - 1 - i;
            let arg_shape_keys = {
                let env = &self.environment_stack[stack_idx];
                let Some(arg_shape_map) = env
                    .known_atomic_facts_in_forall_facts_by_arg_shape
                    .get(&lookup_key)
                else {
                    continue;
                };
                arg_shape_map
                    .keys()
                    .filter(|key| !arg_shape_lookup_keys.contains(key))
                    .cloned()
                    .collect::<Vec<_>>()
            };
            for arg_shape_key in arg_shape_keys.iter() {
                if let Some(fact_verified) = self.try_verify_with_arg_shape_key_in_env(
                    stack_idx,
                    &lookup_key,
                    arg_shape_key,
                    atomic_fact,
                    verify_state,
                )? {
                    return Ok(Some(fact_verified));
                }
            }
        }
        Ok(None)
    }

    fn try_verify_with_arg_shape_key_in_env(
        &mut self,
        stack_idx: usize,
        lookup_key: &(AtomicFactKey, bool),
        arg_shape_key: &AtomicFactInForallArgShapeKey,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let Some(bucket_count) = ({
            let env = &self.environment_stack[stack_idx];
            env.known_atomic_facts_in_forall_facts_by_arg_shape
                .get(&lookup_key)
                .and_then(|arg_shape_map| arg_shape_map.get(arg_shape_key))
                .map(|bucket| bucket.len())
        }) else {
            return Ok(None);
        };

        for j in 0..bucket_count {
            let entry_idx = bucket_count - 1 - j;
            let candidate = {
                let env = &self.environment_stack[stack_idx];
                env.known_atomic_facts_in_forall_facts_by_arg_shape
                    .get(lookup_key)
                    .and_then(|arg_shape_map| arg_shape_map.get(arg_shape_key))
                    .and_then(|bucket| bucket.get(entry_idx))
                    .cloned()
            };
            let Some((atomic_fact_in_known_forall_fact, forall_rc)) = candidate else {
                continue;
            };
            if let Some(fact_verified) = self.try_verify_known_forall_candidate(
                atomic_fact_in_known_forall_fact,
                forall_rc,
                atomic_fact,
                verify_state,
            )? {
                return Ok(Some(fact_verified));
            }
        }
        Ok(None)
    }

    fn verify_args_satisfy_forall_requirements(
        &mut self,
        atomic_fact_in_known_forall_fact: &AtomicFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let param_names = known_forall.params_def.collect_param_names();

        if !param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        // Collect the arg for each param.
        let mut args_for_params: Vec<Obj> = Vec::new();

        for param_name in param_names.iter() {
            let obj = match arg_map.get(param_name) {
                Some(v) => v,
                None => return Ok(None),
            };

            args_for_params.push(obj.clone());
        }

        let args_param_types = self
            .verify_args_satisfy_param_def_flat_types(
                &known_forall.params_def,
                &args_for_params,
                verify_state,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(given_atomic_fact.clone()).into_stmt()),
                        String::new(),
                        given_atomic_fact.line_file(),
                        Some(e),
                        vec![],
                    )))
                }
            })?;
        if args_param_types.is_unknown() {
            return Ok(None);
        }

        let param_to_arg_map = match known_forall
            .params_def
            .param_def_params_to_arg_map(&arg_map)
        {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = self
                .inst_fact(dom_fact, &param_to_arg_map, ParamObjType::Forall, None)
                .map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(given_atomic_fact.clone()).into_stmt()),
                            String::new(),
                            given_atomic_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    }
                })?;
            let result = self
                .verify_fact(&instantiated_dom_fact, verify_state)
                .map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(given_atomic_fact.clone()).into_stmt()),
                            String::new(),
                            given_atomic_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    }
                })?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![atomic_fact_in_known_forall_fact.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_atomic_fact.clone().into(),
            VerifiedByResult::cited_fact(
                given_atomic_fact.clone().into(),
                verified_by_known_forall_fact.clone().into(),
                None,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    fn match_atomic_fact_args_against_known_forall_ordered_args(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if let Some(match_result) =
            self.match_in_fact_standard_set_target(atomic_fact_in_known_forall, given_fact)?
        {
            return Ok(match_result);
        }

        let atomic_fact_args_in_known_forall = atomic_fact_in_known_forall.args();
        let given_args = given_fact.args();
        let forward = self.match_args_in_fact_in_known_forall_fact_with_given_args(
            &atomic_fact_args_in_known_forall,
            &given_args,
        )?;
        return Ok(forward);
    }

    fn match_in_fact_standard_set_target(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
    ) -> Result<Option<Option<HashMap<String, Obj>>>, RuntimeError> {
        let (AtomicFact::InFact(known_in), AtomicFact::InFact(given_in)) =
            (atomic_fact_in_known_forall, given_fact)
        else {
            return Ok(None);
        };
        let (Obj::StandardSet(known_set), Obj::StandardSet(given_set)) =
            (&known_in.set, &given_in.set)
        else {
            return Ok(None);
        };

        let Some(element_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            &known_in.element,
            &given_in.element,
        )?
        else {
            return Ok(Some(None));
        };

        // Narrow known membership implies broader target membership directly.
        // Broad known membership may match a narrow target only when the narrow
        // membership is already a known atomic fact, not merely builtin-provable.
        if Self::standard_set_is_subset_eq(known_set, given_set) {
            return Ok(Some(Some(element_map)));
        }
        if Self::standard_set_is_subset_eq(given_set, known_set) {
            let known_only_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(given_fact)?;
            if known_only_result.is_true() {
                return Ok(Some(Some(element_map)));
            }
        }

        Ok(Some(None))
    }

    pub fn match_args_in_fact_in_known_forall_fact_with_given_args(
        &mut self,
        fact_args_in_known_forall: &Vec<Obj>,
        given_fact_args: &Vec<Obj>,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if fact_args_in_known_forall.len() != given_fact_args.len() {
            return Ok(None);
        }

        let mut atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map: HashMap<String, Obj> =
            HashMap::new();

        for (arg_in_atomic_fact_in_known_forall, arg_in_given) in
            fact_args_in_known_forall.iter().zip(given_fact_args.iter())
        {
            let sub_map_option = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                arg_in_atomic_fact_in_known_forall,
                arg_in_given,
            )?;
            let sub_map = match sub_map_option {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(
                &mut atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map,
                sub_map,
            ) {
                return Ok(None);
            }
        }

        Ok(Some(
            atom_in_known_atomic_fact_to_matched_objs_in_given_fact_map,
        ))
    }

    // Return None if the given arg does not match the known arg.
    // Return Some(HashMap::new()) if the given arg matches the known arg.
    fn match_arg_in_atomic_fact_in_known_forall_with_given_arg(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match known_arg {
            // Only `*FreeParamObj` bind; plain identifiers are fixed names.
            Obj::Atom(AtomObj::Identifier(ref id_known)) => {
                if id_known.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::IdentifierWithMod(_)) => {
                self.match_arg_when_left_is_identifier_with_mod(given_arg)
            }
            Obj::FnObj(ref f) => self.match_arg_when_left_is_fn_obj(f, given_arg),
            Obj::Number(ref left) => self.match_arg_when_left_is_number(left, given_arg),
            Obj::Add(ref a) => self.match_arg_when_left_is_add(&a.left, &a.right, given_arg),
            Obj::MatrixAdd(ref a) => {
                self.match_arg_when_left_is_matrix_add(&a.left, &a.right, given_arg)
            }
            Obj::MatrixSub(ref a) => {
                self.match_arg_when_left_is_matrix_sub(&a.left, &a.right, given_arg)
            }
            Obj::MatrixMul(ref a) => {
                self.match_arg_when_left_is_matrix_mul(&a.left, &a.right, given_arg)
            }
            Obj::MatrixScalarMul(ref a) => {
                self.match_arg_when_left_is_matrix_scalar_mul(&a.scalar, &a.matrix, given_arg)
            }
            Obj::MatrixPow(ref a) => {
                self.match_arg_when_left_is_matrix_pow(&a.base, &a.exponent, given_arg)
            }
            Obj::Sub(ref a) => self.match_arg_when_left_is_sub(&a.left, &a.right, given_arg),
            Obj::Mul(ref a) => self.match_arg_when_left_is_mul(&a.left, &a.right, given_arg),
            Obj::Div(ref a) => self.match_arg_when_left_is_div(&a.left, &a.right, given_arg),
            Obj::Mod(ref a) => self.match_arg_when_left_is_mod(&a.left, &a.right, given_arg),
            Obj::Pow(ref a) => self.match_arg_when_left_is_pow(&a.base, &a.exponent, given_arg),
            Obj::Abs(ref a) => self.match_arg_when_left_is_abs(a.arg.as_ref(), given_arg),
            Obj::Sqrt(ref a) => self.match_arg_when_left_is_sqrt(a.arg.as_ref(), given_arg),
            Obj::Log(ref a) => self.match_arg_when_left_is_log(&a.base, &a.arg, given_arg),
            Obj::Max(ref a) => self.match_arg_when_left_is_max(&a.left, &a.right, given_arg),
            Obj::Min(ref a) => self.match_arg_when_left_is_min(&a.left, &a.right, given_arg),
            Obj::Union(ref a) => self.match_arg_when_left_is_union(&a.left, &a.right, given_arg),
            Obj::Intersect(ref a) => {
                self.match_arg_when_left_is_intersect(&a.left, &a.right, given_arg)
            }
            Obj::SetMinus(ref a) => {
                self.match_arg_when_left_is_set_minus(&a.left, &a.right, given_arg)
            }
            Obj::SetDiff(ref a) => {
                self.match_arg_when_left_is_set_diff(&a.left, &a.right, given_arg)
            }
            Obj::Cup(ref a) => self.match_arg_when_left_is_cup(&a.left, given_arg),
            Obj::Cap(ref a) => self.match_arg_when_left_is_cap(&a.left, given_arg),
            Obj::ListSet(ref left) => self.match_arg_when_left_is_list_set(&left.list, given_arg),
            Obj::SetBuilder(ref left) => self.match_arg_when_left_is_set_builder(left, given_arg),
            Obj::FnSet(ref left) => self.match_arg_when_left_is_fn_set_with_params(left, given_arg),
            Obj::AnonymousFn(ref left) => {
                self.match_arg_when_left_is_anonymous_fn_with_params(left, given_arg)
            }
            Obj::StandardSet(StandardSet::NPos) => self.match_arg_when_left_is_n_pos_obj(given_arg),
            Obj::StandardSet(StandardSet::N) => self.match_arg_when_left_is_n_obj(given_arg),
            Obj::StandardSet(StandardSet::Q) => self.match_arg_when_left_is_q_obj(given_arg),
            Obj::StandardSet(StandardSet::Z) => self.match_arg_when_left_is_z_obj(given_arg),
            Obj::StandardSet(StandardSet::R) => self.match_arg_when_left_is_r_obj(given_arg),
            Obj::Cart(ref left) => self.match_arg_when_left_is_cart(&left.args, given_arg),
            Obj::CartDim(ref left) => {
                self.match_arg_when_left_is_cart_dim(left.set.as_ref(), given_arg)
            }
            Obj::Proj(ref left) => {
                self.match_arg_when_left_is_proj(left.set.as_ref(), left.dim.as_ref(), given_arg)
            }
            Obj::TupleDim(ref left) => {
                self.match_arg_when_left_is_dim(left.arg.as_ref(), given_arg)
            }
            Obj::Tuple(ref left) => self.match_arg_when_left_is_tuple(&left.args, given_arg),
            Obj::FiniteSeqListObj(ref left) => {
                self.match_arg_when_left_is_finite_seq_list(&left.objs, given_arg)
            }
            Obj::Count(ref left) => self.match_arg_when_left_is_count(left.set.as_ref(), given_arg),
            Obj::Sum(ref left) => self.match_arg_when_left_is_sum(
                left.start.as_ref(),
                left.end.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::Product(ref left) => self.match_arg_when_left_is_product(
                left.start.as_ref(),
                left.end.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::Range(ref left) => {
                self.match_arg_when_left_is_range(left.start.as_ref(), left.end.as_ref(), given_arg)
            }
            Obj::ClosedRange(ref left) => self.match_arg_when_left_is_closed_range(
                left.start.as_ref(),
                left.end.as_ref(),
                given_arg,
            ),
            Obj::IntervalObj(ref left) => self.match_arg_when_left_is_interval(left, given_arg),
            Obj::OneSideInfinityIntervalObj(ref left) => {
                self.match_arg_when_left_is_one_side_infinity_interval(left, given_arg)
            }
            Obj::FiniteSeqSet(ref left) => self.match_arg_when_left_is_finite_seq_set(
                left.set.as_ref(),
                left.n.as_ref(),
                given_arg,
            ),
            Obj::SeqSet(ref left) => {
                self.match_arg_when_left_is_seq_set(left.set.as_ref(), given_arg)
            }
            Obj::MatrixListObj(ref left) => {
                self.match_arg_when_left_is_matrix_list(&left.rows, given_arg)
            }
            Obj::MatrixSet(ref left) => self.match_arg_when_left_is_matrix_set(
                left.set.as_ref(),
                left.row_len.as_ref(),
                left.col_len.as_ref(),
                given_arg,
            ),
            Obj::PowerSet(ref left) => {
                self.match_arg_when_left_is_power_set(left.set.as_ref(), given_arg)
            }
            Obj::Choose(ref left) => {
                self.match_arg_when_left_is_choose(left.set.as_ref(), given_arg)
            }
            Obj::ObjAtIndex(ref left) => self.match_arg_when_left_is_obj_at_index(
                left.obj.as_ref(),
                left.index.as_ref(),
                given_arg,
            ),
            Obj::StandardSet(StandardSet::QPos) => self.match_arg_when_left_is_q_pos(given_arg),
            Obj::StandardSet(StandardSet::RPos) => self.match_arg_when_left_is_r_pos(given_arg),
            Obj::StandardSet(StandardSet::QNeg) => self.match_arg_when_left_is_q_neg(given_arg),
            Obj::StandardSet(StandardSet::ZNeg) => self.match_arg_when_left_is_z_neg(given_arg),
            Obj::StandardSet(StandardSet::RNeg) => self.match_arg_when_left_is_r_neg(given_arg),
            Obj::StandardSet(StandardSet::QNz) => self.match_arg_when_left_is_q_nz(given_arg),
            Obj::StandardSet(StandardSet::ZNz) => self.match_arg_when_left_is_z_nz(given_arg),
            Obj::StandardSet(StandardSet::RNz) => self.match_arg_when_left_is_r_nz(given_arg),
            Obj::StructObj(known) => match given_arg {
                Obj::StructObj(given) => {
                    if known.name.to_string() != given.name.to_string() {
                        return Ok(None);
                    }
                    self.match_arg_vec_then_merge(&known.params, &given.params)
                }
                _ => Ok(None),
            },
            Obj::ObjAsStructInstanceWithFieldAccess(known) => match given_arg {
                Obj::ObjAsStructInstanceWithFieldAccess(given) => {
                    if known.struct_obj.name.to_string() != given.struct_obj.name.to_string()
                        || known.field_name != given.field_name
                    {
                        return Ok(None);
                    }
                    let params_result = self.match_arg_vec_then_merge(
                        &known.struct_obj.params,
                        &given.struct_obj.params,
                    )?;
                    let obj_result = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        known.obj.as_ref(),
                        given.obj.as_ref(),
                    )?;
                    match (params_result, obj_result) {
                        (Some(params_map), Some(obj_map)) => {
                            Ok(self.merge_arg_match_maps(params_map, obj_map))
                        }
                        _ => Ok(None),
                    }
                }
                _ => Ok(None),
            },
            Obj::InstantiatedTemplateObj(known) => match given_arg {
                Obj::InstantiatedTemplateObj(given) => {
                    if known.template_name != given.template_name {
                        return Ok(None);
                    }
                    self.match_arg_vec_then_merge(&known.args, &given.args)
                }
                _ => Ok(None),
            },
            Obj::Atom(AtomObj::Forall(ref p)) => {
                self.match_arg_when_left_is_forall_param(p, given_arg)
            }
            Obj::Atom(AtomObj::Def(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::Exist(ref p)) => match given_arg {
                Obj::Atom(AtomObj::Exist(_)) => {
                    let mut m = HashMap::new();
                    m.insert(p.name.clone(), given_arg.clone());
                    Ok(Some(m))
                }
                _ => {
                    if p.to_string() != given_arg.to_string() {
                        return Ok(None);
                    }
                    Ok(Some(HashMap::new()))
                }
            },
            Obj::Atom(AtomObj::SetBuilder(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::FnSet(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::Induc(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::DefAlgo(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::DefStructField(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
        }
    }

    fn match_arg_when_left_is_forall_param(
        &mut self,
        id_known: &ForallFreeParamObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut map = HashMap::new();
        map.insert(id_known.name.clone(), given_arg.clone());
        Ok(Some(map))
    }

    fn match_arg_when_left_is_identifier_with_mod(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Atom(AtomObj::IdentifierWithMod(_)) => {
                self.match_arg_type_not_implemented("IdentifierWithMod")
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_obj(
        &mut self,
        left: &FnObj,
        right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match right {
            Obj::FnObj(ref right_fn) => {
                // body lengths must match
                if left.body.len() != right_fn.body.len() {
                    return Ok(None);
                }

                let left_head: Obj = left.head.as_ref().clone().into();
                let right_head: Obj = right_fn.head.as_ref().clone().into();

                // heads must match
                let head_match = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    &left_head,
                    &right_head,
                )?;
                let mut head_map = match head_match {
                    Some(m) => m,
                    None => return Ok(None),
                };

                for (left_row, right_row) in left.body.iter().zip(right_fn.body.iter()) {
                    if left_row.len() != right_row.len() {
                        return Ok(None);
                    }
                    for (left_arg, right_arg) in left_row.iter().zip(right_row.iter()) {
                        let sub_map = match self
                            .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                                left_arg.as_ref(),
                                right_arg.as_ref(),
                            )? {
                            Some(m) => m,
                            None => return Ok(None),
                        };
                        if !self.merge_arg_match_map_into(&mut head_map, sub_map) {
                            return Ok(None);
                        }
                    }
                }

                Ok(Some(head_map))
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_number(
        &mut self,
        left: &Number,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if !given_arg.evaluate_to_normalized_decimal_number().is_some() {
            return Ok(None);
        }
        let left_obj: Obj = left.clone().into();
        if left_obj.two_objs_can_be_calculated_and_equal_by_calculation(given_arg) {
            Ok(Some(HashMap::new()))
        } else {
            Ok(None)
        }
    }

    fn match_arg_when_left_is_matrix_add(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixAdd(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_sub(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixSub(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_mul(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixMul(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_scalar_mul(
        &mut self,
        left_scalar: &Obj,
        left_matrix: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixScalarMul(ref g) => {
                self.match_arg_binary_then_merge(left_scalar, left_matrix, &g.scalar, &g.matrix)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_pow(
        &mut self,
        left_base: &Obj,
        left_exp: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixPow(ref g) => {
                self.match_arg_binary_then_merge(left_base, left_exp, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_add(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Add(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(left_left_number) = left_left {
                    let new_given = Sub::new(given_arg.clone(), left_left_number.clone().into());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right,
                        &new_given.into(),
                    );
                } else if let Obj::Number(left_right_number) = left_right {
                    let new_given = Sub::new(given_arg.clone(), left_right_number.clone().into());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    fn match_arg_when_left_is_sub(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sub(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(right_number) = left_right {
                    let new_given = Add::new(right_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else if let Obj::Number(left_left_number) = left_left {
                    let new_given = Sub::new(left_left_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    fn match_arg_when_left_is_mul(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Mul(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                let neg_one: Obj = Number::new("-1".to_string()).into();
                let known_left_is_neg_one = match left_left {
                    Obj::Number(n) => {
                        let left_obj: Obj = n.clone().into();
                        "-1".to_string() == left_obj.to_string()
                    }
                    _ => false,
                };
                if known_left_is_neg_one {
                    let synthetic: Obj = Mul::new(neg_one, given_arg.clone()).into();
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right, &synthetic,
                    );
                } else {
                    if let Obj::Number(n) = left_left {
                        if n.normalized_value == "0".to_string() {
                            return Ok(None);
                        } else {
                            let synthetic: Obj =
                                Div::new(given_arg.clone(), n.clone().into()).into();
                            return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                                left_right, &synthetic,
                            );
                        }
                    } else if let Obj::Number(left_right_number) = left_right {
                        let new_given =
                            Div::new(given_arg.clone(), left_right_number.clone().into());
                        return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                            left_left,
                            &new_given.into(),
                        );
                    } else {
                        return Ok(None);
                    }
                }
            }
        }
    }

    fn match_arg_when_left_is_div(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Div(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(left_right_number) = left_right {
                    let new_given = Mul::new(left_right_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    fn match_arg_when_left_is_mod(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Mod(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_pow(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Pow(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_abs(
        &mut self,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Abs(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_arg, &g.arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_sqrt(
        &mut self,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sqrt(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_arg, &g.arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_log(
        &mut self,
        left_base: &Obj,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Log(ref g) => {
                self.match_arg_binary_then_merge(left_base, left_arg, &g.base, &g.arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_max(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Max(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_min(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Min(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_union(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Union(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_intersect(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Intersect(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_minus(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SetMinus(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_diff(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SetDiff(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cup(
        &mut self,
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cup(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cap(
        &mut self,
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cap(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    /// Match two pairs (left_left, given_left) and (left_right, given_right); if either returns None, return None; else merge maps and return Some(merged).
    fn match_arg_binary_then_merge(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let left_res =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, given_left)?;
        let map1 = match left_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let right_res =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_right, given_right)?;
        let map2 = match right_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let merged = self.merge_arg_match_maps(map1, map2);
        Ok(merged)
    }

    fn match_arg_ternary_then_merge(
        &mut self,
        a1: &Obj,
        a2: &Obj,
        a3: &Obj,
        b1: &Obj,
        b2: &Obj,
        b3: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let m12 = self.match_arg_binary_then_merge(a1, a2, b1, b2)?;
        let map12 = match m12 {
            Some(m) => m,
            None => return Ok(None),
        };
        let m3 = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(a3, b3)?;
        let map3 = match m3 {
            Some(m) => m,
            None => return Ok(None),
        };
        Ok(self.merge_arg_match_maps(map12, map3))
    }

    /// Merge `from` into `into`. Returns `false` when a key is already bound to a different object.
    fn merge_arg_match_map_into(
        &mut self,
        into: &mut HashMap<String, Obj>,
        from: HashMap<String, Obj>,
    ) -> bool {
        for (k, v) in from {
            if let Some(existing) = into.get(&k) {
                if existing.to_string() != v.to_string()
                    && !existing.two_objs_can_be_calculated_and_equal_by_calculation(&v)
                {
                    return false;
                }
            }
            into.insert(k, v);
        }
        true
    }

    fn merge_arg_match_maps(
        &mut self,
        mut map1: HashMap<String, Obj>,
        map2: HashMap<String, Obj>,
    ) -> Option<HashMap<String, Obj>> {
        if !self.merge_arg_match_map_into(&mut map1, map2) {
            return None;
        }
        Some(map1)
    }

    /// Zip known/given argument pairs of equal length; merge substitution maps from each recursive match.
    fn match_arg_pairs_then_merge<'a>(
        &mut self,
        pairs: impl Iterator<Item = (&'a Obj, &'a Obj)>,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (left_elem, given_elem) in pairs {
            let sub_map = match self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_elem, given_elem)?
            {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_boxed_arg_vec_then_merge(
        &mut self,
        left_elements: &[Box<Obj>],
        given_elements: &[Box<Obj>],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left_elements.len() != given_elements.len() {
            return Ok(None);
        }
        self.match_arg_pairs_then_merge(
            left_elements
                .iter()
                .zip(given_elements.iter())
                .map(|(l, g)| (l.as_ref(), g.as_ref())),
        )
    }

    fn match_arg_vec_then_merge(
        &mut self,
        left: &[Obj],
        given: &[Obj],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.len() != given.len() {
            return Ok(None);
        }
        self.match_arg_pairs_then_merge(left.iter().zip(given.iter()).map(|(l, g)| (l, g)))
    }

    fn match_arg_matrix_rows_then_merge(
        &mut self,
        left_rows: &[Vec<Box<Obj>>],
        given_rows: &[Vec<Box<Obj>>],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left_rows.len() != given_rows.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lr, gr) in left_rows.iter().zip(given_rows.iter()) {
            let sub_map = match self.match_boxed_arg_vec_then_merge(lr, gr)? {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_list_set(
        &mut self,
        left_list: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ListSet(ref given) => self.match_boxed_arg_vec_then_merge(left_list, &given.list),
            _ => Ok(None),
        }
    }

    fn match_arg_or_and_chain_atomic_fact_in_known_forall(
        &mut self,
        left: &OrAndChainAtomicFact,
        given: &OrAndChainAtomicFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Some(pairs) =
            Self::_verify_or_and_chain_atomic_facts_the_same_type_and_return_matched_args(
                left, given,
            )?
        else {
            return Ok(None);
        };
        self.match_arg_pairs_then_merge(pairs.iter().map(|(l, g)| (l, g)))
    }

    fn match_arg_when_left_is_set_builder(
        &mut self,
        left: &SetBuilder,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::SetBuilder(given) = given_arg else {
            return Ok(None);
        };
        if left.param != given.param {
            return Ok(None);
        }
        let Some(mut merged) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.param_set.as_ref(),
            given.param_set.as_ref(),
        )?
        else {
            return Ok(None);
        };
        if left.facts.len() != given.facts.len() {
            return Ok(None);
        }
        for (lf, gf) in left.facts.iter().zip(given.facts.iter()) {
            let Some(fact_map) = self.match_arg_or_and_chain_atomic_fact_in_known_forall(lf, gf)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let verify_state = VerifyState::new_with_final_round(false);
        for value in merged.values() {
            if self
                .verify_obj_well_defined_and_store_cache(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_fn_set_with_params(
        &mut self,
        left: &FnSet,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FnSet(given) = given_arg else {
            return Ok(None);
        };
        if left.body.params_def_with_set.len() != given.body.params_def_with_set.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lg, gg) in left
            .body
            .params_def_with_set
            .iter()
            .zip(given.body.params_def_with_set.iter())
        {
            if lg.params != gg.params {
                return Ok(None);
            }
            let Some(m) = self.match_fn_param_group_type_in_known_forall_with_given(lg, gg)? else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, m) {
                return Ok(None);
            }
        }
        if left.body.dom_facts.len() != given.body.dom_facts.len() {
            return Ok(None);
        }
        for (lf, gf) in left.body.dom_facts.iter().zip(given.body.dom_facts.iter()) {
            let Some(fact_map) = self.match_arg_or_and_chain_atomic_fact_in_known_forall(lf, gf)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let Some(ret_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.body.ret_set.as_ref(),
            given.body.ret_set.as_ref(),
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, ret_map) {
            return Ok(None);
        }
        let verify_state = VerifyState::new_with_final_round(false);
        for value in merged.values() {
            if self
                .verify_obj_well_defined_and_store_cache(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_anonymous_fn_with_params(
        &mut self,
        left: &AnonymousFn,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::AnonymousFn(given) = given_arg else {
            return Ok(None);
        };
        if left.body.params_def_with_set.len() != given.body.params_def_with_set.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lg, gg) in left
            .body
            .params_def_with_set
            .iter()
            .zip(given.body.params_def_with_set.iter())
        {
            if lg.params != gg.params {
                return Ok(None);
            }
            let Some(m) = self.match_fn_param_group_type_in_known_forall_with_given(lg, gg)? else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, m) {
                return Ok(None);
            }
        }
        if left.body.dom_facts.len() != given.body.dom_facts.len() {
            return Ok(None);
        }
        for (lf, gf) in left.body.dom_facts.iter().zip(given.body.dom_facts.iter()) {
            let Some(fact_map) = self.match_arg_or_and_chain_atomic_fact_in_known_forall(lf, gf)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let Some(ret_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.body.ret_set.as_ref(),
            given.body.ret_set.as_ref(),
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, ret_map) {
            return Ok(None);
        }
        let Some(eq_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.equal_to.as_ref(),
            given.equal_to.as_ref(),
        )?
        else {
            let Some(eq_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
                left.equal_to.as_ref(),
                given.equal_to.as_ref(),
                &given.body,
            )?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, eq_map) {
                return Ok(None);
            }
            let verify_state = VerifyState::new_with_final_round(false);
            for value in merged.values() {
                if self
                    .verify_obj_well_defined_and_store_cache(value, &verify_state)
                    .is_err()
                {
                    return Ok(None);
                }
            }
            return Ok(Some(merged));
        };
        if !self.merge_arg_match_map_into(&mut merged, eq_map) {
            return Ok(None);
        }
        let verify_state = VerifyState::new_with_final_round(false);
        for value in merged.values() {
            if self
                .verify_obj_well_defined_and_store_cache(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_in_anonymous_fn_body_with_given_arg(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if let Some(existing_match) =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(known_arg, given_arg)?
        {
            return Ok(Some(existing_match));
        }
        if let Some(function_param_match) = self
            .match_forall_function_param_application_as_anonymous_fn(
                known_arg,
                given_arg,
                anonymous_fn_body,
            )?
        {
            return Ok(Some(function_param_match));
        }

        match (known_arg, given_arg) {
            (Obj::FnObj(left), Obj::FnObj(given)) => {
                self.match_fn_obj_in_anonymous_fn_body(left, given, anonymous_fn_body)
            }
            (Obj::Add(left), Obj::Add(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Sub(left), Obj::Sub(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Mul(left), Obj::Mul(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Div(left), Obj::Div(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Mod(left), Obj::Mod(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Pow(left), Obj::Pow(given)) => self.match_binary_in_anonymous_fn_body(
                left.base.as_ref(),
                left.exponent.as_ref(),
                given.base.as_ref(),
                given.exponent.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::MatrixAdd(left), Obj::MatrixAdd(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixSub(left), Obj::MatrixSub(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixMul(left), Obj::MatrixMul(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixScalarMul(left), Obj::MatrixScalarMul(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.scalar.as_ref(),
                    left.matrix.as_ref(),
                    given.scalar.as_ref(),
                    given.matrix.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixPow(left), Obj::MatrixPow(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.base.as_ref(),
                    left.exponent.as_ref(),
                    given.base.as_ref(),
                    given.exponent.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Abs(left), Obj::Abs(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Sqrt(left), Obj::Sqrt(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Log(left), Obj::Log(given)) => self.match_binary_in_anonymous_fn_body(
                left.base.as_ref(),
                left.arg.as_ref(),
                given.base.as_ref(),
                given.arg.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Max(left), Obj::Max(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Min(left), Obj::Min(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Tuple(left), Obj::Tuple(given)) => self.match_boxed_args_in_anonymous_fn_body(
                &left.args,
                &given.args,
                anonymous_fn_body,
            ),
            (Obj::Cart(left), Obj::Cart(given)) => self.match_boxed_args_in_anonymous_fn_body(
                &left.args,
                &given.args,
                anonymous_fn_body,
            ),
            (Obj::ListSet(left), Obj::ListSet(given)) => self
                .match_boxed_args_in_anonymous_fn_body(&left.list, &given.list, anonymous_fn_body),
            (Obj::FiniteSeqListObj(left), Obj::FiniteSeqListObj(given)) => self
                .match_boxed_args_in_anonymous_fn_body(&left.objs, &given.objs, anonymous_fn_body),
            _ => Ok(None),
        }
    }

    fn match_fn_obj_in_anonymous_fn_body(
        &mut self,
        left: &FnObj,
        given: &FnObj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.body.len() != given.body.len() {
            return Ok(None);
        }
        let left_head: Obj = left.head.as_ref().clone().into();
        let given_head: Obj = given.head.as_ref().clone().into();
        let Some(mut merged) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            &left_head,
            &given_head,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };

        for (left_row, given_row) in left.body.iter().zip(given.body.iter()) {
            if left_row.len() != given_row.len() {
                return Ok(None);
            }
            let Some(row_map) =
                self.match_boxed_args_in_anonymous_fn_body(left_row, given_row, anonymous_fn_body)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, row_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_binary_in_anonymous_fn_body(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Some(mut merged) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            left_left,
            given_left,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };
        let Some(right_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            left_right,
            given_right,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, right_map) {
            return Ok(None);
        }
        Ok(Some(merged))
    }

    fn match_boxed_args_in_anonymous_fn_body(
        &mut self,
        left: &[Box<Obj>],
        given: &[Box<Obj>],
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.len() != given.len() {
            return Ok(None);
        }
        let mut merged = HashMap::new();
        for (left_arg, given_arg) in left.iter().zip(given.iter()) {
            let Some(sub_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
                left_arg.as_ref(),
                given_arg.as_ref(),
                anonymous_fn_body,
            )?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_forall_function_param_application_as_anonymous_fn(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FnObj(fn_obj) = known_arg else {
            return Ok(None);
        };
        let FnObjHead::Forall(forall_param) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        if !Self::fn_obj_applies_to_exact_anonymous_fn_params(fn_obj, anonymous_fn_body) {
            return Ok(None);
        }

        let anonymous_fn = AnonymousFn::new(
            anonymous_fn_body.params_def_with_set.clone(),
            anonymous_fn_body.dom_facts.clone(),
            (*anonymous_fn_body.ret_set).clone(),
            given_arg.clone(),
        )?;
        let mut map = HashMap::new();
        map.insert(forall_param.name.clone(), anonymous_fn.into());
        Ok(Some(map))
    }

    fn fn_obj_applies_to_exact_anonymous_fn_params(
        fn_obj: &FnObj,
        anonymous_fn_body: &FnSetBody,
    ) -> bool {
        let expected_param_names = anonymous_fn_body.get_params();
        let expected_len = expected_param_names.len();
        let actual_args_count: usize = fn_obj.body.iter().map(|row| row.len()).sum();
        if actual_args_count != expected_len {
            return false;
        }

        let mut flat_index = 0;
        for row in fn_obj.body.iter() {
            for arg in row.iter() {
                let expected = obj_for_bound_param_in_scope(
                    expected_param_names[flat_index].clone(),
                    ParamObjType::FnSet,
                );
                if arg.to_string() != expected.to_string() {
                    return false;
                }
                flat_index += 1;
            }
        }
        true
    }

    fn match_fn_param_group_type_in_known_forall_with_given(
        &mut self,
        left: &ParamGroupWithSet,
        given: &ParamGroupWithSet,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.set_obj(),
            given.set_obj(),
        )
    }

    fn standard_set_is_subset_eq(subset: &StandardSet, superset: &StandardSet) -> bool {
        match (subset, superset) {
            (StandardSet::NPos, StandardSet::NPos)
            | (StandardSet::NPos, StandardSet::N)
            | (StandardSet::NPos, StandardSet::Z)
            | (StandardSet::NPos, StandardSet::Q)
            | (StandardSet::NPos, StandardSet::R)
            | (StandardSet::NPos, StandardSet::QPos)
            | (StandardSet::NPos, StandardSet::RPos)
            | (StandardSet::NPos, StandardSet::ZNz)
            | (StandardSet::NPos, StandardSet::QNz)
            | (StandardSet::NPos, StandardSet::RNz)
            | (StandardSet::N, StandardSet::N)
            | (StandardSet::N, StandardSet::Z)
            | (StandardSet::N, StandardSet::Q)
            | (StandardSet::N, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::ZNeg)
            | (StandardSet::ZNeg, StandardSet::Z)
            | (StandardSet::ZNeg, StandardSet::Q)
            | (StandardSet::ZNeg, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::QNeg)
            | (StandardSet::ZNeg, StandardSet::RNeg)
            | (StandardSet::ZNeg, StandardSet::ZNz)
            | (StandardSet::ZNeg, StandardSet::QNz)
            | (StandardSet::ZNeg, StandardSet::RNz)
            | (StandardSet::ZNz, StandardSet::ZNz)
            | (StandardSet::ZNz, StandardSet::Z)
            | (StandardSet::ZNz, StandardSet::Q)
            | (StandardSet::ZNz, StandardSet::R)
            | (StandardSet::ZNz, StandardSet::QNz)
            | (StandardSet::ZNz, StandardSet::RNz)
            | (StandardSet::Z, StandardSet::Z)
            | (StandardSet::Z, StandardSet::Q)
            | (StandardSet::Z, StandardSet::R)
            | (StandardSet::QPos, StandardSet::QPos)
            | (StandardSet::QPos, StandardSet::Q)
            | (StandardSet::QPos, StandardSet::R)
            | (StandardSet::QPos, StandardSet::RPos)
            | (StandardSet::QPos, StandardSet::QNz)
            | (StandardSet::QPos, StandardSet::RNz)
            | (StandardSet::QNeg, StandardSet::QNeg)
            | (StandardSet::QNeg, StandardSet::Q)
            | (StandardSet::QNeg, StandardSet::R)
            | (StandardSet::QNeg, StandardSet::RNeg)
            | (StandardSet::QNeg, StandardSet::QNz)
            | (StandardSet::QNeg, StandardSet::RNz)
            | (StandardSet::QNz, StandardSet::QNz)
            | (StandardSet::QNz, StandardSet::Q)
            | (StandardSet::QNz, StandardSet::R)
            | (StandardSet::QNz, StandardSet::RNz)
            | (StandardSet::Q, StandardSet::Q)
            | (StandardSet::Q, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RPos)
            | (StandardSet::RPos, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RNz)
            | (StandardSet::RNeg, StandardSet::RNeg)
            | (StandardSet::RNeg, StandardSet::R)
            | (StandardSet::RNeg, StandardSet::RNz)
            | (StandardSet::RNz, StandardSet::RNz)
            | (StandardSet::RNz, StandardSet::R)
            | (StandardSet::R, StandardSet::R) => true,
            _ => false,
        }
    }

    fn match_arg_when_left_is_n_pos_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_n_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::N) | Obj::StandardSet(StandardSet::NPos) => {
                self.match_arg_same_type(given_arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::R)
            | Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::RNeg)
            | Obj::StandardSet(StandardSet::RNz)
            | Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart(
        &mut self,
        left_args: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cart(ref given) => self.match_boxed_arg_vec_then_merge(left_args, &given.args),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart_dim(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::CartDim(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_proj(
        &mut self,
        left_set: &Obj,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Proj(ref given) => self.match_arg_binary_then_merge(
                left_set,
                left_dim,
                given.set.as_ref(),
                given.dim.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_dim(
        &mut self,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::TupleDim(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_dim,
                    given.arg.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_tuple(
        &mut self,
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Tuple(ref given) => {
                self.match_boxed_arg_vec_then_merge(left_elements, &given.args)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_finite_seq_list(
        &mut self,
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSeqListObj(ref given) => {
                self.match_boxed_arg_vec_then_merge(left_elements, &given.objs)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_count(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Count(ref given) => self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_set,
                given.set.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_range(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Range(ref given) => self.match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_sum(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sum(ref g) => self.match_arg_ternary_then_merge(
                left_start,
                left_end,
                left_func,
                g.start.as_ref(),
                g.end.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_product(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Product(ref g) => self.match_arg_ternary_then_merge(
                left_start,
                left_end,
                left_func,
                g.start.as_ref(),
                g.end.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_closed_range(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ClosedRange(ref given) => self.match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_interval(
        &mut self,
        left: &IntervalObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::IntervalObj(given) = given_arg else {
            return Ok(None);
        };
        if left.left_closed() != given.left_closed() || left.right_closed() != given.right_closed()
        {
            return Ok(None);
        }
        self.match_arg_binary_then_merge(left.start(), left.end(), given.start(), given.end())
    }

    fn match_arg_when_left_is_one_side_infinity_interval(
        &mut self,
        left: &OneSideInfinityIntervalObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::OneSideInfinityIntervalObj(given) = given_arg else {
            return Ok(None);
        };
        if !left.same_kind_as(given) {
            return Ok(None);
        }
        self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left.start(), given.start())
    }

    fn match_arg_when_left_is_finite_seq_set(
        &mut self,
        left_set: &Obj,
        left_n: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSeqSet(ref given) => self.match_arg_binary_then_merge(
                left_set,
                left_n,
                given.set.as_ref(),
                given.n.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_seq_set(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SeqSet(ref given) => self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_set,
                given.set.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_list(
        &mut self,
        left_rows: &[Vec<Box<Obj>>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixListObj(ref given) => {
                self.match_arg_matrix_rows_then_merge(left_rows, &given.rows)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_set(
        &mut self,
        left_set: &Obj,
        left_row_len: &Obj,
        left_col_len: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixSet(ref given) => self.match_arg_ternary_then_merge(
                left_set,
                left_row_len,
                left_col_len,
                given.set.as_ref(),
                given.row_len.as_ref(),
                given.col_len.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_power_set(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::PowerSet(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_choose(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Choose(ref given) => self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_set,
                given.set.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_obj_at_index(
        &mut self,
        left_obj: &Obj,
        left_index: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ObjAtIndex(ref given) => self.match_arg_binary_then_merge(
                left_obj,
                left_index,
                given.obj.as_ref(),
                given.index.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_pos(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::QPos) | Obj::StandardSet(StandardSet::NPos) => {
                self.match_arg_same_type(given_arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_pos(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_neg(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::QNeg) | Obj::StandardSet(StandardSet::ZNeg) => {
                self.match_arg_same_type(given_arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_neg(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::ZNeg) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_neg(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::RNeg)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNeg) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_nz(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_nz(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_nz(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::RNz)
            | Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::RNeg)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_same_type(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut map = HashMap::new();
        map.insert(given_arg.to_string(), given_arg.clone());
        Ok(Some(map))
    }

    fn match_arg_type_not_implemented(
        &mut self,
        obj_type_name: &str,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let _ = obj_type_name;
        Ok(None)
    }
}

fn atomic_fact_in_forall_lookup_arg_shape_keys(
    atomic_fact: &AtomicFact,
) -> Vec<AtomicFactInForallArgShapeKey> {
    let exact_key = atomic_fact_in_forall_arg_shape_key(atomic_fact);
    let forall_param_key_part = (ObjKind::ForallFreeParam, String::new());
    let mut keys = Vec::new();
    push_atomic_fact_in_forall_arg_shape_key_if_new(&mut keys, exact_key.clone());

    for index in 0..exact_key.len() {
        let known_keys_count = keys.len();
        for key_index in 0..known_keys_count {
            let mut key = keys[key_index].clone();
            key[index] = forall_param_key_part.clone();
            push_atomic_fact_in_forall_arg_shape_key_if_new(&mut keys, key);
        }
    }

    keys
}

fn push_atomic_fact_in_forall_arg_shape_key_if_new(
    keys: &mut Vec<AtomicFactInForallArgShapeKey>,
    key: AtomicFactInForallArgShapeKey,
) {
    if !keys.contains(&key) {
        keys.push(key);
    }
}
