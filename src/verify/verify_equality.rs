use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_objs_are_equal(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact.line_file.clone(),
            verify_state,
        )
    }

    pub fn verify_objs_are_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(done) =
            self.try_verify_function_equality_from_known_fn_eq(left, right, line_file.clone())?
        {
            return Ok(done);
        }

        let builtin_goal: AtomicFact =
            EqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let mut result = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                &builtin_goal,
            )?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_atomic_fact_with_builtin_strategy(&builtin_goal)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_equality_with_known_equalities(
            left,
            right,
            line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verified_by_arg_to_arg = self
                .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                    left,
                    right,
                    verify_state,
                    line_file.clone(),
                )?;
            if verified_by_arg_to_arg {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        EqualFact::new(left.clone(), right.clone(), line_file.clone()).into(),
                        same_shape_and_equal_args_reason(left, right),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if verify_state.is_round_0() && verify_state.equality_can_use_known_forall {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();
            result = self.verify_atomic_fact_with_known_forall(
                &EqualFact::new(left.clone(), right.clone(), line_file.clone()).into(),
                &verify_state_add_one_round,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    // Function extensionality bridge from an already proved `$fn_eq`.
    // Example: after `$fn_eq(f, g)`, prove the ordinary equality `f = g`.
    fn try_verify_function_equality_from_known_fn_eq(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let direct = FnEqualFact::new(left.clone(), right.clone(), line_file.clone());
        if let Some(done) =
            self.try_verify_function_equality_from_one_known_fn_eq(left, right, &direct)?
        {
            return Ok(Some(done));
        }

        let reversed = FnEqualFact::new(right.clone(), left.clone(), line_file.clone());
        self.try_verify_function_equality_from_one_known_fn_eq(left, right, &reversed)
    }

    fn try_verify_function_equality_from_one_known_fn_eq(
        &mut self,
        left: &Obj,
        right: &Obj,
        fn_eq_fact: &FnEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let fn_eq_atomic: AtomicFact = fn_eq_fact.clone().into();
        let fn_eq_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&fn_eq_atomic)?;
        if !fn_eq_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), fn_eq_fact.line_file.clone()).into(),
                "function equality from known fn_eq".to_string(),
                vec![fn_eq_result],
            )
            .into(),
        ))
    }

    pub(crate) fn verify_equality_with_known_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_string = obj_equality_key(left);
        let right_string = obj_equality_key(right);

        if verify_state.round == 0 && self.known_equality_candidate_replay_depth == 0 {
            let known_pairs = self.collect_known_equality_pairs_from_envs(
                &left_string,
                &right_string,
                left,
                right,
            );
            for (known_left, known_right) in known_pairs {
                self.known_equality_candidate_replay_depth += 1;
                let candidate_result = self.try_verify_known_equality_candidates_with_builtin_root(
                    left,
                    right,
                    line_file.clone(),
                    verify_state,
                    known_left.as_ref(),
                    known_right.as_ref(),
                );
                self.known_equality_candidate_replay_depth -= 1;
                if let Some(result) = candidate_result? {
                    return Ok(result);
                }
            }
        }

        if let Some(done) = self.try_verify_objs_equal_via_user_defined_fn_definition_substitution(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        Ok((StmtUnknown::new()).into())
    }

    fn try_verify_known_equality_candidates_with_builtin_root(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
        known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
        known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match (known_objs_equal_to_left, known_objs_equal_to_right) {
            (None, None) => Ok(None),
            (Some(left_candidates), None) => {
                for candidate in left_candidates.iter() {
                    if let Some(result) = self.verify_one_equality_candidate_with_builtin_root(
                        candidate,
                        right,
                        line_file.clone(),
                        verify_state,
                    )? {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (None, Some(right_candidates)) => {
                for candidate in right_candidates.iter() {
                    if let Some(result) = self.verify_one_equality_candidate_with_builtin_root(
                        left,
                        candidate,
                        line_file.clone(),
                        verify_state,
                    )? {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (Some(left_candidates), Some(right_candidates)) => {
                for left_candidate in left_candidates.iter() {
                    for right_candidate in right_candidates.iter() {
                        if let Some(result) = self.verify_one_equality_candidate_with_builtin_root(
                            left_candidate,
                            right_candidate,
                            line_file.clone(),
                            verify_state,
                        )? {
                            return Ok(Some(result));
                        }
                    }
                }
                Ok(None)
            }
        }
    }

    fn verify_one_equality_candidate_with_builtin_root(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let candidate: AtomicFact =
            EqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let leaf_result = self
            .verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation(&candidate)?;
        if leaf_result.is_true() {
            return Ok(Some(leaf_result));
        }

        let structural_state = verify_state.new_state_with_round_increased();

        // A named object may be equal to one explicit structure field. Replay that single
        // constructor-decreasing projection with a fresh builtin root. The field rule itself
        // reads only the exact known tuple constructor and does not enumerate other equality
        // candidates. Example: `selected = &Pair{pair}.second`, `pair = (a, b)` proves
        // `selected = b`.
        if matches!(left, Obj::ObjAsStructInstanceWithFieldAccess(_))
            || matches!(right, Obj::ObjAsStructInstanceWithFieldAccess(_))
        {
            let field_result = self
                .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                    &candidate,
                )?;
            if field_result.is_true() {
                return Ok(Some(field_result));
            }
        }

        // A direct builtin replay is useful for small arithmetic representatives such as
        // `0 + q = p`, but unsafe for unreduced function applications: resolving those can
        // repeatedly duplicate stored bodies. Function-shaped candidates use the checked
        // one-step structural path below instead.
        if is_plain_native_arithmetic_candidate(left) && is_plain_native_arithmetic_candidate(right)
        {
            let direct_result = self
                .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                    &candidate,
                )?;
            if direct_result.is_true() {
                return Ok(Some(direct_result));
            }
        }

        if !could_match_after_one_checked_function_unfold(left, right) {
            return Ok(None);
        }

        // Candidate replay is deliberately one structural step. Child argument
        // comparisons use a later round, so they cannot enumerate and expand
        // the same known-equality candidates without a decreasing boundary.
        let mut pairs = Vec::new();
        if matches!(left, Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_)) {
            if let Some(reduced_left) =
                self.unfold_known_fn_application_once(left, &structural_state)?
            {
                pairs.push((reduced_left, right.clone()));
            }
        }
        if matches!(right, Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_)) {
            if let Some(reduced_right) =
                self.unfold_known_fn_application_once(right, &structural_state)?
            {
                pairs.push((left.clone(), reduced_right));
            }
        }

        for (candidate_left, candidate_right) in pairs {
            if !same_arithmetic_shape_with_immediate_fn_application(
                &candidate_left,
                &candidate_right,
            ) {
                continue;
            }

            let structurally_equal = self
                .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                    &candidate_left,
                    &candidate_right,
                    &structural_state,
                    line_file.clone(),
                )?;
            if structurally_equal {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        candidate.clone().into(),
                        "known equality candidate with one-step structural function replay"
                            .to_string(),
                        Vec::new(),
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    /// Stored `have fn` body (`KnownFnInfo.equal_to`): unfold one application and compare.
    fn try_verify_objs_equal_via_user_defined_fn_definition_substitution(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) = self.try_one_side_user_defined_fn_app_equals_other_side(
            left,
            right,
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_one_side_user_defined_fn_app_equals_other_side(
            left,
            right,
            right,
            left,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }
        Ok(None)
    }

    fn try_one_side_user_defined_fn_app_equals_other_side(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let reduced = match self.unfold_known_fn_application_once(application_side, verify_state)? {
            Some(reduced) => reduced,
            None => {
                let Some(set_builder) =
                    self.get_obj_equal_to_set_builder(&application_side.to_string())
                else {
                    return Ok(None);
                };
                set_builder.into()
            }
        };
        if objs_equal_with_nested_binder_alpha_equivalence(&reduced, other_side) {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(statement_left.clone(), statement_right.clone(), line_file)
                        .into(),
                    "one user-defined function unfolding, modulo bound-variable renaming"
                        .to_string(),
                    Vec::new(),
                )
                .into(),
            ));
        }
        let inner = self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
            &EqualFact::new(reduced.clone(), other_side.clone(), line_file.clone()).into(),
        )?;
        if !inner.is_true() {
            return Ok(None);
        }
        let fact: Fact = EqualFact::new(
            statement_left.clone(),
            statement_right.clone(),
            line_file.clone(),
        )
        .into();
        let msg = format!(
            "according to user-defined function `{}` = `{}`",
            application_side, reduced
        );
        let cited = fact.clone();
        let verified_by = VerifiedByResult::cited_fact(fact.clone(), cited, Some(msg));
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_known_fact(fact, verified_by, Vec::new())
                .into(),
        ))
    }

    /// Build equality closures without merging the underlying environments.
    fn collect_known_equality_pairs_from_envs(
        &self,
        left_string: &str,
        right_string: &str,
        left: &Obj,
        right: &Obj,
    ) -> Vec<(Option<Rc<Vec<Obj>>>, Option<Rc<Vec<Obj>>>)> {
        let current_environments = self.iter_environments_from_top().collect::<Vec<_>>();
        let mut pairs = vec![(
            known_equality_class_across_environments(
                &current_environments,
                &[left_string.to_string()],
            ),
            known_equality_class_across_environments(
                &current_environments,
                &[right_string.to_string()],
            ),
        )];
        let mut module_names = self.obj_referenced_module_names(left);
        for module_name in self.obj_referenced_module_names(right) {
            if !module_names
                .iter()
                .any(|existing_module_name| existing_module_name == &module_name)
            {
                module_names.push(module_name);
            }
        }
        for module_name in module_names.iter() {
            let environments = self.imported_module_environments(module_name);
            if environments.is_empty() {
                continue;
            }
            let left_keys =
                equality_lookup_keys_for_module_env(left, left_string, module_name.as_str());
            let right_keys =
                equality_lookup_keys_for_module_env(right, right_string, module_name.as_str());
            pairs.push((
                known_equality_class_across_environments(&environments, &left_keys),
                known_equality_class_across_environments(&environments, &right_keys),
            ));
        }
        pairs
    }

    fn verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        right_left: &Obj,
        right_right: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_left,
            right_left,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_right,
            right_right,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        Ok(true)
    }

    fn verify_unary_objs_are_equal_when_their_only_args_are_equal(
        &mut self,
        left_value: &Obj,
        right_value: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_value,
            right_value,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_true() {
            return Ok(true);
        }
        Ok(false)
    }

    fn verify_function_args_are_equal_for_iterated_operator(
        &mut self,
        left_func: &Obj,
        right_func: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        // Iterated operators such as sum/product compare their summand
        // functions extensionally. Example:
        // `sum(1, n, fn(x Z) Z {f(x)}) = sum(1, n, fn(y Z) Z {f(y)})`.
        if self
            .try_verify_function_equality_from_known_fn_eq(
                left_func,
                right_func,
                equality_line_file.clone(),
            )?
            .is_some()
        {
            return Ok(true);
        }

        self.verify_unary_objs_are_equal_when_their_only_args_are_equal(
            left_func,
            right_func,
            verify_state,
            equality_line_file,
        )
    }

    pub(crate) fn verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        match (left_obj, right_obj) {
            (Obj::Sum(left), Obj::Sum(right)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left.start,
                    &left.end,
                    &right.start,
                    &right.end,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::SumOfFiniteSet(left), Obj::SumOfFiniteSet(right)) => {
                if !self
                    .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        left.set.as_ref(),
                        right.set.as_ref(),
                        verify_state,
                        equality_line_file.clone(),
                    )?
                    .is_true()
                {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::ProductOfFiniteSet(left), Obj::ProductOfFiniteSet(right)) => {
                if !self
                    .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        left.set.as_ref(),
                        right.set.as_ref(),
                        verify_state,
                        equality_line_file.clone(),
                    )?
                    .is_true()
                {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::Product(left), Obj::Product(right)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left.start,
                    &left.end,
                    &right.start,
                    &right.end,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            _ => Self::same_shape_and_corresponding_args_match(
                left_obj,
                right_obj,
                &mut |left_arg, right_arg| {
                    self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        left_arg,
                        right_arg,
                        verify_state,
                        equality_line_file.clone(),
                    )
                    .map(|result| result.is_true())
                },
            ),
        }
    }

    fn verify_two_objs_equal_by_builtin_rules_and_known_equalities(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                &EqualFact::new(
                    left_obj.clone(),
                    right_obj.clone(),
                    equality_line_file.clone(),
                )
                .into(),
            )?;
        if result.is_true() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(
                        left_obj.clone(),
                        right_obj.clone(),
                        equality_line_file.clone(),
                    )
                    .into(),
                    "builtin rules".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        result = self.verify_equality_with_known_equalities(
            left_obj,
            right_obj,
            equality_line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        let verified_by_arg_to_arg = self
            .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                left_obj,
                right_obj,
                verify_state,
                equality_line_file.clone(),
            )?;
        if verified_by_arg_to_arg {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left_obj.clone(), right_obj.clone(), equality_line_file).into(),
                    same_shape_and_equal_args_reason(left_obj, right_obj),
                    Vec::new(),
                ))
                .into(),
            );
        }

        Ok((StmtUnknown::new()).into())
    }
}

fn equality_lookup_keys_for_module_env(
    obj: &Obj,
    default_key: &str,
    module_name: &str,
) -> Vec<String> {
    let mut keys = vec![default_key.to_string()];
    if let Obj::Atom(AtomObj::IdentifierWithMod(identifier)) = obj {
        if identifier.mod_name == module_name {
            keys.push(identifier.name.clone());
        }
    }
    let local_key = default_key.replace(&format!("{}{}", module_name, MOD_SIGN), "");
    if local_key != default_key {
        keys.push(local_key);
    }
    keys
}

fn known_equality_class_across_environments(
    environments: &[&Environment],
    initial_keys: &[String],
) -> Option<Rc<Vec<Obj>>> {
    let mut keys = initial_keys.to_vec();
    let mut objects = Vec::new();
    let mut next_index = 0;
    let mut found_equality = false;

    while next_index < keys.len() {
        let current = keys[next_index].clone();
        next_index += 1;
        for environment in environments {
            let Some((_, equivalent_objects)) = environment.known_equality.get(&current) else {
                continue;
            };
            found_equality = true;
            for object in equivalent_objects.iter() {
                let object_key = obj_equality_key(object);
                if !keys.contains(&object_key) {
                    keys.push(object_key.clone());
                }
                if !objects
                    .iter()
                    .any(|known: &Obj| obj_equality_key(known) == object_key)
                {
                    objects.push(object.clone());
                }
            }
        }
    }

    if found_equality {
        Some(Rc::new(objects))
    } else {
        None
    }
}

fn same_shape_and_equal_args_reason(left_obj: &Obj, right_obj: &Obj) -> String {
    match (left_obj, right_obj) {
        (Obj::FnObj(_), Obj::FnObj(_)) => {
            "the function parts are equal, and the function arguments are equal one by one"
                .to_string()
        }
        _ => "the corresponding builtin-object arguments are equal one by one".to_string(),
    }
}

fn same_arithmetic_shape_with_immediate_fn_application(left: &Obj, right: &Obj) -> bool {
    let has_fn_application = |left_arg: &Obj, right_arg: &Obj| {
        matches!(left_arg, Obj::FnObj(_)) || matches!(right_arg, Obj::FnObj(_))
    };
    match (left, right) {
        (Obj::Add(left), Obj::Add(right)) => {
            has_fn_application(left.left.as_ref(), right.left.as_ref())
                || has_fn_application(left.right.as_ref(), right.right.as_ref())
        }
        (Obj::Sub(left), Obj::Sub(right)) => {
            has_fn_application(left.left.as_ref(), right.left.as_ref())
                || has_fn_application(left.right.as_ref(), right.right.as_ref())
        }
        (Obj::Mul(left), Obj::Mul(right)) => {
            has_fn_application(left.left.as_ref(), right.left.as_ref())
                || has_fn_application(left.right.as_ref(), right.right.as_ref())
        }
        (Obj::Div(left), Obj::Div(right)) => {
            has_fn_application(left.left.as_ref(), right.left.as_ref())
                || has_fn_application(left.right.as_ref(), right.right.as_ref())
        }
        (Obj::FnObj(left), Obj::FnObj(right))
            if left.head.to_string() == right.head.to_string()
                && left.body.len() == right.body.len() =>
        {
            left.body
                .iter()
                .zip(right.body.iter())
                .any(|(left_group, right_group)| {
                    left_group.len() == right_group.len()
                        && left_group
                            .iter()
                            .zip(right_group.iter())
                            .any(|(left_arg, right_arg)| {
                                has_fn_application(left_arg.as_ref(), right_arg.as_ref())
                            })
                })
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_equality_runs_only_from_the_outer_round() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("structural_equality_outer_round");

        let a: Obj = Identifier::new("A".to_string()).into();
        let b: Obj = Identifier::new("B".to_string()).into();
        let union_ab: Obj = Union::new(a.clone(), b.clone()).into();
        let union_ba: Obj = Union::new(b, a).into();
        let left: Obj =
            StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ab]).into();
        let right: Obj =
            StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ba]).into();
        assert!(runtime
            .verify_objs_are_equal_by_known_equality(&left, &right, default_line_file())
            .is_unknown());
        assert!(runtime
            .verify_objs_are_equal(
                &left,
                &right,
                default_line_file(),
                &UseContextVerifyState::new(1, true),
            )
            .expect("later-round equality verification")
            .is_unknown());
        assert!(runtime
            .verify_objs_are_equal(
                &left,
                &right,
                default_line_file(),
                &UseContextVerifyState::new(0, true),
            )
            .expect("outer-round equality verification")
            .is_true());
    }
}

fn could_match_after_one_checked_function_unfold(left: &Obj, right: &Obj) -> bool {
    let is_replayable_function =
        |obj: &Obj| matches!(obj, Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_));
    let is_plain_arithmetic = |obj: &Obj| {
        let immediate_args_have_function = |left: &Obj, right: &Obj| {
            matches!(left, Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_))
                || matches!(right, Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_))
        };
        match obj {
            Obj::Add(op) => !immediate_args_have_function(op.left.as_ref(), op.right.as_ref()),
            Obj::Sub(op) => !immediate_args_have_function(op.left.as_ref(), op.right.as_ref()),
            Obj::Mul(op) => !immediate_args_have_function(op.left.as_ref(), op.right.as_ref()),
            Obj::Div(op) => !immediate_args_have_function(op.left.as_ref(), op.right.as_ref()),
            _ => false,
        }
    };
    (is_replayable_function(left) && is_plain_arithmetic(right))
        || (is_replayable_function(right) && is_plain_arithmetic(left))
}

fn is_plain_native_arithmetic_candidate(obj: &Obj) -> bool {
    match obj {
        Obj::Atom(_)
        | Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::StandardSet(_)
        | Obj::FiniteSetSize(_) => true,
        Obj::Add(op) => {
            is_plain_native_arithmetic_candidate(op.left.as_ref())
                && is_plain_native_arithmetic_candidate(op.right.as_ref())
        }
        Obj::Sub(op) => {
            is_plain_native_arithmetic_candidate(op.left.as_ref())
                && is_plain_native_arithmetic_candidate(op.right.as_ref())
        }
        Obj::Mul(op) => {
            is_plain_native_arithmetic_candidate(op.left.as_ref())
                && is_plain_native_arithmetic_candidate(op.right.as_ref())
        }
        Obj::Div(op) => {
            is_plain_native_arithmetic_candidate(op.left.as_ref())
                && is_plain_native_arithmetic_candidate(op.right.as_ref())
        }
        Obj::Pow(op) => {
            is_plain_native_arithmetic_candidate(op.base.as_ref())
                && is_plain_native_arithmetic_candidate(op.exponent.as_ref())
        }
        _ => false,
    }
}
