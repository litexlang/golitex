use crate::prelude::*;
use std::collections::{HashMap, HashSet};

struct ResolvedAtomicFactLookup {
    fact: AtomicFact,
    fact_transformation: Option<FactTransformationEvidence>,
}

impl ResolvedAtomicFactLookup {
    fn new(fact: AtomicFact, fact_transformation: Option<FactTransformationEvidence>) -> Self {
        Self {
            fact,
            fact_transformation,
        }
    }
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_known_atomic_facts(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(memoized_result) = self.verify_atomic_fact_from_statement_memo(atomic_fact) {
            return Ok(memoized_result);
        }

        let result = if atomic_fact.number_of_args() == 1 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(atomic_fact)?
        } else if atomic_fact.number_of_args() == 2 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(atomic_fact)?
        } else {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
                atomic_fact,
            )?
        };

        Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let args = atomic_fact.args_ref();
        let all_objs_equal_to_arg =
            self.all_objs_equal_to_arg_for_known_atomic_fact(args[0], &module_names);

        for environment in self.iter_environments_from_top() {
            let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(
                environment,
                atomic_fact,
                &all_objs_equal_to_arg,
                &module_names,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(
                    environment,
                    atomic_fact,
                    &all_objs_equal_to_arg,
                    &module_names,
                )?;
                if result.is_true() {
                    return Ok(result);
                }
            }
        }
        if let Some(result) = self
            .verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts(
                atomic_fact,
                &module_names,
            )?
        {
            return Ok(result);
        }

        if let Some(resolved) = self.resolved_atomic_fact_for_lookup_with_evidence(atomic_fact)? {
            let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(
                &resolved.fact,
            )?;
            return Ok(self.retarget_resolved_known_atomic_fact_result(
                atomic_fact,
                result,
                resolved.fact_transformation,
            ));
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let args = atomic_fact.args_ref();
        let all_objs_equal_to_arg0 =
            self.all_objs_equal_to_arg_for_known_atomic_fact(args[0], &module_names);
        let all_objs_equal_to_arg1 =
            self.all_objs_equal_to_arg_for_known_atomic_fact(args[1], &module_names);

        for environment in self.iter_environments_from_top() {
            let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(
                environment,
                atomic_fact,
                &all_objs_equal_to_arg0,
                &all_objs_equal_to_arg1,
                &module_names,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(
                    environment,
                    atomic_fact,
                    &all_objs_equal_to_arg0,
                    &all_objs_equal_to_arg1,
                    &module_names,
                )?;
                if result.is_true() {
                    return Ok(result);
                }
            }
        }
        if let Some(result) = self
            .verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts(
                atomic_fact,
                &module_names,
            )?
        {
            return Ok(result);
        }

        if let Some(resolved) = self.resolved_atomic_fact_for_lookup_with_evidence(atomic_fact)? {
            let result = self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(
                    &resolved.fact,
                )?;
            return Ok(self.retarget_resolved_known_atomic_fact_result(
                atomic_fact,
                result,
                resolved.fact_transformation,
            ));
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        let args = atomic_fact.args_ref();
        for arg in args.iter() {
            all_objs_equal_to_each_arg
                .push(self.all_objs_equal_to_arg_for_known_atomic_fact(arg, &module_names));
        }

        for environment in self.iter_environments_from_top() {
            let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
                environment,
                atomic_fact,
                &all_objs_equal_to_each_arg,
                &module_names,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                let result = self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
                    environment,
                    atomic_fact,
                    &all_objs_equal_to_each_arg,
                    &module_names,
                )?;
                if result.is_true() {
                    return Ok(result);
                }
            }
        }
        if let Some(result) = self
            .verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts(
                atomic_fact,
                &module_names,
            )?
        {
            return Ok(result);
        }

        if let Some(resolved) = self.resolved_atomic_fact_for_lookup_with_evidence(atomic_fact)? {
            let result = self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
                    &resolved.fact,
                )?;
            return Ok(self.retarget_resolved_known_atomic_fact_result(
                atomic_fact,
                result,
                resolved.fact_transformation,
            ));
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(crate) fn all_objs_equal_to_arg_for_known_atomic_fact(
        &self,
        arg: &Obj,
        module_names: &[String],
    ) -> Vec<String> {
        let raw_arg = arg.to_string();
        let normalized_arg = obj_equality_key(arg);
        let mut all_objs_equal_to_arg = vec![raw_arg.clone(), normalized_arg.clone()];
        self.extend_all_objs_equal_to_given_from_current_and_imported_envs(
            &mut all_objs_equal_to_arg,
            &normalized_arg,
            module_names,
        );
        if raw_arg != normalized_arg {
            self.extend_all_objs_equal_to_given_from_current_and_imported_envs(
                &mut all_objs_equal_to_arg,
                &raw_arg,
                module_names,
            );
        }

        if let Some(calculated_obj) = self.resolve_obj_to_number(arg) {
            if calculated_obj.to_string() != raw_arg {
                self.extend_all_objs_equal_to_given_from_current_and_imported_envs(
                    &mut all_objs_equal_to_arg,
                    &calculated_obj.to_string(),
                    module_names,
                );
            }
        }

        dedup_strings(&mut all_objs_equal_to_arg);
        all_objs_equal_to_arg
    }

    fn extend_all_objs_equal_to_given_from_current_and_imported_envs(
        &self,
        result: &mut Vec<String>,
        given: &str,
        module_names: &[String],
    ) {
        result.extend(self.get_all_objs_equal_to_given(given));
        for module_name in module_names.iter() {
            let environments = self.imported_module_environments(module_name);
            if environments.is_empty() {
                continue;
            }
            if !result.iter().any(|item| item == given) {
                result.push(given.to_string());
            }
            result.extend(Self::get_all_objs_equal_to_given_in_environments(
                &environments,
                given,
            ));
        }
    }

    pub(crate) fn equality_transport_for_known_atomic_fact(
        &self,
        known_fact: &AtomicFact,
        goal: &AtomicFact,
        module_names: &[String],
    ) -> Option<EqualityTransportEvidence> {
        if known_fact.key() != goal.key() || known_fact.is_true() != goal.is_true() {
            return None;
        }
        let known_args = known_fact.args_ref();
        let goal_args = goal.args_ref();
        if known_args.len() != goal_args.len() {
            return None;
        }
        if known_args
            .iter()
            .zip(goal_args.iter())
            .all(|(known, goal)| obj_equality_key(known) == obj_equality_key(goal))
        {
            return Some(EqualityTransportEvidence::new(Vec::new()));
        }

        // Equality lookup already combines nested runtime environments. Build
        // the corresponding proof graph from those same checked direct edges
        // so the successful lookup retains an actual transport path.
        let equalities = self.known_equality_proof_graph(module_names);

        let mut steps = Vec::new();
        for (known_arg, goal_arg) in known_args.iter().zip(goal_args.iter()) {
            if !self.collect_nested_equality_transport_steps(
                &EqualFact::new_from_refs(known_arg, goal_arg, goal.line_file()),
                &equalities,
                module_names,
                &mut steps,
            ) {
                return None;
            }
        }
        Some(EqualityTransportEvidence::new(steps))
    }

    /// Retain a replayable congruence proof from `source` to `goal`.
    ///
    /// A direct equality edge may relate the complete objects, such as
    /// `a + b = 14`. Otherwise, matching outer constructors are traversed and
    /// the same rule is applied recursively to their corresponding children.
    /// This makes equality transport independent of the depth or particular
    /// supported object constructor at which a stored equality is used.
    fn collect_nested_equality_transport_steps(
        &self,
        equal_fact: &EqualFact,
        equalities: &KnownEquality,
        module_names: &[String],
        steps: &mut Vec<EqualityTransportStep>,
    ) -> bool {
        if obj_equality_key(&equal_fact.left) == obj_equality_key(&equal_fact.right) {
            return true;
        }

        if let Some(path) = equalities.proof_path(&equal_fact.left, &equal_fact.right) {
            for proof_step in path {
                let equality_fact: Fact = AtomicFact::EqualFact(proof_step.equality.clone()).into();
                let equality_fact_id =
                    self.fact_id_for_transport_fact(&equality_fact, module_names);
                steps.push(EqualityTransportStep::new(
                    proof_step.from,
                    proof_step.to,
                    proof_step.equality,
                    equality_fact_id,
                ));
            }
            return true;
        }

        let result: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
            &equal_fact.left,
            &equal_fact.right,
            &mut |source_arg, goal_arg| {
                Ok(self.collect_nested_equality_transport_steps(
                    &EqualFact::new_from_refs(source_arg, goal_arg, equal_fact.line_file.clone()),
                    equalities,
                    module_names,
                    steps,
                ))
            },
        );
        result.unwrap_or(false)
    }

    fn extend_equality_proof_graph(equalities: &mut KnownEquality, environment: &Environment) {
        for equality in environment.known_equality.direct_equalities().iter() {
            equalities.store(equality);
        }
    }

    fn known_equality_proof_graph(&self, module_names: &[String]) -> KnownEquality {
        let mut equalities = KnownEquality::new();
        for environment in self.iter_environments_from_top() {
            Self::extend_equality_proof_graph(&mut equalities, environment);
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::extend_equality_proof_graph(&mut equalities, environment);
            }
        }
        equalities
    }

    pub(crate) fn fact_id_for_transport_fact(
        &self,
        fact: &Fact,
        module_names: &[String],
    ) -> Option<FactId> {
        let display_key = fact.to_string();
        let normalized_key = nested_obj_binder_normalized_fact_key(fact);
        let find_in_environment = |environment: &Environment| {
            environment
                .cache_known_fact
                .get(&display_key)
                .or_else(|| environment.cache_known_fact.get(&normalized_key))
                .map(|cached| cached.fact_id)
        };

        for environment in self.iter_environments_from_top() {
            if let Some(fact_id) = find_in_environment(environment) {
                return Some(fact_id);
            }
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                if let Some(fact_id) = find_in_environment(environment) {
                    return Some(fact_id);
                }
            }
        }
        None
    }

    fn cited_known_atomic_fact(
        &self,
        goal: &AtomicFact,
        known_fact: &AtomicFact,
        module_names: &[String],
        detail: Option<String>,
    ) -> VerifiedByResult {
        let source_fact: Fact = known_fact.clone().into();
        let source_fact_id = self.fact_id_for_transport_fact(&source_fact, module_names);
        let equality_transport =
            self.equality_transport_for_known_atomic_fact(known_fact, goal, module_names);
        // The fast structural lookup can descend through an object such as
        // `f(a + b)` before the slower resolved-fact retry runs. Preserve the
        // same source-to-goal replay evidence on that route too, provided its
        // resolved source is exactly the known fact we are citing.
        let fact_transformation = equality_transport
            .is_none()
            .then(|| {
                self.resolved_atomic_fact_for_lookup_with_evidence(goal)
                    .ok()
                    .flatten()
                    .filter(|resolved| {
                        nested_obj_binder_normalized_fact_key(&Fact::from(resolved.fact.clone()))
                            == nested_obj_binder_normalized_fact_key(&source_fact)
                    })
                    .and_then(|resolved| resolved.fact_transformation)
            })
            .flatten();
        VerifiedByResult::cited_fact_with_provenance(
            goal.clone().into(),
            source_fact,
            source_fact_id,
            equality_transport,
            fact_transformation,
            detail,
        )
    }

    fn atomic_fact_with_resolved_unary_operand(fact: &AtomicFact, x: Obj) -> AtomicFact {
        let line_file = fact.line_file();
        match fact {
            AtomicFact::IsSetFact(_) => IsSetFact::new(x, line_file).into(),
            AtomicFact::IsNonemptySetFact(_) => IsNonemptySetFact::new(x, line_file).into(),
            AtomicFact::IsFiniteSetFact(_) => IsFiniteSetFact::new(x, line_file).into(),
            AtomicFact::IsCartFact(_) => IsCartFact::new(x, line_file).into(),
            AtomicFact::IsTupleFact(_) => IsTupleFact::new(x, line_file).into(),
            AtomicFact::NotIsSetFact(_) => NotIsSetFact::new(x, line_file).into(),
            AtomicFact::NotIsNonemptySetFact(_) => NotIsNonemptySetFact::new(x, line_file).into(),
            AtomicFact::NotIsFiniteSetFact(_) => NotIsFiniteSetFact::new(x, line_file).into(),
            AtomicFact::NotIsCartFact(_) => NotIsCartFact::new(x, line_file).into(),
            AtomicFact::NotIsTupleFact(_) => NotIsTupleFact::new(x, line_file).into(),
            AtomicFact::NormalAtomicFact(n) => {
                NormalAtomicFact::new(n.predicate.clone(), vec![x], line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(n) => {
                NotNormalAtomicFact::new(n.predicate.clone(), vec![x], line_file).into()
            }
            _ => unreachable!(
                "atomic_fact_with_resolved_unary_operand: expected a one-argument atomic fact"
            ),
        }
    }

    fn atomic_fact_with_resolved_binary_operands(
        fact: &AtomicFact,
        left: Obj,
        right: Obj,
    ) -> AtomicFact {
        let line_file = fact.line_file();
        match fact {
            AtomicFact::EqualFact(_) => EqualFact::new(left, right, line_file).into(),
            AtomicFact::LessFact(_) => LessFact::new(left, right, line_file).into(),
            AtomicFact::GreaterFact(_) => GreaterFact::new(left, right, line_file).into(),
            AtomicFact::LessEqualFact(_) => LessEqualFact::new(left, right, line_file).into(),
            AtomicFact::GreaterEqualFact(_) => GreaterEqualFact::new(left, right, line_file).into(),
            AtomicFact::InFact(_) => InFact::new(left, right, line_file).into(),
            AtomicFact::SubsetFact(_) => SubsetFact::new(left, right, line_file).into(),
            AtomicFact::SupersetFact(_) => SupersetFact::new(left, right, line_file).into(),
            AtomicFact::NotEqualFact(_) => NotEqualFact::new(left, right, line_file).into(),
            AtomicFact::NotLessFact(_) => NotLessFact::new(left, right, line_file).into(),
            AtomicFact::NotGreaterFact(_) => NotGreaterFact::new(left, right, line_file).into(),
            AtomicFact::NotLessEqualFact(_) => NotLessEqualFact::new(left, right, line_file).into(),
            AtomicFact::NotGreaterEqualFact(_) => {
                NotGreaterEqualFact::new(left, right, line_file).into()
            }
            AtomicFact::NotInFact(_) => NotInFact::new(left, right, line_file).into(),
            AtomicFact::NotSubsetFact(_) => NotSubsetFact::new(left, right, line_file).into(),
            AtomicFact::NotSupersetFact(_) => NotSupersetFact::new(left, right, line_file).into(),
            AtomicFact::FnEqualFact(_) => FnEqualFact::new(left, right, line_file).into(),
            AtomicFact::NormalAtomicFact(x) => {
                NormalAtomicFact::new(x.predicate.clone(), vec![left, right], line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(x) => {
                NotNormalAtomicFact::new(x.predicate.clone(), vec![left, right], line_file).into()
            }
            _ => unreachable!(
                "atomic_fact_with_resolved_binary_operands: expected a two-argument atomic fact"
            ),
        }
    }

    fn atomic_fact_with_resolved_predicate_args(fact: &AtomicFact, args: Vec<Obj>) -> AtomicFact {
        let line_file = fact.line_file();
        match fact {
            AtomicFact::NormalAtomicFact(x) => {
                NormalAtomicFact::new(x.predicate.clone(), args, line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(x) => {
                NotNormalAtomicFact::new(x.predicate.clone(), args, line_file).into()
            }
            _ => unreachable!(
                "atomic_fact_with_resolved_predicate_args: expected NormalAtomicFact or NotNormalAtomicFact"
            ),
        }
    }

    pub(crate) fn atomic_fact_with_replaced_args(
        atomic_fact: &AtomicFact,
        args: Vec<Obj>,
    ) -> Option<AtomicFact> {
        match args.as_slice() {
            [arg] => Some(Self::atomic_fact_with_resolved_unary_operand(
                atomic_fact,
                arg.clone(),
            )),
            [left, right] => Some(Self::atomic_fact_with_resolved_binary_operands(
                atomic_fact,
                left.clone(),
                right.clone(),
            )),
            _ if matches!(
                atomic_fact,
                AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_)
            ) =>
            {
                Some(Self::atomic_fact_with_resolved_predicate_args(
                    atomic_fact,
                    args,
                ))
            }
            _ => None,
        }
    }

    fn resolved_atomic_fact_for_lookup_with_evidence(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<ResolvedAtomicFactLookup>, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let equalities = self.known_equality_proof_graph(&module_names);
        let mut substitutions = HashMap::new();
        let mut substituted_symbols = HashSet::new();
        let mut source_to_goal_equality_steps = Vec::new();

        for equality in equalities.direct_equalities().iter() {
            for candidate in [&equality.left, &equality.right] {
                let Obj::Atom(atom) = candidate else {
                    continue;
                };
                let Some(symbol) = atom.symbol_ref() else {
                    continue;
                };
                let symbol_key = symbol.substitution_key();
                if substituted_symbols.contains(&symbol_key) {
                    continue;
                }
                let resolved = self.resolve_obj(candidate);
                if obj_equality_key(candidate) == obj_equality_key(&resolved) {
                    continue;
                }

                let trial_substitution = HashMap::from([(symbol_key.clone(), resolved.clone())]);
                let mut changes_goal = false;
                for argument in atomic_fact.args_ref().iter() {
                    let replaced =
                        self.inst_obj(argument, &trial_substitution, ParamObjType::Forall)?;
                    if obj_equality_key(argument) != obj_equality_key(&replaced) {
                        changes_goal = true;
                        break;
                    }
                }
                if !changes_goal {
                    continue;
                }

                let Some(path) = equalities.proof_path(candidate, &resolved) else {
                    continue;
                };
                substitutions.insert(symbol_key.clone(), resolved);
                substituted_symbols.insert(symbol_key);
                for proof_step in path.into_iter().rev() {
                    let equality_fact: Fact =
                        AtomicFact::EqualFact(proof_step.equality.clone()).into();
                    source_to_goal_equality_steps.push(EqualityTransportStep::new(
                        proof_step.to,
                        proof_step.from,
                        proof_step.equality,
                        self.fact_id_for_transport_fact(&equality_fact, &module_names),
                    ));
                }
            }
        }

        let equality_rewritten_args = atomic_fact
            .args_ref()
            .iter()
            .map(|argument| self.inst_obj(argument, &substitutions, ParamObjType::Forall))
            .collect::<Result<Vec<_>, _>>()?;
        let Some(equality_rewritten_fact) =
            Self::atomic_fact_with_replaced_args(atomic_fact, equality_rewritten_args)
        else {
            return Ok(None);
        };
        let resolved_args = equality_rewritten_fact
            .args_ref()
            .iter()
            .map(|argument| self.resolve_obj(argument))
            .collect::<Vec<_>>();
        let Some(resolved_fact) =
            Self::atomic_fact_with_replaced_args(&equality_rewritten_fact, resolved_args)
        else {
            return Ok(None);
        };
        if resolved_fact.to_string() == atomic_fact.to_string() {
            return Ok(None);
        }

        let mut transformations = Vec::new();
        let mut transformations_are_replayable = true;
        if resolved_fact.to_string() != equality_rewritten_fact.to_string() {
            if atomic_facts_align_by_nested_rational_normalization(
                &resolved_fact,
                &equality_rewritten_fact,
            ) {
                transformations.push(FactTransformationStep::new(
                    equality_rewritten_fact.clone().into(),
                    FactTransformationRule::RationalNormalization,
                ));
            } else {
                transformations_are_replayable = false;
            }
        }
        if equality_rewritten_fact.to_string() != atomic_fact.to_string() {
            if source_to_goal_equality_steps.is_empty() {
                transformations_are_replayable = false;
            } else {
                transformations.push(FactTransformationStep::new(
                    atomic_fact.clone().into(),
                    FactTransformationRule::EqualityRewrite(EqualityTransportEvidence::new(
                        source_to_goal_equality_steps,
                    )),
                ));
            }
        }

        let fact_transformation = transformations_are_replayable.then(|| {
            FactTransformationEvidence::new(resolved_fact.clone().into(), transformations)
        });
        Ok(Some(ResolvedAtomicFactLookup::new(
            resolved_fact,
            fact_transformation,
        )))
    }

    fn retarget_resolved_known_atomic_fact_result(
        &self,
        goal: &AtomicFact,
        result: StmtResult,
        fact_transformation: Option<FactTransformationEvidence>,
    ) -> StmtResult {
        let Some(fact_transformation) = fact_transformation else {
            return result;
        };
        let Some(success) = result.factual_success() else {
            return result;
        };
        let VerifiedByResult::Fact(citation) = success.underlying_verified_by() else {
            return result;
        };

        let mut citation = citation.clone();
        if citation.fact_transformation.is_some() {
            return result;
        }
        citation.fact_transformation = Some(fact_transformation);
        FactualStmtSuccess::new_with_verified_by_known_fact(
            goal.clone().into(),
            VerifiedByResult::Fact(citation),
            Vec::new(),
        )
        .into()
    }

    pub(crate) fn resolved_atomic_fact_for_lookup(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<AtomicFact> {
        let args = atomic_fact.args_ref();
        let resolved_args = args
            .iter()
            .map(|arg| self.resolve_obj(arg))
            .collect::<Vec<_>>();
        if args
            .iter()
            .zip(resolved_args.iter())
            .all(|(arg, resolved)| arg.to_string() == resolved.to_string())
        {
            return None;
        }

        Self::atomic_fact_with_replaced_args(atomic_fact, resolved_args)
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(
        &self,
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg: &Vec<String>,
        module_names: &[String],
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_1_arg
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj in all_objs_equal_to_arg.iter() {
                if let Some(known_atomic_fact) = known_facts_map.get(obj) {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        atomic_fact.clone().into(),
                        self.cited_known_atomic_fact(
                            atomic_fact,
                            known_atomic_fact,
                            module_names,
                            None,
                        ),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(
        &self,
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg0: &Vec<String>,
        all_objs_equal_to_arg1: &Vec<String>,
        module_names: &[String],
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj0 in all_objs_equal_to_arg0.iter() {
                for obj1 in all_objs_equal_to_arg1.iter() {
                    if let Some(known_atomic_fact) =
                        known_facts_map.get(&(obj0.clone(), obj1.clone()))
                    {
                        return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                            atomic_fact.clone().into(),
                            self.cited_known_atomic_fact(
                                atomic_fact,
                                known_atomic_fact,
                                module_names,
                                None,
                            ),
                            Vec::new(),
                        ))
                        .into());
                    }
                }
            }

            let given_args = atomic_fact.args_ref();
            for known_atomic_fact in known_facts_map.values() {
                let known_args = known_atomic_fact.args_ref();
                let args_match =
                    known_args
                        .iter()
                        .zip(given_args.iter())
                        .all(|(known_arg, given_arg)| {
                            self.objs_match_for_known_atomic_fact_lookup(
                                known_arg,
                                given_arg,
                                atomic_fact.line_file(),
                            )
                        });
                if args_match {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        atomic_fact.clone().into(),
                        self.cited_known_atomic_fact(
                            atomic_fact,
                            known_atomic_fact,
                            module_names,
                            Some("corresponding arguments are known equal".to_string()),
                        ),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        // Order facts are stored under `<` vs `>` etc.; e.g. known `a > 0` must match goal `0 < a`.
        if let Some(alt) = atomic_fact.transposed_binary_order_equivalent() {
            if let Some(known_facts_map) = environment
                .known_atomic_facts_with_2_args
                .get(&(alt.key(), alt.is_true()))
            {
                for obj0 in all_objs_equal_to_arg1.iter() {
                    for obj1 in all_objs_equal_to_arg0.iter() {
                        if let Some(known_atomic_fact) =
                            known_facts_map.get(&(obj0.clone(), obj1.clone()))
                        {
                            return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                                atomic_fact.clone().into(),
                                VerifiedByResult::cited_fact(
                                    atomic_fact.clone().into(),
                                    known_atomic_fact.clone().into(),
                                    None,
                                ),
                                Vec::new(),
                            ))
                            .into());
                        }
                    }
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn objs_match_for_known_atomic_fact_lookup(
        &self,
        known_arg: &Obj,
        given_arg: &Obj,
        line_file: LineFile,
    ) -> bool {
        if self.equal_fact_sides_are_congruent_by_known_equalities(&EqualFact::new_from_refs(
            known_arg,
            given_arg,
            line_file.clone(),
        )) {
            return true;
        }

        let mut known_candidates = vec![known_arg.clone()];
        known_candidates.extend(self.get_all_obj_representatives_equal_to_given(known_arg));
        let mut given_candidates = vec![given_arg.clone()];
        given_candidates.extend(self.get_all_obj_representatives_equal_to_given(given_arg));

        // Reuse a fact through both a stored equality and structural congruence.
        // Example: A = {a} and a = b let membership in A imply membership in {b}.
        known_candidates.iter().any(|known_candidate| {
            given_candidates.iter().any(|given_candidate| {
                self.equal_fact_sides_are_congruent_by_known_equalities(&EqualFact::new_from_refs(
                    known_candidate,
                    given_candidate,
                    line_file.clone(),
                ))
            })
        })
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
        &self,
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
        module_names: &[String],
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_facts) = environment
            .known_atomic_facts_with_0_or_more_than_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            let atomic_fact_args = atomic_fact.args_ref();
            for known_fact in known_facts.iter() {
                let known_fact_args = known_fact.args_ref();
                if known_fact_args.len() != atomic_fact_args.len() {
                    let message = format!(
                        "known atomic fact {} has different number of args than the given fact {}",
                        known_fact.to_string(),
                        atomic_fact.to_string()
                    );
                    return Err({
                        VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(atomic_fact.clone()).into_stmt()),
                            message.clone(),
                            atomic_fact.line_file(),
                            Some(
                                UnknownRuntimeError(RuntimeErrorStruct::new(
                                    Some(Fact::from(atomic_fact.clone()).into_stmt()),
                                    message,
                                    atomic_fact.line_file(),
                                    None,
                                    vec![],
                                ))
                                .into(),
                            ),
                            vec![],
                        ))
                        .into()
                    });
                }
                let mut all_args_match = true;
                for (index, known_arg) in known_fact_args.iter().enumerate() {
                    let known_arg_string = known_arg.to_string();
                    if !all_objs_equal_to_each_arg[index].contains(&known_arg_string) {
                        all_args_match = false;
                        break;
                    }
                }
                if all_args_match {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        atomic_fact.clone().into(),
                        self.cited_known_atomic_fact(atomic_fact, known_fact, module_names, None),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts(
        &self,
        atomic_fact: &AtomicFact,
        module_names: &[String],
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !atomic_fact
            .args_ref()
            .iter()
            .any(|arg| matches!(arg, Obj::AnonymousFn(_)))
        {
            return Ok(None);
        }

        for environment in self.iter_environments_from_top() {
            if let Some(result) = self
                .verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts_in_environment(
                    environment,
                    atomic_fact,
                )?
            {
                return Ok(Some(result));
            }
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                if let Some(result) = self
                    .verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts_in_environment(
                        environment,
                        atomic_fact,
                    )?
                {
                    return Ok(Some(result));
                }
            }
        }

        Ok(None)
    }

    fn verify_atomic_fact_with_alpha_equivalent_anonymous_fn_known_facts_in_environment(
        &self,
        environment: &Environment,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
        let mut known_facts = Vec::new();
        match atomic_fact.number_of_args() {
            1 => {
                if let Some(facts) = environment.known_atomic_facts_with_1_arg.get(&lookup_key) {
                    known_facts.extend(facts.values());
                }
            }
            2 => {
                if let Some(facts) = environment.known_atomic_facts_with_2_args.get(&lookup_key) {
                    known_facts.extend(facts.values());
                }
            }
            _ => {
                if let Some(facts) = environment
                    .known_atomic_facts_with_0_or_more_than_2_args
                    .get(&lookup_key)
                {
                    known_facts.extend(facts.iter());
                }
            }
        }

        let given_args = atomic_fact.args_ref();
        for known_fact in known_facts {
            let known_args = known_fact.args_ref();
            if known_args.len() != given_args.len() {
                continue;
            }
            let mut all_args_match = true;
            for (known_arg, given_arg) in known_args.iter().zip(given_args.iter()) {
                if !self.objs_match_for_fact_lookup(known_arg, given_arg)? {
                    all_args_match = false;
                    break;
                }
            }
            if all_args_match {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_known_fact(
                        atomic_fact.clone().into(),
                        VerifiedByResult::cited_fact(
                            atomic_fact.clone().into(),
                            known_fact.clone().into(),
                            None,
                        ),
                        Vec::new(),
                    )
                    .into(),
                ));
            }
        }

        Ok(None)
    }
}

fn atomic_facts_align_by_nested_rational_normalization(
    source: &AtomicFact,
    goal: &AtomicFact,
) -> bool {
    if source.key() != goal.key() || source.is_true() != goal.is_true() {
        return false;
    }
    let source_args = source.args_ref();
    let goal_args = goal.args_ref();
    source_args.len() == goal_args.len()
        && source_args
            .iter()
            .zip(goal_args.iter())
            .all(|(source, goal)| objs_align_by_nested_rational_normalization(source, goal))
}

fn objs_align_by_nested_rational_normalization(source: &Obj, goal: &Obj) -> bool {
    if objs_equal_by_rational_expression_evaluation(source, goal) {
        return true;
    }
    let result: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
        source,
        goal,
        &mut |source_arg, goal_arg| {
            Ok(objs_align_by_nested_rational_normalization(
                source_arg, goal_arg,
            ))
        },
    );
    result.unwrap_or(false)
}

fn dedup_strings(values: &mut Vec<String>) {
    let mut deduped = Vec::with_capacity(values.len());
    for value in values.drain(..) {
        if !deduped.iter().any(|existing| existing == &value) {
            deduped.push(value);
        }
    }
    *values = deduped;
}
