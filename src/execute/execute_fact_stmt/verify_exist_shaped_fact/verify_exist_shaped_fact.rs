use crate::ast::fact::{
    exist_shaped_fact_from_fact, exist_shaped_fact_to_fact, exist_shaped_fact_free_args_ref,
    exist_shaped_fact_id, EqualFact, ExistShapedFact, Fact, InFact, IsNonemptySetFact, LessFact,
    NotEqualFact,
};
use crate::ast::obj::{
    IntegerOperator, Literal, Mod, Number, Obj, StandardSet,
};
use crate::exec_env::exist_shaped_fact_index_key::{
    exist_shaped_fact_alpha_match_key, exist_shaped_fact_can_prove_goal,
    exist_shaped_fact_known_lookup_keys,
};
use crate::exec_env::known_forall_conclusion_memory::{
    exist_at_forall_location, ForallConclusionCite,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::helper::{
    archimedean_reciprocal_bound, equality_witness_from_membership_parts,
    integer_multiple_from_zero_remainder_operands, nonempty_set_member_witness_set,
    rational_integer_ratio_free_operand, rational_positive_denominator_free_operand,
    real_density_midpoint_endpoints, real_line_comparison_free_operands,
};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::result::{
    exist_shaped_fact_result_from_search_fail, exist_shaped_fact_result_from_success,
    exist_shaped_fact_result_from_wd_fail, ExistShapedBuiltinArchimedeanReciprocal,
    ExistShapedBuiltinEqualityWitnessFromMembership,
    ExistShapedBuiltinIntegerMultipleFromZeroRemainder,
    ExistShapedBuiltinNonemptySetMemberWitness, ExistShapedBuiltinRationalIntegerRatio,
    ExistShapedBuiltinRationalPositiveDenominator, ExistShapedBuiltinRealDensityMidpoint,
    ExistShapedBuiltinRealLineComparisonWitness, ExistShapedFactSearchProofByBuiltinRule,
    ExistShapedFactSearchProofByKnownExistShapedFact, ExistShapedFactSearchedProof,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::{
    VerifyExistShapedFactWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Split plain exist / exist! / not exist.
    // Each: WD (Success|Failed, same shape as atomic) → Builtin → known → known_forall.
    // Example (known): stored `exist x N st {x = 1}` proves the same goal.
    // Example (forall): known `forall a N: exist x N st {x = a}` proves `exist x N st {x = 2}`.
    pub fn verify_exist_shaped_fact(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            match self.verify_exist_shaped_fact_well_definedness(fact, verify_state.clone())? {
                VerifyExistShapedFactWellDefinedResult::Success(proof) => proof,
                VerifyExistShapedFactWellDefinedResult::Failed(reason) => {
                    return Ok(exist_shaped_fact_result_from_wd_fail(fact, reason));
                }
            };
        let Some(searched_proof) = self.search_exist_shaped_fact_proof(fact, verify_state)? else {
            return Ok(exist_shaped_fact_result_from_search_fail(fact, well_defined_proof));
        };
        Ok(exist_shaped_fact_result_from_success(
            fact,
            well_defined_proof,
            searched_proof,
        ))
    }

    // Builtin → known_exist → known_forall.
    fn search_exist_shaped_fact_proof(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedFactSearchedProof>> {
        if let Some(proof) =
            self.search_exist_shaped_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(ExistShapedFactSearchedProof::ByBuiltinRule(proof)));
        }
        if let Some(proof) =
            self.search_exist_shaped_fact_proof_by_known_exist_shaped_fact(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_exist_shaped_fact_proof_by_known_forall_fact(fact, verify_state)?
        {
            return Ok(Some(ExistShapedFactSearchedProof::ByKnownForallFact(proof)));
        }
        Ok(None)
    }

    fn search_exist_shaped_fact_proof_by_builtin_rule(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedFactSearchProofByBuiltinRule>> {
        if let Some(proof) =
            self.search_exist_builtin_real_line_comparison_witness(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::RealLineComparisonWitness(proof),
            ));
        }
        if let Some(proof) =
            self.search_exist_builtin_equality_witness_from_membership(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::EqualityWitnessFromMembership(proof),
            ));
        }
        if let Some(proof) =
            self.search_exist_builtin_nonempty_set_member_witness(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::NonemptySetMemberWitness(proof),
            ));
        }
        if let Some(proof) =
            self.search_exist_builtin_rational_positive_denominator(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::RationalPositiveDenominator(proof),
            ));
        }
        if let Some(proof) =
            self.search_exist_builtin_rational_integer_ratio(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::RationalIntegerRatio(proof),
            ));
        }
        if let Some(proof) = self
            .search_exist_builtin_integer_multiple_from_zero_remainder(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::IntegerMultipleFromZeroRemainder(proof),
            ));
        }
        if let Some(proof) =
            self.search_exist_builtin_archimedean_reciprocal(fact, verify_state.clone())?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::ArchimedeanReciprocal(proof),
            ));
        }
        if let Some(proof) =
            self.search_exist_builtin_real_density_midpoint(fact, verify_state)?
        {
            return Ok(Some(
                ExistShapedFactSearchProofByBuiltinRule::RealDensityMidpoint(proof),
            ));
        }
        Ok(None)
    }

    // Builtin: real-line comparison witness. See ExistShapedBuiltinRealLineComparisonWitness.
    fn search_exist_builtin_real_line_comparison_witness(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinRealLineComparisonWitness>> {
        let Some(free_operands) = real_line_comparison_free_operands(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let mut requirement_facts = Vec::with_capacity(free_operands.len());
        let mut proof_of_requirement_facts = Vec::with_capacity(free_operands.len());
        let mut seen = Vec::new();
        for operand in free_operands {
            let key = operand.display_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            let premise: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: operand,
                set: Obj::StandardSet(StandardSet::R),
                line_file: line_file.clone(),
            }
            .into();
            let proof = self.verify_fact(&premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            requirement_facts.push(premise);
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some(ExistShapedBuiltinRealLineComparisonWitness {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    // Builtin: equality witness from membership. See ExistShapedBuiltinEqualityWitnessFromMembership.
    fn search_exist_builtin_equality_witness_from_membership(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinEqualityWitnessFromMembership>> {
        let Some((set, member)) = equality_witness_from_membership_parts(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let premise: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: member,
            set,
            line_file,
        }
        .into();
        let membership_proof = self.verify_fact(&premise, child_state)?;
        if membership_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ExistShapedBuiltinEqualityWitnessFromMembership {
            membership_proof,
        }))
    }

    // Builtin: nonempty-set member witness. See ExistShapedBuiltinNonemptySetMemberWitness.
    fn search_exist_builtin_nonempty_set_member_witness(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinNonemptySetMemberWitness>> {
        let Some(set) = nonempty_set_member_witness_set(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let premise: Fact = IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set,
            line_file,
        }
        .into();
        let nonempty_proof = self.verify_fact(&premise, child_state)?;
        if nonempty_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ExistShapedBuiltinNonemptySetMemberWitness {
            nonempty_proof,
        }))
    }

    // Builtin: rational positive-denominator representation.
    // See ExistShapedBuiltinRationalPositiveDenominator.
    fn search_exist_builtin_rational_positive_denominator(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinRationalPositiveDenominator>> {
        let Some(rational) = rational_positive_denominator_free_operand(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let premise: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: rational,
            set: Obj::StandardSet(StandardSet::Q),
            line_file,
        }
        .into();
        let rational_membership_proof = self.verify_fact(&premise, child_state)?;
        if rational_membership_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ExistShapedBuiltinRationalPositiveDenominator {
            rational_membership_proof,
        }))
    }

    // Builtin: rational integer / nonzero-integer ratio.
    // See ExistShapedBuiltinRationalIntegerRatio.
    fn search_exist_builtin_rational_integer_ratio(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinRationalIntegerRatio>> {
        let Some(rational) = rational_integer_ratio_free_operand(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let premise: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: rational,
            set: Obj::StandardSet(StandardSet::Q),
            line_file,
        }
        .into();
        let rational_membership_proof = self.verify_fact(&premise, child_state)?;
        if rational_membership_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ExistShapedBuiltinRationalIntegerRatio {
            rational_membership_proof,
        }))
    }

    // Builtin: zero remainder ⇒ integer multiple.
    // See ExistShapedBuiltinIntegerMultipleFromZeroRemainder.
    fn search_exist_builtin_integer_multiple_from_zero_remainder(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinIntegerMultipleFromZeroRemainder>> {
        let Some((dividend, divisor)) = integer_multiple_from_zero_remainder_operands(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let requirement_facts: Vec<Fact> = vec![
            InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: dividend.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: line_file.clone(),
            }
            .into(),
            InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: divisor.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: line_file.clone(),
            }
            .into(),
            NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: divisor.clone(),
                right: zero.clone(),
                line_file: line_file.clone(),
            }
            .into(),
            EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: Box::new(dividend),
                    right: Box::new(divisor),
                })),
                right: zero,
                line_file,
            }
            .into(),
        ];
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for premise in &requirement_facts {
            let proof = self.verify_fact(premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some(ExistShapedBuiltinIntegerMultipleFromZeroRemainder {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    // Builtin: Archimedean reciprocal bound. See ExistShapedBuiltinArchimedeanReciprocal.
    fn search_exist_builtin_archimedean_reciprocal(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinArchimedeanReciprocal>> {
        let Some(bound) = archimedean_reciprocal_bound(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let premise: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: bound,
            set: Obj::StandardSet(StandardSet::RPos),
            line_file,
        }
        .into();
        let positive_bound_proof = self.verify_fact(&premise, child_state)?;
        if positive_bound_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ExistShapedBuiltinArchimedeanReciprocal {
            positive_bound_proof,
        }))
    }

    // Builtin: real density midpoint. See ExistShapedBuiltinRealDensityMidpoint.
    fn search_exist_builtin_real_density_midpoint(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinRealDensityMidpoint>> {
        let Some((left, right)) = real_density_midpoint_endpoints(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let requirement_facts: Vec<Fact> = vec![
            InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: left.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: line_file.clone(),
            }
            .into(),
            InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: right.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: line_file.clone(),
            }
            .into(),
            LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left,
                right,
                line_file,
            }
            .into(),
        ];
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for premise in &requirement_facts {
            let proof = self.verify_fact(premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some(ExistShapedBuiltinRealDensityMidpoint {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    fn search_exist_shaped_fact_proof_by_known_exist_shaped_fact(
        &mut self,
        fact: &ExistShapedFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedFactSearchedProof>> {
        let goal_id = exist_shaped_fact_id(fact);
        for key in exist_shaped_fact_known_lookup_keys(fact) {
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(entries) = env.facts.known_exist.by_key.get(&key) {
                    for entry in entries {
                        let cite_fact_id = exist_shaped_fact_id(entry);
                        if cite_fact_id != goal_id {
                            return Ok(Some(ExistShapedFactSearchedProof::ByKnownExistShapedFact(
                                ExistShapedFactSearchProofByKnownExistShapedFact { cite_fact_id },
                            )));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    // After: SearchProofByKnownForallFact cite.
    fn search_exist_shaped_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state.can_use_def_and_known_forall_and_known_strategy
            || verify_state.can_use_builtin_rule_round == 0
        {
            return Ok(None);
        }
        let premise_state = verify_state.with_one_less_round();
        for lookup_key in exist_shaped_fact_known_lookup_keys(fact) {
            let mut cites = Vec::new();
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(entries) = env.facts.known_forall_conclusions.by_exist.get(&lookup_key)
                {
                    cites.extend(entries.iter().cloned());
                }
            }
            for cite in cites {
                if let Some(proof) =
                    self.try_apply_forall_exist_conclusion_cite(fact, &cite, premise_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }
        }
        Ok(None)
    }

    fn try_apply_forall_exist_conclusion_cite(
        &mut self,
        goal: &ExistShapedFact,
        cite: &ForallConclusionCite,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        let forall = {
            let mut found = None;
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(Fact::ForallFact(f)) = env.facts.facts_by_id.get(&cite.fact_id) {
                    found = Some(f.clone());
                    break;
                }
            }
            match found {
                Some(f) => f,
                None => return Ok(None),
            }
        };
        let Some(conclusion) = exist_at_forall_location(&forall, &cite.location) else {
            return Ok(None);
        };
        if !exist_shaped_fact_can_prove_goal(&conclusion, goal) {
            return Ok(None);
        }

        // Step 1: list forall params in declaration order.
        let param_ids = forall.typed_parameters.ordered_param_ids();
        let conclusion_args = exist_shaped_fact_free_args_ref(&conclusion);
        let goal_args = exist_shaped_fact_free_args_ref(goal);

        // Step 2–3: bind params / strict-equal non-params; every param must be bound.
        // Example: known `forall a N: exist x N st {x = a}` vs goal `exist x N st {x = 2}`
        // → bind a ↦ 2.
        let Some(matched) =
            self.match_forall_conclusion_args(&conclusion_args, &goal_args, &param_ids)?
        else {
            return Ok(None);
        };
        let subst = subst_from_ordered_params(&param_ids, &matched.forall_parameters_match_what_args);

        // Step 4: instantiate the exist conclusion and alpha-compare to the goal.
        let instantiated = match self.inst_fact(&exist_shaped_fact_to_fact(&conclusion), &subst) {
            Ok(f) => match exist_shaped_fact_from_fact(&f) {
                Some(e) => e,
                None => return Ok(None),
            },
            Err(_) => return Ok(None),
        };
        if exist_shaped_fact_alpha_match_key(&instantiated) != exist_shaped_fact_alpha_match_key(goal) {
            return Ok(None);
        }

        // Step 5: prove param-type obligations, then dom facts.
        let Some(instantiation_requirements) =
            self.prove_forall_instantiation_requirements(&forall, &subst, verify_state)?
        else {
            return Ok(None);
        };

        Ok(Some(SearchProofByKnownForallFact {
            cite: cite.clone(),
            forall_parameters_match_what_args: matched.forall_parameters_match_what_args,
            arg_match_proofs: matched.arg_match_proofs,
            instantiation_requirements,
        }))
    }
}
