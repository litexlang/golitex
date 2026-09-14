use crate::prelude::*;
use crate::verification::{compare_normalized_number_str_to_zero, NumberCompareResult};

fn obj_is_infer_literal_zero(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => matches!(
            compare_normalized_number_str_to_zero(&n.normalized_value),
            NumberCompareResult::Equal
        ),
        _ => false,
    }
}

impl Runtime {
    fn store_inferred_fact_and_record_result(
        &mut self,
        inferred_fact: Fact,
        equal_fact: &EqualFact,
        result: &mut SuccessInferResult,
        infer_step_description: &str,
        inference_state: &InferenceState,
    ) -> Result<SuccessStoreFactResult, RuntimeError> {
        result.new_fact(&inferred_fact);
        let conclusion_fact = inferred_fact.clone();
        let conclusion_infers = self
            .store_typed_inference_conclusion_and_infer(inferred_fact, inference_state)
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!(
                        "failed to store inferred {} while inferring `{}`",
                        infer_step_description, equal_fact
                    ),
                    equal_fact.line_file.clone(),
                    Some(previous_error),
                    vec![],
                )))
            })?;
        Ok(SuccessStoreFactResult::new(
            conclusion_fact,
            conclusion_infers,
        ))
    }

    fn infer_equal_fact_cart_from_known_side(
        &mut self,
        known_cart_obj: &Cart,
        known_cart_obj_as_symbol: &Obj,
        target_obj: &Obj,
        equal_fact: &EqualFact,
        result: &mut SuccessInferResult,
        inference_state: &InferenceState,
    ) -> Result<(), RuntimeError> {
        let target_is_cart_fact = self
            .new_is_cart_fact(target_obj.clone(), equal_fact.line_file.clone())
            .into();
        let _ = self.store_inferred_fact_and_record_result(
            target_is_cart_fact,
            equal_fact,
            result,
            "cart fact",
            inference_state,
        )?;

        let target_cart_dim_obj = CartDim::new(target_obj.clone()).into();
        let known_cart_dim_obj = Number::new(known_cart_obj.args.len().to_string()).into();
        let cart_dim_equal_fact = self
            .new_equal_fact(
                target_cart_dim_obj,
                known_cart_dim_obj,
                equal_fact.line_file.clone(),
            )
            .into();
        let _ = self.store_inferred_fact_and_record_result(
            cart_dim_equal_fact,
            equal_fact,
            result,
            "cart_dim fact",
            inference_state,
        )?;
        self.store_known_cart_obj(
            &known_cart_obj_as_symbol.to_string(),
            known_cart_obj.clone(),
            equal_fact.line_file.clone(),
        );
        self.store_known_cart_obj(
            &target_obj.to_string(),
            known_cart_obj.clone(),
            equal_fact.line_file.clone(),
        );
        Ok(())
    }

    fn infer_equal_fact_tuple_from_known_side(
        &mut self,
        known_tuple_obj: &Tuple,
        target_obj: &Obj,
        equal_fact: &EqualFact,
        result: &mut SuccessInferResult,
        known_side: KnownTupleEqualitySide,
        inference_state: &InferenceState,
    ) -> Result<(), RuntimeError> {
        if known_tuple_obj.args.len() < 2 {
            return Ok(());
        }
        let target_is_tuple_fact = self
            .new_is_tuple_fact(target_obj.clone(), equal_fact.line_file.clone())
            .into();
        let tuple_conclusion = self.store_inferred_fact_and_record_result(
            target_is_tuple_fact,
            equal_fact,
            result,
            "tuple fact",
            inference_state,
        )?;

        let target_tuple_dim_obj = TupleDim::new(target_obj.clone()).into();
        let known_tuple_dim_obj = Number::new(known_tuple_obj.args.len().to_string()).into();
        let tuple_dim_equal_fact = self
            .new_equal_fact(
                target_tuple_dim_obj,
                known_tuple_dim_obj,
                equal_fact.line_file.clone(),
            )
            .into();
        let dimension_conclusion = self.store_inferred_fact_and_record_result(
            tuple_dim_equal_fact,
            equal_fact,
            result,
            "tuple_dim fact",
            inference_state,
        )?;

        result.add_rule_application(
            InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(
                TupleEqualityWithKnownTupleImpliesTupleShapeInferRule {
                    known_side,
                    tuple_length: known_tuple_obj.args.len(),
                },
            ),
            equal_fact.clone().into(),
            vec![tuple_conclusion, dimension_conclusion],
        );

        self.store_tuple_obj_and_cart(
            &target_obj.to_string(),
            Some(known_tuple_obj.clone()),
            None,
            equal_fact.line_file.clone(),
        );
        Ok(())
    }

    fn infer_equal_fact_finite_seq_list_from_known_side(
        &mut self,
        known_list: &FiniteSeqListObj,
        target_obj: &Obj,
        equal_fact: &EqualFact,
    ) -> Result<(), RuntimeError> {
        let lf = equal_fact.line_file.clone();
        self.store_known_finite_seq_list_obj(&target_obj.to_string(), known_list.clone(), None, lf);
        Ok(())
    }

    fn infer_equal_fact_matrix_list_from_known_side(
        &mut self,
        known_matrix: &MatrixListObj,
        target_obj: &Obj,
        equal_fact: &EqualFact,
    ) -> Result<(), RuntimeError> {
        let lf = equal_fact.line_file.clone();
        self.store_known_matrix_list_obj(&target_obj.to_string(), known_matrix.clone(), None, lf);
        Ok(())
    }

    fn infer_equal_fact_by_finite_seq_list(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let result = SuccessInferResult::new();

        if let Obj::FiniteSeqListObj(list) = &equal_fact.left {
            if !matches!(&equal_fact.right, Obj::FiniteSeqListObj(_)) {
                self.infer_equal_fact_finite_seq_list_from_known_side(
                    list,
                    &equal_fact.right,
                    equal_fact,
                )?;
            }
        }

        if let Obj::FiniteSeqListObj(list) = &equal_fact.right {
            if !matches!(&equal_fact.left, Obj::FiniteSeqListObj(_)) {
                self.infer_equal_fact_finite_seq_list_from_known_side(
                    list,
                    &equal_fact.left,
                    equal_fact,
                )?;
            }
        }

        Ok(result)
    }

    fn infer_equal_fact_by_matrix_list(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let result = SuccessInferResult::new();

        if let Obj::MatrixListObj(m) = &equal_fact.left {
            if !matches!(&equal_fact.right, Obj::MatrixListObj(_)) {
                self.infer_equal_fact_matrix_list_from_known_side(
                    m,
                    &equal_fact.right,
                    equal_fact,
                )?;
            }
        }

        if let Obj::MatrixListObj(m) = &equal_fact.right {
            if !matches!(&equal_fact.left, Obj::MatrixListObj(_)) {
                self.infer_equal_fact_matrix_list_from_known_side(m, &equal_fact.left, equal_fact)?;
            }
        }

        Ok(result)
    }

    // From `u = v`: merge numeric normal forms in the env; if one side is `a-b` and the other `0`, emit `a=b`;
    // if one side is a literal cart/tuple/set-builder/finite-seq/matrix list, record shape for the other symbol.
    // Example: `a = 1+2` binds `a` to normalized `3`; `0 = x-y` yields fact `x = y`.
    pub(in crate::inference) fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        result.new_infer_result_inside(
            self.infer_equal_fact_from_subtraction_equals_zero(equal_fact, inference_state)?,
        );
        result.new_infer_result_inside(self.infer_equal_fact_and_give_value_to_obj(equal_fact)?);
        result.new_infer_result_inside(self.infer_equal_fact_by_cart(equal_fact, inference_state)?);
        result
            .new_infer_result_inside(self.infer_equal_fact_by_tuple(equal_fact, inference_state)?);
        result.new_infer_result_inside(self.infer_equal_fact_by_set_builder(equal_fact)?);
        result.new_infer_result_inside(self.infer_equal_fact_by_finite_seq_list(equal_fact)?);
        result.new_infer_result_inside(self.infer_equal_fact_by_matrix_list(equal_fact)?);
        result.new_infer_result_inside(self.infer_equal_fact_by_anonymous_fn(equal_fact)?);
        result.new_infer_result_inside(
            self.infer_equal_fact_by_positive_real_power(equal_fact, inference_state)?,
        );

        Ok(result)
    }

    /// `name = fn(... ) ... { ... }'`: treat `name` as having the anonymous function's `FnSetBody`
    /// (same side table as `name $in fn ...` after infer).
    fn infer_equal_fact_by_anonymous_fn(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if let Obj::AnonymousFn(anon) = &equal_fact.right {
            if !matches!(&equal_fact.left, Obj::AnonymousFn(_)) {
                let eq = (*anon.equal_to).clone();
                let lf = equal_fact.line_file.clone();
                self.register_function_set_knowledge_for_element(
                    &equal_fact.left,
                    anon.body.clone(),
                    None,
                    Some(eq),
                    lf.clone(),
                    lf,
                );
            }
        }
        if let Obj::AnonymousFn(anon) = &equal_fact.left {
            if !matches!(&equal_fact.right, Obj::AnonymousFn(_)) {
                let eq = (*anon.equal_to).clone();
                let lf = equal_fact.line_file.clone();
                self.register_function_set_knowledge_for_element(
                    &equal_fact.right,
                    anon.body.clone(),
                    None,
                    Some(eq),
                    lf.clone(),
                    lf,
                );
            }
        }
        Ok(SuccessInferResult::new())
    }

    // `0 = u - v` or `u - v = 0` => add `u = v` (non-trivial pair only).
    fn infer_equal_fact_from_subtraction_equals_zero(
        &mut self,
        equal_fact: &EqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        let (a, b) = if obj_is_infer_literal_zero(&equal_fact.left) {
            match &equal_fact.right {
                Obj::Sub(s) => (s.left.as_ref().clone(), s.right.as_ref().clone()),
                _ => return Ok(result),
            }
        } else if obj_is_infer_literal_zero(&equal_fact.right) {
            match &equal_fact.left {
                Obj::Sub(s) => (s.left.as_ref().clone(), s.right.as_ref().clone()),
                _ => return Ok(result),
            }
        } else {
            return Ok(result);
        };
        if a.to_string() == b.to_string() {
            return Ok(result);
        }
        let derived: Fact = self
            .new_equal_fact(a, b, equal_fact.line_file.clone())
            .into();
        let _ = self.store_inferred_fact_and_record_result(
            derived,
            equal_fact,
            &mut result,
            "equality from a - b = 0",
            inference_state,
        )?;
        Ok(result)
    }

    fn infer_equal_fact_by_cart(
        &mut self,
        equal_fact: &EqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();

        if let Obj::Cart(cart) = &equal_fact.left {
            self.infer_equal_fact_cart_from_known_side(
                cart,
                &equal_fact.left,
                &equal_fact.right,
                equal_fact,
                &mut result,
                inference_state,
            )?;
        }

        if let Obj::Cart(cart) = &equal_fact.right {
            self.infer_equal_fact_cart_from_known_side(
                cart,
                &equal_fact.right,
                &equal_fact.left,
                equal_fact,
                &mut result,
                inference_state,
            )?;
        }

        Ok(result)
    }

    fn infer_equal_fact_set_builder_from_known_side(
        &mut self,
        set_builder: &SetBuilder,
        known_set_builder_obj: &Obj,
        target_obj: &Obj,
        equal_fact: &EqualFact,
    ) {
        let lf = equal_fact.line_file.clone();
        self.store_known_set_builder_obj(&target_obj.to_string(), set_builder.clone(), lf.clone());
        self.store_known_set_builder_obj(
            &known_set_builder_obj.to_string(),
            set_builder.clone(),
            lf,
        );
    }

    fn infer_equal_fact_by_set_builder(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let left_set_builder = match &equal_fact.left {
            Obj::SetBuilder(set_builder) => Some(set_builder.clone()),
            _ => self.get_obj_equal_to_set_builder(&equal_fact.left),
        };
        let right_set_builder = match &equal_fact.right {
            Obj::SetBuilder(set_builder) => Some(set_builder.clone()),
            _ => self.get_obj_equal_to_set_builder(&equal_fact.right),
        };

        // Equality propagates a known set-builder representative across equal named sets.
        // This is used when a template instance first equals its materialized
        // identifier and that identifier equals `{x T: P(x)}`.
        // Example: `\selected<T> = selected<T> = {x T: P(x)}` lets membership
        // in either selected object expose `P(x)`.
        if let Some(set_builder) = left_set_builder {
            self.infer_equal_fact_set_builder_from_known_side(
                &set_builder,
                &equal_fact.left,
                &equal_fact.right,
                equal_fact,
            );
        }

        if let Some(set_builder) = right_set_builder {
            self.infer_equal_fact_set_builder_from_known_side(
                &set_builder,
                &equal_fact.right,
                &equal_fact.left,
                equal_fact,
            );
        }

        Ok(SuccessInferResult::new())
    }

    fn infer_equal_fact_by_tuple(
        &mut self,
        equal_fact: &EqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();

        if let Obj::Tuple(tuple) = &equal_fact.left {
            self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.right,
                equal_fact,
                &mut result,
                KnownTupleEqualitySide::Left,
                inference_state,
            )?;
        }

        if !matches!(&equal_fact.left, Obj::Tuple(_)) {
            if let Obj::Tuple(tuple) = &equal_fact.right {
                self.infer_equal_fact_tuple_from_known_side(
                    tuple,
                    &equal_fact.left,
                    equal_fact,
                    &mut result,
                    KnownTupleEqualitySide::Right,
                    inference_state,
                )?;
            }
        }

        Ok(result)
    }

    fn infer_equal_fact_and_give_value_to_obj(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_known_obj_value_from_equal_side(&equal_fact.left, &equal_fact.right);
        self.store_known_obj_value_from_equal_side(&equal_fact.right, &equal_fact.left);

        if let Some(derived) =
            crate::environment::equality_linear_derive::maybe_derived_linear_equal_fact(
                self, equal_fact,
            )
        {
            self.store_known_obj_value_from_equal_side(&derived.left, &derived.right);
        }

        Ok(SuccessInferResult::new())
    }

    fn store_known_obj_value_from_equal_side(&mut self, target: &Obj, source: &Obj) {
        let Some(value) = self.known_obj_value_from_obj(source) else {
            return;
        };
        self.top_level_env()
            .object_properties
            .store_simplified_value(target.to_string(), value);
    }

    // From `a^x = y`, infer `y $in R+` when `0 < a` and `x $in R`.
    // This is safe because a positive real base raised to a real exponent is positive.
    // Example: `a R+`, `x R`, `a^x = y` infers `y $in R+`.
    fn infer_equal_fact_by_positive_real_power(
        &mut self,
        equal_fact: &EqualFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact,
            &mut result,
            inference_state,
        )?;
        self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.right,
            &equal_fact.left,
            equal_fact,
            &mut result,
            inference_state,
        )?;
        Ok(result)
    }

    fn infer_positive_real_power_membership_to_equal_side(
        &mut self,
        maybe_power: &Obj,
        target: &Obj,
        equal_fact: &EqualFact,
        result: &mut SuccessInferResult,
        inference_state: &InferenceState,
    ) -> Result<(), RuntimeError> {
        if maybe_power.to_string() == target.to_string() {
            return Ok(());
        }
        let Obj::Pow(_) = maybe_power else {
            return Ok(());
        };

        let power_in_r_pos: AtomicFact = self
            .new_in_fact(
                maybe_power.clone(),
                StandardSet::RPos.into(),
                equal_fact.line_file.clone(),
            )
            .into();
        let verify_state = VerifyState::initial().with_inference_state(inference_state);
        let power_result = self.verify_atomic_except_equality_with_bounded_builtin_routes(
            &power_in_r_pos,
            &verify_state,
        )?;
        if !power_result.is_success() {
            return Ok(());
        }

        let target_in_r_pos: AtomicFact = self
            .new_in_fact(
                target.clone(),
                StandardSet::RPos.into(),
                equal_fact.line_file.clone(),
            )
            .into();
        let target_fact: Fact = target_in_r_pos.clone().into();
        let nested_infer = self
            .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                target_in_r_pos.clone(),
                InferReason::StoredFact.store_reason(),
                inference_state,
            )?;
        let conclusion = SuccessStoreFactResult::new(target_fact, nested_infer.clone());
        let is_closed_positive_power = maybe_power
            .evaluate_to_normalized_decimal_number()
            .is_some_and(|number| {
                matches!(
                    compare_normalized_number_str_to_zero(&number.normalized_value),
                    NumberCompareResult::Greater
                )
            });
        let positive_integer_base_natural_power_premises = if let Obj::Pow(power) = maybe_power {
            let exponent_is_natural = power
                .exponent
                .evaluate_to_normalized_decimal_number()
                .is_some_and(|number| {
                    number
                        .normalized_value
                        .parse::<i128>()
                        .is_ok_and(|exponent| exponent >= 0)
                });
            let base_positive: Fact = self
                .new_less_fact(
                    Number::new("0".to_string()).into(),
                    power.base.as_ref().clone(),
                    equal_fact.line_file.clone(),
                )
                .into();
            let base_in_z: Fact = self
                .new_in_fact(
                    power.base.as_ref().clone(),
                    StandardSet::Z.into(),
                    equal_fact.line_file.clone(),
                )
                .into();
            (exponent_is_natural
                && self.known_fact_id_for_fact(&base_positive)?.is_some()
                && self.known_fact_id_for_fact(&base_in_z)?.is_some())
            .then_some((base_positive, base_in_z))
        } else {
            None
        };
        if is_closed_positive_power {
            result.add_rule_application_preserving_conclusion_result_structure(
                InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(
                    ClosedPositivePowerEqualityImpliesEqualSideMembershipInferRule {
                        power_is_left_endpoint: obj_equality_key(maybe_power)
                            == obj_equality_key(&equal_fact.left),
                    },
                ),
                vec![equal_fact.clone().into()],
                vec![conclusion],
            );
        } else if let Some((base_positive, base_in_z)) =
            positive_integer_base_natural_power_premises
        {
            result.add_rule_application_preserving_conclusion_result_structure(
                InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
                    PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembershipInferRule {
                        power_is_left_endpoint: obj_equality_key(maybe_power)
                            == obj_equality_key(&equal_fact.left),
                    },
                ),
                vec![equal_fact.clone().into(), base_positive, base_in_z],
                vec![conclusion],
            );
        } else {
            result.new_infer_result_inside(nested_infer);
            result.new_fact(&target_in_r_pos.into());
        }
        Ok(())
    }

    // Positive builtin predicates expose their definition facts before ordinary `prop` inference.
    // Example: `A $proper_subset B` infers both `A $subset B` and `A != B`.
    // For `P(args)`, each instantiated `iff` body is stored after checking parameter types.
    pub(in crate::inference) fn infer_normal_atomic_fact(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let firing_key = format!(
            "normal predicate definition:{}",
            nested_obj_binder_normalized_fact_key(&normal_atomic_fact.clone().into())
        );
        // A fixed predicate definition has deterministic consequences for fixed
        // arguments. Example: expanding `$is_linear_map(..., T)` twice must not
        // repeat its parameter typing and `iff` facts.
        if self.infer_rule_firing_cached(&firing_key) {
            return Ok(SuccessInferResult::new());
        }
        let proper_relation_facts = crate::verification::verify_proper_set_relations_builtin::positive_proper_set_relation_definition_facts(self, normal_atomic_fact);
        let builtin_definition_facts = match proper_relation_facts {
            Some(facts) => Some(facts),
            None => match self.builtin_prime_definition_facts(normal_atomic_fact)? {
                Some(facts) => Some(facts),
                None => match self.builtin_coprime_definition_facts(normal_atomic_fact) {
                    Some(facts) => Some(facts),
                    None => match self.builtin_dvd_definition_facts(normal_atomic_fact)? {
                        Some(facts) => Some(facts),
                        None => match crate::verification::choice_function_for_definition_facts(
                            self,
                            normal_atomic_fact,
                        )? {
                            Some(facts) => Some(facts),
                            None => {
                                self.builtin_function_property_definition_facts(normal_atomic_fact)?
                            }
                        },
                    },
                },
            },
        };
        if let Some(definition_facts) = builtin_definition_facts {
            let mut result = SuccessInferResult::new();
            let reason = InferReason::ByDefinition;
            for fact in definition_facts {
                result.add_fact_by_definition(&fact);
                result.new_infer_result_inside(
                    self.store_typed_inference_conclusion_and_infer_with_reason(
                        fact,
                        reason.clone(),
                        inference_state,
                    )?,
                );
            }
            // Injectivity and surjectivity together give a unique preimage.
            // Keep this as an explicitly named builtin inference instead of
            // strengthening the definitional clauses of `$bijective`.
            if let Some(unique_preimage) =
                self.bijective_unique_preimage_fact(normal_atomic_fact)?
            {
                let rule = "bijective functions have unique preimages";
                result.add_builtin_inference(rule, &unique_preimage);
                result.new_infer_result_inside(
                    self.store_typed_inference_conclusion_and_infer_with_reason(
                        unique_preimage,
                        InferReason::BuiltinInference(rule.to_string()),
                        inference_state,
                    )?,
                );
            }
            self.store_infer_rule_firing(firing_key);
            return Ok(result);
        }
        let predicate_definition = match self.get_prop_definition_by_name(&predicate_name) {
            Some(predicate_definition) => predicate_definition,
            None => return Ok(SuccessInferResult::new()),
        };
        let mut result = SuccessInferResult::new();
        let by_definition_reason = InferReason::ByDefinition;
        let source_fact: Fact = normal_atomic_fact.clone().into();

        let parameter_requirement_facts = self
            .instantiate_argument_parameter_requirement_facts(
                &predicate_definition.typed_parameters,
                &normal_atomic_fact.body,
                normal_atomic_fact.line_file.clone(),
                SubstitutionMode::Exact,
            )
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!(
                        "failed to instantiate parameter requirements for `{}`",
                        normal_atomic_fact
                    ),
                    normal_atomic_fact.line_file.clone(),
                    Some(previous_error),
                    vec![],
                )))
            })?;
        for (parameter_index, parameter_requirement_fact) in
            parameter_requirement_facts.into_iter().enumerate()
        {
            let stored_parameter_requirement = self
                .store_typed_inference_conclusion_and_infer_with_reason(
                    parameter_requirement_fact.clone(),
                    by_definition_reason.clone(),
                    inference_state,
                )
                .map_err(|previous_error| {
                    RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to store inferred parameter type {} for `{}`",
                            parameter_index, normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file.clone(),
                        Some(previous_error),
                        vec![],
                    )))
                })?;
            if let Fact::AtomicFact(AtomicFact::InFact(requirement)) = &parameter_requirement_fact {
                if let (Obj::Atom(argument), Obj::StructObj(struct_obj)) =
                    (&requirement.element, &requirement.set)
                {
                    if let Some(symbol) = argument.symbol_ref() {
                        self.remember_inferred_direct_struct_carrier_for_symbol(
                            symbol, struct_obj,
                        )?;
                    }
                }
            }
            result.add_rule_application_preserving_conclusion_result_structure(
                InferRule::DefinedPredicateParameterRequirementProjection(
                    DefinedPredicateParameterRequirementProjectionInferRule {
                        predicate_name: predicate_name.clone(),
                        parameter_index,
                    },
                ),
                vec![source_fact.clone()],
                vec![SuccessStoreFactResult::new(
                    parameter_requirement_fact,
                    stored_parameter_requirement,
                )],
            );
        }

        let param_to_arg_map = self.params_to_arg_map(
            &predicate_definition.typed_parameters,
            &normal_atomic_fact.body,
        )?;

        for (clause_index, iff_fact) in predicate_definition.iff_facts.iter().enumerate() {
            let instantiated_iff_fact = self
                .inst_fact(
                    iff_fact,
                    &param_to_arg_map,
                    SubstitutionMode::Exact,
                    Some(normal_atomic_fact.line_file.clone()),
                )
                .map_err(|e| {
                    RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to instantiate iff fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    )))
                })?;
            let fact_to_store = instantiated_iff_fact;
            // A positive user prop recursively exposes positive user props in
            // its definition. Example: `Outer(x) := Inner(x)` and
            // `Inner(x) := x >= 0`, so `Outer(x)` infers `x >= 0`.
            // A positive prop exposes its parameter-type facts as part of its
            // meaning. The call above stores their instantiated forms before
            // these clauses. Since the clauses were checked under the matching
            // formal parameter facts when the prop was defined, typed,
            // capture-avoiding substitution preserves well-definedness.
            // The active-fact guard and firing cache stop cyclic definitions.
            let stored_clause = self
                .store_without_well_defined_verification_and_infer_with_reason_and_state(
                    fact_to_store.clone(),
                    by_definition_reason.clone(),
                    inference_state,
                )
                .map_err(|previous_error| {
                    RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to store instantiated iff fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file.clone(),
                        Some(previous_error),
                        vec![],
                    )))
                })?;
            result.add_rule_application_preserving_conclusion_result_structure(
                InferRule::DefinedPredicateDefinitionClauseProjection(
                    DefinedPredicateDefinitionClauseProjectionInferRule {
                        predicate_name: predicate_name.clone(),
                        clause_index,
                    },
                ),
                vec![source_fact.clone()],
                vec![SuccessStoreFactResult::new(fact_to_store, stored_clause)],
            );
        }

        self.store_infer_rule_firing(firing_key);
        Ok(result)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/inference/equality_and_normalization/defined_predicate_inference_result_tests.rs"]
mod defined_predicate_inference_result_tests;
