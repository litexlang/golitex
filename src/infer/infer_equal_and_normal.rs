use crate::prelude::*;
use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

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
        infer_result: &mut InferResult,
        infer_step_description: &str,
    ) -> Result<(), RuntimeError> {
        infer_result.new_fact(&inferred_fact);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(inferred_fact)
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
        Ok(())
    }

    fn infer_equal_fact_cart_from_known_side(
        &mut self,
        known_cart_obj: &Cart,
        known_cart_obj_as_symbol: &Obj,
        target_obj: &Obj,
        equal_fact: &EqualFact,
        infer_result: &mut InferResult,
    ) -> Result<(), RuntimeError> {
        let target_is_cart_fact =
            IsCartFact::new(target_obj.clone(), equal_fact.line_file.clone()).into();
        self.store_inferred_fact_and_record_result(
            target_is_cart_fact,
            equal_fact,
            infer_result,
            "cart fact",
        )?;

        let target_cart_dim_obj = CartDim::new(target_obj.clone()).into();
        let known_cart_dim_obj = Number::new(known_cart_obj.args.len().to_string()).into();
        let cart_dim_equal_fact = EqualFact::new(
            target_cart_dim_obj,
            known_cart_dim_obj,
            equal_fact.line_file.clone(),
        )
        .into();
        self.store_inferred_fact_and_record_result(
            cart_dim_equal_fact,
            equal_fact,
            infer_result,
            "cart_dim fact",
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
        infer_result: &mut InferResult,
    ) -> Result<(), RuntimeError> {
        if known_tuple_obj.args.len() < 2 {
            return Ok(());
        }
        let target_is_tuple_fact =
            IsTupleFact::new(target_obj.clone(), equal_fact.line_file.clone()).into();
        self.store_inferred_fact_and_record_result(
            target_is_tuple_fact,
            equal_fact,
            infer_result,
            "tuple fact",
        )?;

        let target_tuple_dim_obj = TupleDim::new(target_obj.clone()).into();
        let known_tuple_dim_obj = Number::new(known_tuple_obj.args.len().to_string()).into();
        let tuple_dim_equal_fact = EqualFact::new(
            target_tuple_dim_obj,
            known_tuple_dim_obj,
            equal_fact.line_file.clone(),
        )
        .into();
        self.store_inferred_fact_and_record_result(
            tuple_dim_equal_fact,
            equal_fact,
            infer_result,
            "tuple_dim fact",
        )?;

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
    ) -> Result<InferResult, RuntimeError> {
        let infer_result = InferResult::new();

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

        Ok(infer_result)
    }

    fn infer_equal_fact_by_matrix_list(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let infer_result = InferResult::new();

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

        Ok(infer_result)
    }

    // From `u = v`: merge numeric normal forms in the env; if one side is `a-b` and the other `0`, emit `a=b`;
    // if one side is a literal cart/tuple/set-builder/finite-seq/matrix list, record shape for the other symbol.
    // Example: `a = 1+2` binds `a` to normalized `3`; `0 = x-y` yields fact `x = y`.
    pub fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(
            self.infer_equal_fact_from_subtraction_equals_zero(equal_fact)?,
        );
        infer_result
            .new_infer_result_inside(self.infer_equal_fact_and_give_value_to_obj(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_cart(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_tuple(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_set_builder(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_finite_seq_list(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_matrix_list(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_anonymous_fn(equal_fact)?);
        infer_result
            .new_infer_result_inside(self.infer_equal_fact_by_positive_real_power(equal_fact)?);

        Ok(infer_result)
    }

    /// `name = '(... ) ... { ... }'`: treat `name` as having the anonymous function's `FnSetBody`
    /// (same side table as `name $in fn ...` after infer).
    fn infer_equal_fact_by_anonymous_fn(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        if let Obj::AnonymousFn(anon) = &equal_fact.right {
            if !matches!(&equal_fact.left, Obj::AnonymousFn(_)) {
                let eq = (*anon.equal_to).clone();
                let lf = equal_fact.line_file.clone();
                self.register_known_objs_in_fn_sets_for_element_body(
                    &equal_fact.left,
                    anon.body.clone(),
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
                self.register_known_objs_in_fn_sets_for_element_body(
                    &equal_fact.right,
                    anon.body.clone(),
                    Some(eq),
                    lf.clone(),
                    lf,
                );
            }
        }
        Ok(InferResult::new())
    }

    // `0 = u - v` or `u - v = 0` => add `u = v` (non-trivial pair only).
    fn infer_equal_fact_from_subtraction_equals_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        let (a, b) = if obj_is_infer_literal_zero(&equal_fact.left) {
            match &equal_fact.right {
                Obj::Sub(s) => (s.left.as_ref().clone(), s.right.as_ref().clone()),
                _ => return Ok(infer_result),
            }
        } else if obj_is_infer_literal_zero(&equal_fact.right) {
            match &equal_fact.left {
                Obj::Sub(s) => (s.left.as_ref().clone(), s.right.as_ref().clone()),
                _ => return Ok(infer_result),
            }
        } else {
            return Ok(infer_result);
        };
        if a.to_string() == b.to_string() {
            return Ok(infer_result);
        }
        let derived: Fact = EqualFact::new(a, b, equal_fact.line_file.clone()).into();
        self.store_inferred_fact_and_record_result(
            derived,
            equal_fact,
            &mut infer_result,
            "equality from a - b = 0",
        )?;
        Ok(infer_result)
    }

    fn infer_equal_fact_by_cart(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        if let Obj::Cart(cart) = &equal_fact.left {
            self.infer_equal_fact_cart_from_known_side(
                cart,
                &equal_fact.left,
                &equal_fact.right,
                equal_fact,
                &mut infer_result,
            )?;
        }

        if let Obj::Cart(cart) = &equal_fact.right {
            self.infer_equal_fact_cart_from_known_side(
                cart,
                &equal_fact.right,
                &equal_fact.left,
                equal_fact,
                &mut infer_result,
            )?;
        }

        Ok(infer_result)
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
    ) -> Result<InferResult, RuntimeError> {
        if let Obj::SetBuilder(set_builder) = &equal_fact.left {
            self.infer_equal_fact_set_builder_from_known_side(
                set_builder,
                &equal_fact.left,
                &equal_fact.right,
                equal_fact,
            );
        }

        if let Obj::SetBuilder(set_builder) = &equal_fact.right {
            self.infer_equal_fact_set_builder_from_known_side(
                set_builder,
                &equal_fact.right,
                &equal_fact.left,
                equal_fact,
            );
        }

        Ok(InferResult::new())
    }

    fn infer_equal_fact_by_tuple(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        if let Obj::Tuple(tuple) = &equal_fact.left {
            self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.right,
                equal_fact,
                &mut infer_result,
            )?;
        }

        if let Obj::Tuple(tuple) = &equal_fact.right {
            self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.left,
                equal_fact,
                &mut infer_result,
            )?;
        }

        Ok(infer_result)
    }

    fn infer_equal_fact_and_give_value_to_obj(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_known_obj_value_from_equal_side(&equal_fact.left, &equal_fact.right);
        self.store_known_obj_value_from_equal_side(&equal_fact.right, &equal_fact.left);

        if let Some(derived) =
            crate::environment::equality_linear_derive::maybe_derived_linear_equal_fact(equal_fact)
        {
            self.store_known_obj_value_from_equal_side(&derived.left, &derived.right);
        }

        Ok(InferResult::new())
    }

    fn store_known_obj_value_from_equal_side(&mut self, target: &Obj, source: &Obj) {
        let Some(value) = self.known_obj_value_from_obj(source) else {
            return;
        };
        self.top_level_env()
            .known_obj_values
            .insert(target.to_string(), value);
    }

    // From `a^x = y`, infer `y $in R_pos` when `0 < a` and `x $in R`.
    // This is safe because a positive real base raised to a real exponent is positive.
    // Example: `a R_pos`, `x R`, `a^x = y` infers `y $in R_pos`.
    fn infer_equal_fact_by_positive_real_power(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact,
            &mut infer_result,
        )?;
        self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.right,
            &equal_fact.left,
            equal_fact,
            &mut infer_result,
        )?;
        Ok(infer_result)
    }

    fn infer_positive_real_power_membership_to_equal_side(
        &mut self,
        maybe_power: &Obj,
        target: &Obj,
        equal_fact: &EqualFact,
        infer_result: &mut InferResult,
    ) -> Result<(), RuntimeError> {
        if maybe_power.to_string() == target.to_string() {
            return Ok(());
        }
        let Obj::Pow(_) = maybe_power else {
            return Ok(());
        };

        let power_in_r_pos: AtomicFact = InFact::new(
            maybe_power.clone(),
            StandardSet::RPos.into(),
            equal_fact.line_file.clone(),
        )
        .into();
        let power_result = self.verify_non_equational_known_then_builtin_rules_only(
            &power_in_r_pos,
            &VerifyState::new(0, true),
        )?;
        if !power_result.is_true() {
            return Ok(());
        }

        let target_in_r_pos: AtomicFact = InFact::new(
            target.clone(),
            StandardSet::RPos.into(),
            equal_fact.line_file.clone(),
        )
        .into();
        infer_result.new_fact(&target_in_r_pos.clone().into());
        let nested_infer =
            self.store_atomic_fact_without_well_defined_verified_and_infer(target_in_r_pos)?;
        infer_result.new_infer_result_inside(nested_infer);
        Ok(())
    }

    // Predicate `P(args)`: check args against `P`'s param types, then store each instantiated `iff` body.
    // Example: if `P` is defined by `iff` clauses, those clauses become facts with `args` substituted.
    pub fn infer_normal_atomic_fact(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let predicate_definition = match self.get_prop_definition_by_name(&predicate_name) {
            Some(predicate_definition) => predicate_definition,
            None => return Ok(InferResult::new()),
        };
        let mut infer_result = InferResult::new();
        let source_fact: Fact = normal_atomic_fact.clone().into();
        let by_definition_reason = InferReason::ByDefinition(ByDefinitionReason::new(
            Some(source_fact.clone()),
            Some(predicate_name.clone()),
        ));

        let param_type_infer = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers_with_reason(
                &predicate_definition.params_def_with_type,
                &normal_atomic_fact.body,
                normal_atomic_fact.line_file.clone(),
                ParamObjType::DefHeader,
                by_definition_reason.clone(),
            )
            .map_err(|previous_error| {
                RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!(
                        "failed to verify parameter types for `{}`",
                        normal_atomic_fact
                    ),
                    normal_atomic_fact.line_file.clone(),
                    Some(previous_error),
                    vec![],
                )))
            })?;
        infer_result.new_infer_result_inside(param_type_infer);

        let param_to_arg_map = self.params_to_arg_map(
            &predicate_definition.params_def_with_type,
            &normal_atomic_fact.body,
        )?;

        for iff_fact in predicate_definition.iff_facts.iter() {
            let instantiated_iff_fact = self
                .inst_fact(
                    iff_fact,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
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
            infer_result.add_fact_by_definition(
                Some(source_fact.clone()),
                Some(predicate_name.clone()),
                &fact_to_store,
            );
            self.verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                fact_to_store,
                by_definition_reason.clone(),
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
        }

        Ok(infer_result)
    }
}
