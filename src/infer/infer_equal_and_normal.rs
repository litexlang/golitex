use crate::prelude::*;

impl Runtime {
    fn store_inferred_fact_and_record_result(
        &mut self,
        inferred_fact: Fact,
        equal_fact: &EqualFact,
        infer_result: &mut InferResult,
        infer_step_description: &str,
    ) -> Result<(), RuntimeError> {
        let inferred_fact_display = inferred_fact.to_string();
        self.store_fact_without_well_defined_verified_and_infer(inferred_fact)
            .map_err(|previous_error| {
                RuntimeError::new_infer_error_with_msg_position_previous_error(
                    format!(
                        "failed to store inferred {} while inferring `{}`",
                        infer_step_description, equal_fact
                    ),
                    equal_fact.line_file.clone(),
                    Some(previous_error.into()),
                )
            })?;
        infer_result.infer_facts.push(inferred_fact_display);
        Ok(())
    }

    fn infer_equal_fact_cart_from_known_side(
        &mut self,
        known_cart_obj: &crate::obj::Cart,
        known_cart_obj_as_symbol: &Obj,
        target_obj: &Obj,
        equal_fact: &EqualFact,
        infer_result: &mut InferResult,
    ) -> Result<(), RuntimeError> {
        let target_is_cart_fact = Fact::AtomicFact(AtomicFact::IsCartFact(IsCartFact::new(
            target_obj.clone(),
            equal_fact.line_file.clone(),
        )));
        self.store_inferred_fact_and_record_result(
            target_is_cart_fact,
            equal_fact,
            infer_result,
            "cart fact",
        )?;

        let target_cart_dim_obj = Obj::CartDim(CartDim::new(target_obj.clone()));
        let known_cart_dim_obj = Obj::Number(crate::obj::Number::new(
            known_cart_obj.args.len().to_string(),
        ));
        let cart_dim_equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            target_cart_dim_obj,
            known_cart_dim_obj,
            equal_fact.line_file.clone(),
        )));
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
        known_tuple_obj: &crate::obj::Tuple,
        target_obj: &Obj,
        equal_fact: &EqualFact,
        infer_result: &mut InferResult,
    ) -> Result<(), RuntimeError> {
        let target_is_tuple_fact = Fact::AtomicFact(AtomicFact::IsTupleFact(IsTupleFact::new(
            target_obj.clone(),
            equal_fact.line_file.clone(),
        )));
        self.store_inferred_fact_and_record_result(
            target_is_tuple_fact,
            equal_fact,
            infer_result,
            "tuple fact",
        )?;

        let target_tuple_dim_obj = Obj::TupleDim(TupleDim::new(target_obj.clone()));
        let known_tuple_dim_obj = Obj::Number(crate::obj::Number::new(
            known_tuple_obj.args.len().to_string(),
        ));
        let tuple_dim_equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            target_tuple_dim_obj,
            known_tuple_dim_obj,
            equal_fact.line_file.clone(),
        )));
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

    /// Infer from equality by syncing known calculated values.
    /// Example: from `a = 1 + 2`, remember `a -> 3`.
    pub(crate) fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        infer_result
            .new_infer_result_inside(self.infer_equal_fact_and_give_value_to_obj(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_cart(equal_fact)?);
        infer_result.new_infer_result_inside(self.infer_equal_fact_by_tuple(equal_fact)?);

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
        if let Some(right_calculated_value) = self.resolve_obj_to_number(&equal_fact.right) {
            self.top_level_env()
                .known_objs_equal_to_normalized_decimal_number
                .insert(equal_fact.left.to_string(), right_calculated_value);
        }

        if let Some(left_calculated_value) = self.resolve_obj_to_number(&equal_fact.left) {
            self.top_level_env()
                .known_objs_equal_to_normalized_decimal_number
                .insert(equal_fact.right.to_string(), left_calculated_value);
        }

        Ok(InferResult::new())
    }

    /// Infer predicate meaning by instantiating declared iff facts.
    /// Example: from `isEven(n)`, infer the instantiated definition facts.
    pub(crate) fn infer_normal_atomic_fact(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let predicate_definition = match self.get_prop_definition_by_name(&predicate_name) {
            Some(predicate_definition) => predicate_definition.clone(),
            None => return Ok(InferResult::new()),
        };
        let mut infer_result = InferResult::new();

        let param_type_infer = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers(
                &predicate_definition.params_def_with_type,
                &normal_atomic_fact.body,
                normal_atomic_fact.line_file.clone(),
            )
            .map_err(|previous_error| {
                RuntimeError::new_infer_error_with_msg_position_previous_error(
                    format!(
                        "failed to verify parameter types for `{}`",
                        normal_atomic_fact
                    ),
                    normal_atomic_fact.line_file.clone(),
                    Some(previous_error),
                )
            })?;
        infer_result.new_infer_result_inside(param_type_infer);

        let param_to_arg_map = self.params_to_arg_map(
            &predicate_definition.params_def_with_type,
            &normal_atomic_fact.body,
        )?;

        for iff_fact in predicate_definition.iff_facts.iter() {
            let instantiated_iff_fact =
                self.inst_fact(iff_fact, &param_to_arg_map).map_err(|e| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to instantiate iff fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file.clone(),
                        Some(e),
                    )
                })?;
            let fact_to_store =
                instantiated_iff_fact.with_new_line_file(normal_atomic_fact.line_file.clone());
            infer_result.new_fact(&fact_to_store);
            self.store_fact_without_well_defined_verified_and_infer(fact_to_store)
                .map_err(|previous_error| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to store instantiated iff fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file.clone(),
                        Some(previous_error.into()),
                    )
                })?;
        }

        Ok(infer_result)
    }
}
