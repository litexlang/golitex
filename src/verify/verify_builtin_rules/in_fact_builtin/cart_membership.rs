use super::*;

impl Runtime {
    pub(super) fn verify_in_fact_by_left_is_tuple_right_is_cart(
        &mut self,
        in_fact: &InFact,
        tuple: &Tuple,
        cart: &Cart,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if tuple.args.len() < 2 {
            return Ok((StmtUnknown::new()).into());
        }
        if tuple.args.len() != cart.args.len() {
            return Ok((StmtUnknown::new()).into());
        }

        for component_index in 0..tuple.args.len() {
            let tuple_component_obj = (*tuple.args[component_index]).clone();
            let cart_component_obj = (*cart.args[component_index]).clone();
            let component_in_fact = InFact::new(
                tuple_component_obj,
                cart_component_obj,
                in_fact.line_file.clone(),
            )
            .into();
            let component_verify_result = self.verify_atomic_fact_known_then_builtin_rules_only(
                &component_in_fact,
                verify_state,
            )?;
            if !component_verify_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "tuple in cart: each component is in the corresponding cart factor".to_string(),
                Vec::new(),
            ))
            .into(),
        )
    }

    // Cartesian-product introduction for a symbolic cart: matching tuple
    // dimension and every coordinate's factor membership prove membership.
    // Example: `$is_cart(C)`, `tuple_dim(p) = cart_dim(C)`, and
    // `forall i closed_range(1, cart_dim(C)): p[i] $in proj(C, i)` imply `p $in C`.
    pub(super) fn try_verify_in_fact_by_symbolic_cart(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let is_cart_fact: AtomicFact =
            IsCartFact::new(in_fact.set.clone(), in_fact.line_file.clone()).into();
        let is_cart_result =
            self.verify_non_equational_known_then_builtin_rules_only(&is_cart_fact, verify_state)?;
        if !is_cart_result.is_true() {
            return Ok(None);
        }

        let is_tuple_fact: AtomicFact =
            IsTupleFact::new(in_fact.element.clone(), in_fact.line_file.clone()).into();
        let is_tuple_result =
            self.verify_non_equational_known_then_builtin_rules_only(&is_tuple_fact, verify_state)?;
        if !is_tuple_result.is_true() {
            return Ok(None);
        }

        let tuple_dim_fact: AtomicFact = EqualFact::new(
            TupleDim::new(in_fact.element.clone()).into(),
            CartDim::new(in_fact.set.clone()).into(),
            in_fact.line_file.clone(),
        )
        .into();
        let tuple_dim_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&tuple_dim_fact, verify_state)?;
        if !tuple_dim_result.is_true() {
            return Ok(None);
        }

        let index_name = self.generate_random_unused_name();
        let index_obj = obj_for_bound_param_in_scope(index_name.clone(), ParamObjType::Forall);
        let index_set: Obj = ClosedRange::new(
            Number::new("1".to_string()).into(),
            CartDim::new(in_fact.set.clone()).into(),
        )
        .into();
        let coordinate_fact: AtomicFact = InFact::new(
            ObjAtIndex::new(in_fact.element.clone(), index_obj.clone()).into(),
            Proj::new(in_fact.set.clone(), index_obj).into(),
            in_fact.line_file.clone(),
        )
        .into();
        let coordinate_forall: Fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![index_name],
                ParamType::Obj(index_set),
            )]),
            vec![],
            vec![coordinate_fact.into()],
            in_fact.line_file.clone(),
        )?
        .into();
        let coordinate_result = self.verify_fact_full(&coordinate_forall, verify_state)?;
        if !coordinate_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "cart membership from symbolic dimension and projections".to_string(),
                vec![
                    is_cart_result,
                    is_tuple_result,
                    tuple_dim_result,
                    coordinate_result,
                ],
            )
            .into(),
        ))
    }
}
