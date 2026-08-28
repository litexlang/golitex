//! Tuple and Cartesian equality from dimensions and projections.

use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    // Tuple extensionality: a tuple is equal to `(a, b, ...)` when its dimension matches
    // and each projection matches the corresponding component.
    // Example: from `tuple_dim(t) = 2`, `t[1] = a`, and `t[2] = b`, prove `t = (a, b)`.
    pub fn try_verify_tuple_equality_from_dim_and_projections(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (tuple_obj, target_obj) = match (left, right) {
            (target_obj, Obj::Tuple(tuple_obj)) => (tuple_obj, target_obj),
            (Obj::Tuple(tuple_obj), target_obj) => (tuple_obj, target_obj),
            _ => return Ok(None),
        };

        if matches!(target_obj, Obj::Tuple(_)) {
            return Ok(None);
        }

        let is_tuple_fact: AtomicFact =
            IsTupleFact::new(target_obj.clone(), line_file.clone()).into();
        let is_tuple_result = self.verify_atomic_fact(&is_tuple_fact, verify_state)?;
        if !is_tuple_result.is_success() {
            return Ok(None);
        }

        let tuple_dim_obj: Obj = TupleDim::new(target_obj.clone()).into();
        let tuple_dim_value_obj: Obj = Number::new(tuple_obj.args.len().to_string()).into();
        let tuple_dim_fact: AtomicFact =
            EqualFact::new(tuple_dim_obj, tuple_dim_value_obj, line_file.clone()).into();
        let tuple_dim_result = self.verify_atomic_fact(&tuple_dim_fact, verify_state)?;
        if !tuple_dim_result.is_success() {
            return Ok(None);
        }

        let mut steps = vec![is_tuple_result, tuple_dim_result];
        for (index, arg) in tuple_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            let projected_obj: Obj = ObjAtIndex::new(target_obj.clone(), index_obj).into();
            let component_fact: AtomicFact =
                EqualFact::new(projected_obj, arg.as_ref().clone(), line_file.clone()).into();
            let component_result = self.verify_atomic_fact(&component_fact, verify_state)?;
            if !component_result.is_success() {
                return Ok(None);
            }
            steps.push(component_result);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "tuple equality from dimension and projections".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyTupleEqualityFromDimAndProjections,
                ),
                steps,
            )
            .into(),
        ))
    }

    // Tuple extensionality for symbolic dimensions: equal tuples have equal
    // coordinates on their common index range. Example: `tuple_dim(p) = n`,
    // `tuple_dim(q) = n`, and `forall i closed_range(1, n): p[i] = q[i]`
    // prove `p = q`.
    pub fn try_verify_symbolic_tuple_equality_from_coordinates(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let left_is_direct_symbol = matches!(
            left,
            Obj::Atom(AtomObj::Identifier(_) | AtomObj::IdentifierWithMod(_) | AtomObj::Bound(_))
        );
        let right_is_direct_symbol = matches!(
            right,
            Obj::Atom(AtomObj::Identifier(_) | AtomObj::IdentifierWithMod(_) | AtomObj::Bound(_))
        );
        if !left_is_direct_symbol || !right_is_direct_symbol {
            return Ok(None);
        }

        let left_is_tuple: AtomicFact = IsTupleFact::new(left.clone(), line_file.clone()).into();
        let left_is_tuple_result = self.verify_atomic_fact(&left_is_tuple, verify_state)?;
        if !left_is_tuple_result.is_success() {
            return Ok(None);
        }

        let right_is_tuple: AtomicFact = IsTupleFact::new(right.clone(), line_file.clone()).into();
        let right_is_tuple_result = self.verify_atomic_fact(&right_is_tuple, verify_state)?;
        if !right_is_tuple_result.is_success() {
            return Ok(None);
        }

        let left_dim: Obj = TupleDim::new(left.clone()).into();
        let right_dim: Obj = TupleDim::new(right.clone()).into();
        let same_dim: AtomicFact =
            EqualFact::new(left_dim.clone(), right_dim, line_file.clone()).into();
        let same_dim_result = self.verify_atomic_fact(&same_dim, verify_state)?;
        if !same_dim_result.is_success() {
            return Ok(None);
        }

        let dimension_is_positive: AtomicFact = LessEqualFact::new(
            Number::new("1".to_string()).into(),
            left_dim.clone(),
            line_file.clone(),
        )
        .into();
        let dimension_is_positive_result =
            self.verify_atomic_fact(&dimension_is_positive, verify_state)?;
        if !dimension_is_positive_result.is_success() {
            return Ok(None);
        }

        let index_name = self.generate_random_unused_name();
        let coordinate_group = self.fresh_param_group_with_type(
            vec![index_name],
            ParamType::Obj(ClosedRange::new(Number::new("1".to_string()).into(), left_dim).into()),
        )?;
        let index_obj = obj_for_bound_param_in_scope(&coordinate_group.params[0]);
        let coordinate_equality: AtomicFact = EqualFact::new(
            ObjAtIndex::new(left.clone(), index_obj.clone()).into(),
            ObjAtIndex::new(right.clone(), index_obj).into(),
            line_file.clone(),
        )
        .into();
        let coordinate_params = TypedParameterList::new(vec![coordinate_group]);
        let coordinate_result = self.run_in_local_env(|rt| {
            rt.define_params_with_type(&coordinate_params, false, BindingScope::LocalBinder)?;
            rt.verify_atomic_fact_with_known_forall(&coordinate_equality, verify_state)
        })?;
        if !coordinate_result.is_success() {
            return Ok(None);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "tuple equality from symbolic dimension and coordinates".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifySymbolicTupleEqualityFromCoordinates,
                ),
                vec![
                    left_is_tuple_result,
                    right_is_tuple_result,
                    same_dim_result,
                    dimension_is_positive_result,
                    coordinate_result,
                ],
            )
            .into(),
        ))
    }

    // Cart extensionality: a cart object is equal to `cart(A, B, ...)` when it is a cart,
    // its dimension matches, and each factor projection matches the corresponding literal cart
    // factor.
    // Example: from `$is_cart(c)`, `cart_dim(c) = 3`, and `proj(c, i) = R`, prove
    // `c = cart(R, R, R)`.
    pub(super) fn try_verify_cart_equality_from_dim_and_projections(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (cart_obj, target_obj) = match (left, right) {
            (target_obj, Obj::Cart(cart_obj)) => (cart_obj, target_obj),
            (Obj::Cart(cart_obj), target_obj) => (cart_obj, target_obj),
            _ => return Ok(None),
        };

        if matches!(target_obj, Obj::Cart(_)) {
            return Ok(None);
        }

        let is_cart_fact: AtomicFact =
            IsCartFact::new(target_obj.clone(), line_file.clone()).into();
        let cart_dim_obj: Obj = CartDim::new(target_obj.clone()).into();
        let cart_dim_value_obj: Obj = Number::new(cart_obj.args.len().to_string()).into();
        let cart_dim_fact: AtomicFact =
            EqualFact::new(cart_dim_obj, cart_dim_value_obj, line_file.clone()).into();
        let mut complete_premises = vec![is_cart_fact.clone(), cart_dim_fact.clone()];
        for (index, arg) in cart_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            complete_premises.push(
                EqualFact::new(
                    Proj::new(target_obj.clone(), index_obj).into(),
                    arg.as_ref().clone(),
                    line_file.clone(),
                )
                .into(),
            );
        }
        if let Some(steps) = self.verify_builtin_rule_premises(&complete_premises, builtin_state)? {
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "cart equality from dimension and projections".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyCartEqualityFromDimAndProjections01,
                    ),
                    steps,
                )
                .into(),
            ));
        }

        let is_cart_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&is_cart_fact, builtin_state)?;
        if !is_cart_result.is_success() {
            return Ok(None);
        }

        let cart_dim_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&cart_dim_fact, builtin_state)?;
        if !cart_dim_result.is_success() {
            return Ok(None);
        }

        let mut steps = vec![is_cart_result, cart_dim_result];
        for (index, arg) in cart_obj.args.iter().enumerate() {
            let index_obj: Obj = Number::new((index + 1).to_string()).into();
            let projected_target: Obj = Proj::new(target_obj.clone(), index_obj).into();
            let projection_fact: AtomicFact =
                EqualFact::new(projected_target, arg.as_ref().clone(), line_file.clone()).into();
            let mut projection_result =
                self.verify_atomic_fact_as_builtin_rule_premise(&projection_fact, builtin_state)?;
            if !projection_result.is_success() {
                if let Some(known_forall_result) =
                    self.verify_exact_cart_projection_from_known_forall(&projection_fact)?
                {
                    projection_result = known_forall_result;
                }
            }
            if !projection_result.is_success() {
                return Ok(None);
            }
            steps.push(projection_result);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "cart equality from dimension and projections".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyCartEqualityFromDimAndProjections02,
                ),
                steps,
            )
            .into(),
        ))
    }

    pub(super) fn verify_exact_cart_projection_from_known_forall(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lookup_key = (goal.key(), goal.has_positive_polarity());
        let candidates: Vec<(AtomicFact, Rc<StoredForallConclusionReference>)> = self
            .iter_environments_from_top()
            .flat_map(|environment| {
                environment
                    .facts
                    .forall_conclusions
                    .atomic_with_parameterized_head
                    .get(&lookup_key)
                    .into_iter()
                    .flat_map(|facts| facts.iter())
                    .chain(
                        environment
                            .facts
                            .forall_conclusions
                            .atomic_by_argument_shape
                            .get(&lookup_key)
                            .into_iter()
                            .flat_map(|shape_map| shape_map.values())
                            .flat_map(|facts| facts.iter()),
                    )
            })
            .cloned()
            .collect();
        // We have already selected the exact stored forall that can prove this
        // projection. Its domain requirements may use known facts and builtin
        // computation, but must not start another equality/forall search and
        // recursively re-enter cart extensionality.
        let verify_state = VerifyState::after_well_definedness().with_next_round();
        for (pattern, forall_context) in candidates {
            let Some(arg_map) = self.match_atomic_fact_args_against_known_forall_ordered_args(
                &pattern,
                goal,
                &forall_context.params_def,
            )?
            else {
                continue;
            };
            if let Some(success) = self.verify_args_satisfy_forall_requirements(
                &pattern,
                &forall_context,
                arg_map,
                goal,
                &verify_state,
            )? {
                return Ok(Some(success.into()));
            }
        }
        Ok(None)
    }
}
