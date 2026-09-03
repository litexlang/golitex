//! Set-builder, Cartesian, function-set, and anonymous-function binders.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_set_builder(
        &mut self,
        left: &SetBuilder,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::SetBuilder(given) = given_arg else {
            return Ok(None);
        };
        let shared_binding = self.allocate_internal_symbol_binding()?;
        let mut left_rename_map = HashMap::new();
        insert_symbol_substitution(
            &mut left_rename_map,
            &left.param_binding,
            obj_for_bound_param_in_scope(&shared_binding),
        );
        let mut given_rename_map = HashMap::new();
        insert_symbol_substitution(
            &mut given_rename_map,
            &given.param_binding,
            obj_for_bound_param_in_scope(&shared_binding),
        );
        let left = self.alpha_rename_set_builder(left, &left_rename_map)?;
        let given = self.alpha_rename_set_builder(given, &given_rename_map)?;
        self.match_alpha_renamed_set_builder(&left, &given)
    }

    pub(super) fn match_alpha_renamed_set_builder(
        &mut self,
        left: &SetBuilder,
        given: &SetBuilder,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.param_name() != given.param_name() {
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
            let Some(fact_map) = self.match_arg_quantifier_free_fact_in_known_forall(lf, gf)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let verify_state = VerifyState::final_round();
        for value in merged.values() {
            if self
                .verify_obj_well_defined_result(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    pub(super) fn match_arg_when_left_is_general_cart(
        &mut self,
        left: &GeneralCart,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::GeneralCart(given) = given_arg else {
            return Ok(None);
        };
        self.match_args_in_active_binding_scope(
            &[
                left.index_set.as_ref(),
                left.family_set.as_ref(),
                left.family_fn.as_ref(),
            ],
            &[
                given.index_set.as_ref(),
                given.family_set.as_ref(),
                given.family_fn.as_ref(),
            ],
        )
    }

    pub(super) fn match_arg_when_left_is_fn_set_with_params(
        &mut self,
        left: &FnSet,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FnSet(given) = given_arg else {
            return Ok(None);
        };
        let left_param_count =
            SetBoundParameterGroup::number_of_params(&left.body.set_bound_parameters);
        let given_param_count =
            SetBoundParameterGroup::number_of_params(&given.body.set_bound_parameters);
        if left_param_count != given_param_count {
            return Ok(None);
        }
        let alpha_names = Runtime::anonymous_fn_alpha_param_names(left_param_count);
        let Obj::FnSet(left) =
            self.fn_set_alpha_renamed_for_display_compare(&left.body, &alpha_names)?
        else {
            unreachable!("function-set alpha normalization must return a function set");
        };
        let Obj::FnSet(given) =
            self.fn_set_alpha_renamed_for_display_compare(&given.body, &alpha_names)?
        else {
            unreachable!("function-set alpha normalization must return a function set");
        };
        self.match_alpha_renamed_fn_set_with_params(&left, &given)
    }

    pub(super) fn match_alpha_renamed_fn_set_with_params(
        &mut self,
        left: &FnSet,
        given: &FnSet,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.body.set_bound_parameters.len() != given.body.set_bound_parameters.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lg, gg) in left
            .body
            .set_bound_parameters
            .iter()
            .zip(given.body.set_bound_parameters.iter())
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
            let Some(fact_map) = self.match_arg_quantifier_free_fact_in_known_forall(lf, gf)?
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
        let verify_state = VerifyState::final_round();
        for value in merged.values() {
            if self
                .verify_obj_well_defined_result(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    pub(super) fn match_arg_when_left_is_anonymous_fn_with_params(
        &mut self,
        left: &AnonymousFn,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::AnonymousFn(given) = given_arg else {
            return Ok(None);
        };

        let left_param_count =
            SetBoundParameterGroup::number_of_params(&left.body.set_bound_parameters);
        let given_param_count =
            SetBoundParameterGroup::number_of_params(&given.body.set_bound_parameters);
        if left_param_count != given_param_count {
            return Ok(None);
        }

        // Anonymous-function parameter names are binders, not part of the
        // function value.  Rename both sides to the same internal names before
        // matching their domains and bodies.  For example, `fn(k R) R {k}` and
        // `fn(i R) R {i}` must match here.
        let alpha_names = Runtime::anonymous_fn_alpha_param_names(left_param_count);
        let left = self.anonymous_fn_with_alpha_renamed_params(left, &alpha_names)?;
        let given = self.anonymous_fn_with_alpha_renamed_params(given, &alpha_names)?;
        self.match_alpha_renamed_anonymous_fn_with_params(&left, &given)
    }

    pub(super) fn match_alpha_renamed_anonymous_fn_with_params(
        &mut self,
        left: &AnonymousFn,
        given: &AnonymousFn,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.body.set_bound_parameters.len() != given.body.set_bound_parameters.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lg, gg) in left
            .body
            .set_bound_parameters
            .iter()
            .zip(given.body.set_bound_parameters.iter())
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
            let Some(fact_map) = self.match_arg_quantifier_free_fact_in_known_forall(lf, gf)?
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
            let verify_state = VerifyState::final_round();
            for value in merged.values() {
                if self
                    .verify_obj_well_defined_result(value, &verify_state)
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
        let verify_state = VerifyState::final_round();
        for value in merged.values() {
            if self
                .verify_obj_well_defined_result(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }
}
