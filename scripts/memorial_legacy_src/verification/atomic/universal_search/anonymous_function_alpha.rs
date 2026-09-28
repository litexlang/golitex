//! Runtime support for alpha-equivalent anonymous functions.

use super::*;

impl Runtime {
    pub fn objs_match_for_fact_lookup(
        &self,
        known_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<bool, RuntimeError> {
        if known_arg.to_string() == given_arg.to_string() {
            return Ok(true);
        }

        let (Obj::AnonymousFn(known), Obj::AnonymousFn(given)) = (known_arg, given_arg) else {
            return Ok(false);
        };
        self.anonymous_fns_are_alpha_equivalent(known, given)
    }

    pub(in crate::verification) fn anonymous_fns_are_alpha_equivalent(
        &self,
        left: &AnonymousFn,
        right: &AnonymousFn,
    ) -> Result<bool, RuntimeError> {
        let left_param_count =
            SetBoundParameterGroup::number_of_params(&left.body.set_bound_parameters);
        let right_param_count =
            SetBoundParameterGroup::number_of_params(&right.body.set_bound_parameters);
        if left_param_count != right_param_count {
            return Ok(false);
        }

        let alpha_names = Self::anonymous_fn_alpha_param_names(left_param_count);
        let left = self.anonymous_fn_with_alpha_renamed_params(left, &alpha_names)?;
        let right = self.anonymous_fn_with_alpha_renamed_params(right, &alpha_names)?;
        Ok(left.to_string() == right.to_string())
    }

    pub(in crate::verification) fn anonymous_fn_alpha_param_names(
        param_count: usize,
    ) -> Vec<String> {
        (0..param_count)
            .map(|index| format!("#anonymous_fn_alpha_{}", index))
            .collect()
    }

    pub(in crate::verification) fn anonymous_fn_with_alpha_renamed_params(
        &self,
        anonymous_fn: &AnonymousFn,
        alpha_names: &[String],
    ) -> Result<AnonymousFn, RuntimeError> {
        let param_bindings = anonymous_fn
            .body
            .set_bound_parameters
            .collect_param_bindings();
        if param_bindings.len() != alpha_names.len() {
            return Err(VerifyRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "internal: anonymous-function alpha rename needs one name per parameter"
                    .to_string(),
            ))
            .into());
        }

        let alpha_bindings = alpha_names
            .iter()
            .enumerate()
            .map(|(index, name)| SymbolBinding::alpha_canonical(index, name.clone()))
            .collect::<Vec<_>>();
        let mut param_to_alpha_name = HashMap::with_capacity(param_bindings.len() * 2);
        for (param_binding, alpha_binding) in param_bindings.iter().zip(alpha_bindings.iter()) {
            insert_symbol_substitution(
                &mut param_to_alpha_name,
                param_binding,
                obj_for_bound_param_in_scope(alpha_binding),
            );
        }
        self.alpha_rename_anonymous_fn(anonymous_fn, &param_to_alpha_name)
    }
}
