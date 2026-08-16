use crate::execute::exec_have_fn_equal_shared::{
    build_curried_fn_value_apply_for_fn_eq, fn_set_to_fn_set_clause,
    forall_binders_dom_and_curried_layers_from_fn_set_clause,
};
use crate::prelude::*;

// Build f(x) as FnObj for a name or anonymous function.
fn fn_obj_apply_one_arg(func: &Obj, arg: Obj) -> Option<Obj> {
    match func {
        Obj::AnonymousFn(af) => Some(
            FnObj::new(
                FnObjHead::AnonymousFnLiteral(Box::new(af.clone())),
                vec![vec![Box::new(arg)]],
            )
            .into(),
        ),
        o => {
            let h = FnObjHead::given_an_atom_return_a_fn_obj_head(o.clone())?;
            Some(FnObj::new(h, vec![vec![Box::new(arg)]]).into())
        }
    }
}

impl Runtime {
    // $fn_eq_in(f,g,S): forall x in S, f(x)=g(x); verified as a ForallFact in a local env.
    pub fn verify_fn_equal_in_fact_with_builtin_rules(
        &mut self,
        f: &FnEqualInFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let x_name = self.generate_random_unused_names(1)[0].clone();
        let x_group =
            self.fresh_param_group_with_type(vec![x_name], ParamType::Obj(f.set.clone()))?;
        // Use the same `Obj` shape as `define_params_with_type(..., Forall, ...)` and as parsed
        // `forall` parameters, so `verify_equal` can match `f(x) = g(x)` from stored `forall` facts.
        let x: Obj = param_binding_element_obj_for_store(&x_group.params[0], ParamObjType::Forall);
        let Some(left_ap) = fn_obj_apply_one_arg(&f.left, x.clone()) else {
            return Ok(StmtUnknown::new().into());
        };
        let Some(right_ap) = fn_obj_apply_one_arg(&f.right, x) else {
            return Ok(StmtUnknown::new().into());
        };
        let param_def = ParamDefWithType::new(vec![x_group]);
        let forall_f = ForallFact::new_canonical_forall(
            param_def,
            vec![],
            vec![EqualFact::new(left_ap, right_ap, f.line_file.clone()).into()],
            f.line_file.clone(),
        )?;
        let forall_res = self.verify_forall_fact(&forall_f, verify_state)?;
        if !forall_res.is_true() {
            return Ok(forall_res);
        }
        let recorded: Fact = f.clone().into();
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                recorded,
                "fn_eq_in: pointwise equality on the given set (forall x in S, f(x)=g(x))"
                    .to_string(),
                vec![forall_res],
            )
            .into(),
        )
    }

    // $fn_eq(f,g): mutual $in, then Forall with params+dom from FnSet and then f(..)=g(..). Name `f(x)` uses
    // Forall binders in the curried apply (see exec_have_fn_equal_shared) so it cites user foralls.
    pub fn verify_fn_equal_fact_with_builtin_rules(
        &mut self,
        f: &FnEqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_t = match fn_set_type_of_function_value(self, &f.left) {
            Some(fs) => fs,
            None => return Ok(StmtUnknown::new().into()),
        };
        let right_t = match fn_set_type_of_function_value(self, &f.right) {
            Some(fs) => fs,
            None => return Ok(StmtUnknown::new().into()),
        };

        // Function extensionality may consume an already checked pointwise forall directly
        // when both declared function carriers are alpha-equivalent. This exact indexed route
        // runs before reconstructing mutual membership, which can otherwise reopen dependent
        // set definitions. Example: `forall x X: f(x) = g(x)` proves `$fn_eq(f, g)` for
        // `f, g fn(x X) Y`, but not for functions with different domains or return carriers.
        if self.fn_sets_are_alpha_equivalent_for_fn_eq(&left_t, &right_t)? {
            let clause = fn_set_to_fn_set_clause(&left_t);
            let (param_def, dom_facts, layers) =
                forall_binders_dom_and_curried_layers_from_fn_set_clause(self, &clause)?;
            let left_ap = match build_curried_fn_value_apply_for_fn_eq(&f.left, &layers) {
                Some(o) => o,
                None => return Ok(StmtUnknown::new().into()),
            };
            let right_ap = match build_curried_fn_value_apply_for_fn_eq(&f.right, &layers) {
                Some(o) => o,
                None => return Ok(StmtUnknown::new().into()),
            };
            let pointwise = ForallFact::new_canonical_forall(
                param_def,
                dom_facts,
                vec![EqualFact::new(left_ap, right_ap, f.line_file.clone()).into()],
                f.line_file.clone(),
            )?;
            let pointwise_result = self.verify_forall_fact(&pointwise, verify_state)?;
            if pointwise_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        f.clone().into(),
                        "fn_eq: exact known pointwise forall over alpha-equivalent function carriers"
                            .to_string(),
                        vec![pointwise_result],
                    )
                    .into(),
                );
            }
        }

        let in_left: AtomicFact = InFact::new(
            f.left.clone(),
            Obj::FnSet(right_t.clone()),
            f.line_file.clone(),
        )
        .into();
        if !self
            .verify_function_value_in_fn_set_explicit(&f.left, &right_t, &in_left, verify_state)?
            .is_true()
        {
            return Ok(StmtUnknown::new().into());
        }
        let in_right: AtomicFact = InFact::new(
            f.right.clone(),
            Obj::FnSet(left_t.clone()),
            f.line_file.clone(),
        )
        .into();
        if !self
            .verify_function_value_in_fn_set_explicit(&f.right, &left_t, &in_right, verify_state)?
            .is_true()
        {
            return Ok(StmtUnknown::new().into());
        }

        let clause = fn_set_to_fn_set_clause(&left_t);
        let (param_def, dom_facts, layers) =
            forall_binders_dom_and_curried_layers_from_fn_set_clause(self, &clause)?;
        let left_ap = match build_curried_fn_value_apply_for_fn_eq(&f.left, &layers) {
            Some(o) => o,
            None => return Ok(StmtUnknown::new().into()),
        };
        let right_ap = match build_curried_fn_value_apply_for_fn_eq(&f.right, &layers) {
            Some(o) => o,
            None => return Ok(StmtUnknown::new().into()),
        };
        let forall_f = ForallFact::new_canonical_forall(
            param_def,
            dom_facts,
            vec![EqualFact::new(left_ap, right_ap, f.line_file.clone()).into()],
            f.line_file.clone(),
        )?;
        let forall_res = self.verify_forall_fact(&forall_f, verify_state)?;
        if !forall_res.is_true() {
            return Ok(forall_res);
        }
        let recorded: Fact = f.clone().into();
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                recorded,
                "fn_eq: mutual function-space membership and pointwise equality (forall+dom)"
                    .to_string(),
                vec![forall_res],
            )
            .into(),
        )
    }

    fn verify_function_value_in_fn_set_explicit(
        &mut self,
        value: &Obj,
        expected: &FnSet,
        membership: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let AtomicFact::InFact(in_fact) = membership else {
            return Ok(StmtUnknown::new().into());
        };
        let known = self.verify_non_equational_atomic_fact_with_known_fact(membership)?;
        if known.is_true() {
            return Ok(known);
        }
        match value {
            Obj::AnonymousFn(anonymous) => self.verify_anonymous_fn_in_fn_set_explicit(
                anonymous,
                expected,
                in_fact,
                verify_state,
            ),
            _ => {
                self.verify_in_fact_element_in_fn_set_by_stored_definition(value, expected, in_fact)
            }
        }
    }

    fn fn_sets_are_alpha_equivalent_for_fn_eq(
        &mut self,
        left: &FnSet,
        right: &FnSet,
    ) -> Result<bool, RuntimeError> {
        let left_obj: Obj = left.clone().into();
        let right_obj: Obj = right.clone().into();
        if objs_equal_with_nested_binder_alpha_equivalence(&left_obj, &right_obj) {
            return Ok(true);
        }
        let left_names = ParamGroupWithSet::collect_param_names(&left.body.params_def_with_set);
        let right_names = ParamGroupWithSet::collect_param_names(&right.body.params_def_with_set);
        if left_names.len() != right_names.len() {
            return Ok(false);
        }
        let shared_names = self.generate_random_unused_names(left_names.len());
        let left_normalized =
            self.fn_set_alpha_renamed_for_display_compare(&left.body, &shared_names)?;
        let right_normalized =
            self.fn_set_alpha_renamed_for_display_compare(&right.body, &shared_names)?;
        Ok(left_normalized.to_string() == right_normalized.to_string())
    }
}

// FnSet “type” for an anonymous fn, a bare FnSet obj, or a name in known_objs_in_fn_sets.
fn fn_set_type_of_function_value(rt: &Runtime, obj: &Obj) -> Option<FnSet> {
    match obj {
        Obj::AnonymousFn(af) => FnSet::new(
            af.body.params_def_with_set.clone(),
            af.body.dom_facts.clone(),
            (*af.body.ret_set).clone(),
        )
        .ok(),
        Obj::FnSet(fs) => Some(fs.clone()),
        Obj::FnObj(fn_obj) => {
            let return_set = rt.fn_obj_return_set_after_application(fn_obj).ok()??;
            match rt.fn_set_space_from_return_set_obj(return_set).ok()? {
                FnSetSpace::Set(fn_set) => Some(fn_set),
                FnSetSpace::Anon(anonymous_fn) => FnSet::new(
                    anonymous_fn.body.params_def_with_set,
                    anonymous_fn.body.dom_facts,
                    (*anonymous_fn.body.ret_set).clone(),
                )
                .ok(),
            }
        }
        o => rt
            .get_cloned_object_in_fn_set(o)
            .and_then(|body| FnSet::from_body(body).ok()),
    }
}
