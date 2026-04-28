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
            let h = FnObjHead::from_name_obj(o.clone())?;
            Some(FnObj::new(h, vec![vec![Box::new(arg)]]).into())
        }
    }
}

impl Runtime {
    // $fn_eq_in(f,g,S): forall x in S, f(x)=g(x); verified as a ForallFact in a local env.
    pub fn verify_fn_equal_in_fact_with_builtin_rules(
        &mut self,
        f: &FnEqualInFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let x_name = self.generate_random_unused_names(1)[0].clone();
        // Use the same `Obj` shape as `define_params_with_type(..., Forall, ...)` and as parsed
        // `forall` parameters, so `verify_equal` can match `f(x) = g(x)` from stored `forall` facts.
        let x: Obj = param_binding_element_obj_for_store(x_name.clone(), ParamObjType::Forall);
        let Some(left_ap) = fn_obj_apply_one_arg(&f.left, x.clone()) else {
            return Ok(StmtUnknown::new().into());
        };
        let Some(right_ap) = fn_obj_apply_one_arg(&f.right, x) else {
            return Ok(StmtUnknown::new().into());
        };
        let param_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![x_name],
            ParamType::Obj(f.set.clone()),
        )]);
        let forall_f = ForallFact::new(
            param_def,
            vec![],
            vec![EqualFact::new(left_ap, right_ap, f.line_file.clone()).into()],
            f.line_file.clone(),
        );
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
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_t = match fn_set_type_of_function_value(self, &f.left) {
            Some(fs) => fs,
            None => return Ok(StmtUnknown::new().into()),
        };
        let right_t = match fn_set_type_of_function_value(self, &f.right) {
            Some(fs) => fs,
            None => return Ok(StmtUnknown::new().into()),
        };

        let in_left: AtomicFact = InFact::new(
            f.left.clone(),
            Obj::FnSet(right_t.clone()),
            f.line_file.clone(),
        )
        .into();
        if !self.verify_atomic_fact(&in_left, verify_state)?.is_true() {
            return Ok(StmtUnknown::new().into());
        }
        let in_right: AtomicFact = InFact::new(
            f.right.clone(),
            Obj::FnSet(left_t.clone()),
            f.line_file.clone(),
        )
        .into();
        if !self.verify_atomic_fact(&in_right, verify_state)?.is_true() {
            return Ok(StmtUnknown::new().into());
        }

        let clause = fn_set_to_fn_set_clause(&left_t);
        let (param_def, dom_facts, layers) = forall_binders_dom_and_curried_layers_from_fn_set_clause(&clause);
        let left_ap = match build_curried_fn_value_apply_for_fn_eq(&f.left, &layers) {
            Some(o) => o,
            None => return Ok(StmtUnknown::new().into()),
        };
        let right_ap = match build_curried_fn_value_apply_for_fn_eq(&f.right, &layers) {
            Some(o) => o,
            None => return Ok(StmtUnknown::new().into()),
        };
        let forall_f = ForallFact::new(
            param_def,
            dom_facts,
            vec![EqualFact::new(left_ap, right_ap, f.line_file.clone()).into()],
            f.line_file.clone(),
        );
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
}

// FnSet “type” for an anonymous fn, a bare FnSet obj, or a name in known_objs_in_fn_sets.
fn fn_set_type_of_function_value(rt: &Runtime, obj: &Obj) -> Option<FnSet> {
    match obj {
        Obj::AnonymousFn(af) => Some(FnSet::new(
            af.body.params_def_with_set.clone(),
            af.body.dom_facts.clone(),
            (*af.body.ret_set).clone(),
        )),
        Obj::FnSet(fs) => Some(fs.clone()),
        o => rt
            .get_cloned_object_in_fn_set(o)
            .map(|body| FnSet { body }),
    }
}
