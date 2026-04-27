use crate::prelude::*;

/// Build `f(x)` / `f (x)` as a [`FnObj`] when `f` is a name or anonymous function value.
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
    /// Builtin: `$fn_eq_in(f,g,S)` holds iff `forall x : x ∈ S` in the param typing, `f(x) = g(x)`;
    /// we verify the equivalent [`ForallFact`] in a fresh local environment.
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
}
