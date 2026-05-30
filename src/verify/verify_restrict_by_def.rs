// restrict_fn_in proof pipeline:
// step1: forall on RHS params, verify f(x, ...) is well-defined.
// step2: get known fn-set info of f from env.
// step2_1: if known return-set equals RHS return-set, accept immediately.
// step2_2: otherwise prove forall RHS params: f(x, ...) is in RHS return-set.

// Example:
// have f fn(x R, y Q: x < y) Z
// restrict_fn_in(f, fn(a Q, b Q: x < y, x < 0) Z)
// 1. prove forall a Q, b Q: x < y: f(a, b) is well-defined.
// 2. prove restriction keeps outputs in Z.
// 2.1 if known return_set of f is already Z, return success directly.
// 2.2 otherwise build and verify:
//     forall a Q, b Q: x < y, x < 0: f(a, b) $in Z

use crate::prelude::*;
use std::collections::HashMap;
struct RestrictProofFlow {
    // The whole restrict_fn_in(...) fact to be proved.
    restrict_fact: RestrictFact,
    // The RHS function set in restrict_fn_in, e.g. fn(a Q, b Q: x < y, x < 0) Z.
    rhs_fn_set: FnSet,
    // Known function-set body of f from env, e.g. fn(x R, y Q: x < y) Z.
    known_fn_body: FnSetBody,
    // Forall binders for step 1/2.2, e.g. a Q, b Q.
    forall_params: ParamDefWithType,
    // Forall domain facts for step 1/2.2, e.g. x < y, x < 0.
    forall_dom_facts: Vec<Fact>,
    // Applied function object under forall vars, e.g. f(a, b).
    applied_fn_obj: Obj,
}

impl Runtime {
    // Restricts an anonymous function by verifying the target function domain is a valid subdomain
    // for the anonymous function and that outputs stay in the requested return set.
    // Example: `$restrict_fn_in('R(x){x + 1}, fn(x closed_range(1, 2)) R)`.
    pub fn verify_restrict_fact_using_its_definition(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        self.restrict_step_0_verify_input_objects_well_defined(restrict_fact, verify_state)?;

        let flow = match self.restrict_step_2_build_flow_from_env(restrict_fact)? {
            Some(v) => v,
            None => return Ok(None),
        };

        self.restrict_step_1_verify_forall_application_well_defined(&flow, verify_state)?;

        if let Some(success) = self.restrict_step_2_1_try_return_set_shortcut(&flow) {
            return Ok(Some(success));
        }

        self.restrict_step_2_2_prove_forall_membership_in_rhs_return_set(flow, verify_state)
    }

    fn restrict_wrap_verify_runtime_error(
        restrict_fact: &RestrictFact,
        cause: RuntimeError,
    ) -> RuntimeError {
        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
            Some(Fact::from(restrict_fact.clone()).into_stmt()),
            String::new(),
            restrict_fact.line_file.clone(),
            Some(cause),
            vec![],
        )))
    }

    fn restrict_step_0_verify_input_objects_well_defined(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&restrict_fact.obj, verify_state)
            .map_err(|e| Self::restrict_wrap_verify_runtime_error(restrict_fact, e))?;
        self.verify_obj_well_defined_and_store_cache(
            &restrict_fact.obj_can_restrict_to_fn_set,
            verify_state,
        )
        .map_err(|e| Self::restrict_wrap_verify_runtime_error(restrict_fact, e))?;
        Ok(())
    }

    fn restrict_step_2_build_flow_from_env(
        &mut self,
        restrict_fact: &RestrictFact,
    ) -> Result<Option<RestrictProofFlow>, RuntimeError> {
        let rhs_fn_set = match &restrict_fact.obj_can_restrict_to_fn_set {
            Obj::FnSet(v) => v.clone(),
            _ => return Ok(None),
        };

        let known_fn_body =
            self.restrict_step_2_get_known_fn_set_info(&restrict_fact.obj, restrict_fact)?;

        let rhs_flat_param_names = self.restrict_collect_flat_param_names(&rhs_fn_set.body);
        let known_flat_param_names = self.restrict_collect_flat_param_names(&known_fn_body);
        if rhs_flat_param_names.len() != known_flat_param_names.len() {
            return Ok(None);
        }

        let forall_params = self.restrict_build_forall_params_from_rhs(&rhs_fn_set.body)?;
        let forall_dom_facts = self.restrict_build_forall_dom_facts_from_rhs(&rhs_fn_set.body);

        let fn_head = match Self::restrict_fn_head_for_obj(&restrict_fact.obj) {
            Some(v) => v,
            None => return Ok(None),
        };
        let applied_fn_obj: Obj = FnObj::new(
            fn_head,
            self.restrict_build_full_application_arg_groups(&known_fn_body, &rhs_flat_param_names),
        )
        .into();

        Ok(Some(RestrictProofFlow {
            restrict_fact: restrict_fact.clone(),
            rhs_fn_set,
            known_fn_body,
            forall_params,
            forall_dom_facts,
            applied_fn_obj,
        }))
    }

    fn restrict_step_2_get_known_fn_set_info(
        &self,
        function: &Obj,
        restrict_fact: &RestrictFact,
    ) -> Result<FnSetBody, RuntimeError> {
        if let Obj::AnonymousFn(anonymous_fn) = function {
            return Ok(anonymous_fn.body.clone());
        }
        match self.get_cloned_object_in_fn_set(function) {
            Some(v) => Ok(v),
            None => match self.get_cloned_object_in_fn_set_or_restrict(function) {
                Some(v) => Ok(v),
                None => Err(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(restrict_fact.clone()).into_stmt()),
                    String::new(),
                    restrict_fact.line_file.clone(),
                    Some(
                        WellDefinedRuntimeError(RuntimeErrorStruct::new(
                            None,
                            format!(
                                "function `{}` belongs to what function set is unknown",
                                function.to_string()
                            ),
                            default_line_file(),
                            None,
                            vec![],
                        ))
                        .into(),
                    ),
                    vec![],
                ))
                .into()),
            },
        }
    }

    fn restrict_fn_head_for_obj(function: &Obj) -> Option<FnObjHead> {
        match function {
            Obj::AnonymousFn(anonymous_fn) => Some(FnObjHead::AnonymousFnLiteral(Box::new(
                anonymous_fn.clone(),
            ))),
            _ => FnObjHead::given_an_atom_return_a_fn_obj_head(function.clone()),
        }
    }

    fn restrict_step_1_verify_forall_application_well_defined(
        &mut self,
        flow: &RestrictProofFlow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.restrict_step_1_verify_by_local_param_def(flow, verify_state)?;
        self.restrict_step_1_verify_under_rhs_dom_facts(flow, verify_state)?;
        Ok(())
    }

    fn restrict_step_1_verify_by_local_param_def(
        &mut self,
        flow: &RestrictProofFlow,
        _verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_with_its_local_def(
            flow.rhs_fn_set.body.params_def_with_set.clone(),
            ParamObjType::Forall,
            flow.applied_fn_obj.clone(),
        )
        .map_err(|e| Self::restrict_wrap_verify_runtime_error(&flow.restrict_fact, e))
    }

    fn restrict_step_1_verify_under_rhs_dom_facts(
        &mut self,
        flow: &RestrictProofFlow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let stub = ForallFact::new(
            flow.forall_params.clone(),
            flow.forall_dom_facts.clone(),
            Vec::new(),
            flow.restrict_fact.line_file.clone(),
        )?;
        self.run_in_local_env(|rt| {
            rt.forall_assume_params_and_dom_in_current_env(&stub, verify_state)?;
            rt.verify_obj_well_defined_and_store_cache(&flow.applied_fn_obj, verify_state)
        })
        .map_err(|e| Self::restrict_wrap_verify_runtime_error(&flow.restrict_fact, e))
    }

    fn restrict_step_2_1_try_return_set_shortcut(
        &self,
        flow: &RestrictProofFlow,
    ) -> Option<StmtResult> {
        if crate::verify::verify_equality_by_builtin_rules::objs_equal_by_display_string(
            flow.known_fn_body.ret_set.as_ref(),
            flow.rhs_fn_set.body.ret_set.as_ref(),
        ) {
            return Some(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    flow.restrict_fact.clone().into(),
                    "restrict_fn_in: well-defined on narrowed domain; known fn_set already has same return_set"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        None
    }

    fn restrict_step_2_2_prove_forall_membership_in_rhs_return_set(
        &mut self,
        flow: RestrictProofFlow,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let then_facts = vec![InFact::new(
            flow.applied_fn_obj.clone(),
            (*flow.rhs_fn_set.body.ret_set).clone(),
            flow.restrict_fact.line_file.clone(),
        )
        .into()];

        let forall = ForallFact::new(
            flow.forall_params,
            flow.forall_dom_facts,
            then_facts,
            flow.restrict_fact.line_file.clone(),
        )?;

        let forall_result = self.verify_forall_fact(&forall, verify_state)?;
        if !forall_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                flow.restrict_fact.clone().into(),
                "restrict_fn_in: forall on narrowed domain; outputs in stated return set"
                    .to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn restrict_collect_flat_param_names(&self, body: &FnSetBody) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        for g in body.params_def_with_set.iter() {
            for name in g.params.iter() {
                out.push(name.clone());
            }
        }
        out
    }

    fn restrict_build_forall_params_from_rhs(
        &self,
        rhs_body: &FnSetBody,
    ) -> Result<ParamDefWithType, RuntimeError> {
        let mut groups: Vec<ParamGroupWithParamType> = Vec::new();
        let mut param_to_forall_obj: HashMap<String, Obj> = HashMap::new();
        for param_def_with_set in &rhs_body.params_def_with_set {
            let param_type = ParamType::Obj(self.inst_obj(
                param_def_with_set.set_obj(),
                &param_to_forall_obj,
                ParamObjType::FnSet,
            )?);
            groups.push(ParamGroupWithParamType::new(
                param_def_with_set.params.clone(),
                param_type,
            ));
            for param_name in param_def_with_set.params.iter() {
                param_to_forall_obj.insert(
                    param_name.clone(),
                    obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall),
                );
            }
        }
        Ok(ParamDefWithType::new(groups))
    }

    fn restrict_build_forall_dom_facts_from_rhs(&self, rhs_body: &FnSetBody) -> Vec<Fact> {
        let mut out: Vec<Fact> = Vec::new();
        for dom_fact in rhs_body.dom_facts.iter() {
            let chain: OrAndChainAtomicFact = dom_fact.clone();
            out.push(chain.into());
        }
        out
    }

    fn restrict_build_full_application_arg_groups(
        &self,
        known_fn_body: &FnSetBody,
        rhs_flat_param_names: &[String],
    ) -> Vec<Vec<Box<Obj>>> {
        let mut all_args: Vec<Box<Obj>> = Vec::new();
        let mut index: usize = 0;
        for param_group in known_fn_body.params_def_with_set.iter() {
            for _ in param_group.params.iter() {
                let rhs_param_name = rhs_flat_param_names[index].clone();
                all_args.push(Box::new(obj_for_bound_param_in_scope(
                    rhs_param_name,
                    ParamObjType::Forall,
                )));
                index += 1;
            }
        }
        vec![all_args]
    }
}
