use crate::prelude::*;

impl Runtime {
    // Called inside a quantifier's local WD scope. Each carrier may refer to
    // earlier groups, but not to its own or later binders: `A set, a A`.
    pub(crate) fn verify_and_define_wd_parameters(
        &mut self,
        parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<IntroduceTypedParametersResult, VerifyObjWellDefinedResult>> {
        let mut proofs = Vec::with_capacity(parameters.groups.len());
        let mut defined_params = StoreHaveObjAndInferResult::new(Vec::new());
        for group in &parameters.groups {
            let one = TypedParameterList {
                groups: vec![group.clone()],
            };
            let checked =
                self.verify_typed_parameters_well_definedness_or_fail(&one, verify_state.clone())?;
            match checked {
                Ok(mut group_proofs) => proofs.append(&mut group_proofs),
                Err(failed) => return Ok(Err(failed)),
            }
            let defined = self.define_typed_parameters_in_current_env(&one, None, verify_state)?;
            defined_params.extend(defined);
        }
        Ok(Ok(IntroduceTypedParametersResult {
            param_type_well_defined: proofs,
            defined_params,
            auto_opened_struct_layers: None,
        }))
    }

    // One entry per TypedParameterGroup, in source order.
    pub fn verify_typed_parameters_well_definedness(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyParamTypeWellDefinedResult>> {
        let mut out = Vec::new();
        for group in &typed_parameters.groups {
            out.push(
                self.verify_param_type_well_definedness(&group.param_type, verify_state.clone())?,
            );
        }
        Ok(out)
    }

    pub fn verify_param_type_well_definedness(
        &mut self,
        param_type: &ParamType,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyParamTypeWellDefinedResult> {
        let proof = match param_type {
            ParamType::Set(_) => ParamTypeWellDefinedProof::Set,
            ParamType::NonemptySet(_) => ParamTypeWellDefinedProof::NonemptySet,
            ParamType::FiniteSet(_) => ParamTypeWellDefinedProof::FiniteSet,
            ParamType::Obj(obj) => match self.verify_obj_well_definedness(obj, verify_state)? {
                VerifyObjWellDefinedResult::Success(proof) => ParamTypeWellDefinedProof::Obj(proof),
                VerifyObjWellDefinedResult::Failed { obj, reason } => {
                    return Ok(VerifyParamTypeWellDefinedResult::Failed { obj, reason });
                }
            },
        };
        Ok(VerifyParamTypeWellDefinedResult::Success(proof))
    }
}
