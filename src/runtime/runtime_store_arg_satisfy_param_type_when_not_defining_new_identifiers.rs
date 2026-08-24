use crate::prelude::*;

impl Runtime {
    pub fn store_args_satisfy_param_type_when_not_defining_new_identifiers(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        _line_file: LineFile,
        param_obj_type: ParamObjType,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_args_satisfy_param_type_when_not_defining_new_identifiers_with_reason(
            param_defs,
            args,
            _line_file,
            param_obj_type,
            InferReason::VerifiedStatement,
        )
    }

    pub fn store_args_satisfy_param_type_when_not_defining_new_identifiers_with_reason(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        _line_file: LineFile,
        param_obj_type: ParamObjType,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut infer_result = SuccessInferResult::new();
        for new_fact in self.instantiate_argument_parameter_requirement_facts(
            param_defs,
            args,
            _line_file,
            param_obj_type,
        )? {
            infer_result.new_infer_result_inside(
                self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
                    new_fact,
                    reason.clone(),
                )?,
            );
        }

        Ok(infer_result)
    }

    /// Pure transformation shared by ordinary argument storage and the typed
    /// defined-predicate inference producer. It returns one requirement fact
    /// per argument in source order and performs no store by itself.
    pub fn instantiate_argument_parameter_requirement_facts(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &[Obj],
        line_file: LineFile,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<Fact>, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, &args.to_vec(), param_obj_type)?;
        Ok(args
            .iter()
            .zip(instantiated_types.iter())
            .map(|(argument, parameter_type)| match parameter_type {
                ParamType::Set(_) => IsSetFact::new(argument.clone(), line_file.clone()).into(),
                ParamType::NonemptySet(_) => {
                    IsNonemptySetFact::new(argument.clone(), line_file.clone()).into()
                }
                ParamType::FiniteSet(_) => {
                    IsFiniteSetFact::new(argument.clone(), line_file.clone()).into()
                }
                ParamType::Obj(set) => {
                    InFact::new(argument.clone(), set.clone(), line_file.clone()).into()
                }
            })
            .collect())
    }
}
