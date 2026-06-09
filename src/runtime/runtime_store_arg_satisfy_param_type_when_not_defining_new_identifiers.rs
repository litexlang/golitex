use crate::prelude::*;

impl Runtime {
    pub fn store_args_satisfy_param_type_when_not_defining_new_identifiers(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        _line_file: LineFile,
        param_obj_type: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
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
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args, param_obj_type)?;

        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(instantiated_types.iter()) {
            let new_fact: Fact = match param_type {
                ParamType::Set(_) => IsSetFact::new(arg.clone(), _line_file.clone()).into(),
                ParamType::NonemptySet(_) => {
                    IsNonemptySetFact::new(arg.clone(), _line_file.clone()).into()
                }
                ParamType::FiniteSet(_) => {
                    IsFiniteSetFact::new(arg.clone(), _line_file.clone()).into()
                }
                ParamType::Obj(obj) => {
                    InFact::new(arg.clone(), obj.clone(), _line_file.clone()).into()
                }
            };
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                    new_fact,
                    reason.clone(),
                )?,
            );
        }

        Ok(infer_result)
    }
}
