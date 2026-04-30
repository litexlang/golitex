use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_satisfies_param_type(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match param_type {
            ParamType::Obj(set_obj) => {
                let fact = InFact::new(obj, set_obj.clone(), default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::Set(_) => {
                let fact = IsSetFact::new(obj, default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::NonemptySet(_) => {
                let fact = IsNonemptySetFact::new(obj, default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::FiniteSet(_) => {
                let fact = IsFiniteSetFact::new(obj, default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::Restrictive(fs) => {
                let restrict_fact =
                    RestrictFact::new(obj.clone(), fs.clone().into(), default_line_file()).into();
                let restrict_res = self.verify_atomic_fact(&restrict_fact, verify_state)?;
                if restrict_res.is_true() {
                    return Ok(restrict_res);
                }
                // `restrictive (fn …)` is `$restrict_fn_in` shape. Proving the definition often
                // repeats a `forall` that membership `f $in fn …` already encodes when the type is
                // exactly this function space; the dedicated proof may still return unknown.
                let membership = InFact::new(obj, fs.clone().into(), default_line_file()).into();
                self.verify_atomic_fact(&membership, verify_state)
            }
        }
    }

    pub fn verify_args_satisfy_param_def_flat_types(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        verify_state: &VerifyState,
        to_inst_param_type: ParamObjType,
    ) -> Result<StmtResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args, to_inst_param_type)?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let verify_result =
                self.verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)?;
            if verify_result.is_unknown() {
                return Ok(verify_result);
            }
            match verify_result {
                StmtResult::NonFactualStmtSuccess(x) => {
                    infer_result.new_infer_result_inside(x.infers);
                }
                StmtResult::FactualStmtSuccess(x) => {
                    infer_result.new_infer_result_inside(x.infers);
                }
                StmtResult::StmtUnknown(_) => unreachable!(),
            }
        }
        Ok(NonFactualStmtSuccess::new(
            DoNothingStmt::new(default_line_file()).into(),
            infer_result,
            Vec::new(),
        )
        .into())
    }
}
