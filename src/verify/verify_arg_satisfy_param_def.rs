use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_satisfies_param_type(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match param_type {
            ParamType::Struct(struct_ty) => {
                let fact =
                    InFact::new(obj, Obj::StructObj(struct_ty.clone()), default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
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
        }
    }

    /// 对每个实参调用 [`Self::verify_obj_satisfies_param_type`]（含 `family` / `struct`），并合并各步的 [`InferResult`]。
    pub fn verify_args_satisfy_param_def_flat_types(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types = self.inst_param_def_with_type_one_by_one(param_defs, args)?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let verify_result = self
                .verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)?;
            if verify_result.is_unknown() {
                return Err(
                    RuntimeError::new_unknown_error_with_msg_position_optional_stmt_previous_error(
                        format!(
                            "argument {} does not satisfy parameter type (unknown): {}",
                            arg, param_type
                        ),
                        default_line_file(),
                        None,
                        None,
                    )
                    .into(),
                );
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
        Ok(infer_result)
    }
}

impl Runtime {}
