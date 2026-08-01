use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_satisfies_param_type(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match param_type {
            ParamType::Obj(set_obj) => {
                let fact: AtomicFact =
                    InFact::new(obj.clone(), set_obj.clone(), default_line_file()).into();
                if let Obj::AnonymousFn(anonymous_fn) = &obj {
                    let expected_fn_set = match set_obj {
                        Obj::FnSet(fn_set) => Some(fn_set.clone()),
                        Obj::FiniteSeqSet(set) => {
                            Some(self.finite_seq_set_to_fn_set(set, default_line_file()))
                        }
                        Obj::SeqSet(set) => Some(self.seq_set_to_fn_set(set, default_line_file())),
                        Obj::MatrixSet(set) => {
                            Some(self.matrix_set_to_fn_set(set, default_line_file()))
                        }
                        _ => None,
                    };
                    if let Some(expected_fn_set) = expected_fn_set {
                        self.verify_atomic_fact_well_defined(&fact, verify_state)?;
                        let in_fact = InFact::new(
                            obj.clone(),
                            expected_fn_set.clone().into(),
                            default_line_file(),
                        );
                        return self.verify_in_fact_anonymous_fn_signature_matches_fn_set(
                            anonymous_fn,
                            &expected_fn_set,
                            &in_fact,
                            verify_state,
                        );
                    }
                }
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

    pub fn verify_args_satisfy_param_def_flat_types(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        verify_state: &UseContextVerifyState,
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
            infer_result.new_infer_result_inside(verify_result.infer_result());
        }
        Ok(NonFactualStmtSuccess::new(
            DoNothingStmt::new(default_line_file()).into(),
            infer_result,
            Vec::new(),
        )
        .into())
    }
}
