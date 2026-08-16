use crate::prelude::*;

impl Runtime {
    fn verify_obj_satisfies_param_type_known_or_builtin_only(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let fact: AtomicFact = match param_type {
            ParamType::Obj(set_obj) => {
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
                        let in_fact = InFact::new(
                            obj.clone(),
                            expected_fn_set.clone().into(),
                            default_line_file(),
                        );
                        return self.verify_anonymous_fn_in_fn_set_explicit(
                            anonymous_fn,
                            &expected_fn_set,
                            &in_fact,
                            verify_state,
                        );
                    }
                }
                InFact::new(obj, set_obj.clone(), default_line_file()).into()
            }
            ParamType::Set(_) => IsSetFact::new(obj, default_line_file()).into(),
            ParamType::NonemptySet(_) => IsNonemptySetFact::new(obj, default_line_file()).into(),
            ParamType::FiniteSet(_) => IsFiniteSetFact::new(obj, default_line_file()).into(),
        };
        self.verify_atomic_fact_restricted_known_builtin(&fact, verify_state)
    }

    // Definition folding usually receives arguments already stored with their declared
    // carriers. Try that bounded evidence before opening known-forall and strategy search.
    // Example: an exact known `forall V G: preimage(V) in F` can package `Tendsto(f,F,G)`
    // without re-searching the whole environment for the types of X, Y, f, F, and G.
    pub(crate) fn verify_args_satisfy_param_def_known_or_builtin_only(
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
        let mut check_results = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let result = self.verify_obj_satisfies_param_type_known_or_builtin_only(
                arg.clone(),
                param_type,
                verify_state,
            )?;
            if result.is_unknown() {
                return Ok(result);
            }
            infer_result.new_infer_result_inside(result.infer_result());
            check_results.push(result);
        }
        Ok(NonFactualStmtSuccess::new(
            DoNothingStmt::new(default_line_file()).into(),
            infer_result,
            check_results,
        )
        .into())
    }

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
                        return self.verify_anonymous_fn_in_fn_set_explicit(
                            anonymous_fn,
                            &expected_fn_set,
                            &in_fact,
                            verify_state,
                        );
                    }
                }
                let direct_result = self.verify_atomic_fact(&fact, verify_state)?;
                if direct_result.is_true() {
                    return Ok(direct_result);
                }

                // A literal tuple may satisfy a declared dependent structure
                // return type by its immediate field carriers and structure
                // laws. Example: `(n, entries)` returned as `&FiniteList<T,n>`.
                // Keep this constructor check local to typed object/function
                // admission; named members still use their stored membership.
                if let Obj::StructObj(struct_obj) = set_obj {
                    let in_fact = InFact::new(obj, set_obj.clone(), default_line_file());
                    return self.verify_in_fact_by_struct_obj(&in_fact, struct_obj, verify_state);
                }

                Ok(direct_result)
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
        let mut check_results = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let verify_result =
                self.verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)?;
            if verify_result.is_unknown() {
                return Ok(verify_result);
            }
            infer_result.new_infer_result_inside(verify_result.infer_result());
            check_results.push(verify_result);
        }
        Ok(NonFactualStmtSuccess::new(
            DoNothingStmt::new(default_line_file()).into(),
            infer_result,
            check_results,
        )
        .into())
    }
}
