//! Checks that instantiated arguments satisfy defined parameter requirements.

use crate::prelude::*;

impl Runtime {
    /// Parameter checks are recursively consumed by theorem application,
    /// definition folding, and the Lean compiler rather than executed as
    /// standalone statements. Retain the exact WD Result here just as
    /// submitted-fact execution does; otherwise the successful proof may cite
    /// intrinsic object-membership FactIds whose producing Result was lost.
    fn verify_atomic_parameter_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&fact.clone().into(), verify_state)
    }

    fn verify_atomic_parameter_fact_known_or_builtin_only(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_atomic_fact_restricted_known_builtin(fact, verify_state)
    }

    fn verify_obj_satisfies_param_type_known_or_builtin_only(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
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
                        let in_fact = self.new_in_fact(
                            obj.clone(),
                            expected_fn_set.clone().into(),
                            default_line_file(),
                        );
                        let result = self.verify_anonymous_fn_in_fn_set_explicit(
                            anonymous_fn,
                            &expected_fn_set,
                            &in_fact,
                            verify_state,
                        )?;
                        let checked = self.verify_fact_well_defined_result(
                            &in_fact.clone().into(),
                            verify_state,
                        )?;
                        return Ok(Runtime::finish_fact_verification(checked, result));
                    }
                }
                self.new_in_fact(obj, set_obj.clone(), default_line_file())
                    .into()
            }
            ParamType::Set(_) => self.new_is_set_fact(obj, default_line_file()).into(),
            ParamType::NonemptySet(_) => self
                .new_is_nonempty_set_fact(obj, default_line_file())
                .into(),
            ParamType::FiniteSet(_) => self.new_is_finite_set_fact(obj, default_line_file()).into(),
        };
        self.verify_atomic_parameter_fact_known_or_builtin_only(&fact, verify_state)
    }

    // Definition folding usually receives arguments already stored with their defined
    // carriers. Try that bounded evidence before opening known-forall and strategy search.
    // Example: an exact known `forall V G: preimage(V) in F` can package `Tendsto(f,F,G)`
    // without re-searching the whole environment for the types of X, Y, f, F, and G.
    pub fn verify_args_satisfy_param_def_known_or_builtin_only(
        &mut self,
        param_defs: &TypedParameterList,
        args: &[Obj],
        verify_state: &VerifyState,
        substitution_mode: SubstitutionMode,
    ) -> Result<VerifyArgsSatisfyParamDefResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args, substitution_mode)?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let infer_result = SuccessInferResult::new();
        let mut check_results = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let result = self.verify_obj_satisfies_param_type_known_or_builtin_only(
                arg.clone(),
                param_type,
                verify_state,
            )?;
            if result.is_unknown() {
                return Ok(VerifyArgsSatisfyParamDefResult::unknown(result));
            }
            check_results.push(result);
        }
        Ok(VerifyArgsSatisfyParamDefResult::success(
            check_results,
            infer_result,
        ))
    }

    pub fn verify_obj_satisfies_param_type(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        match param_type {
            ParamType::Obj(set_obj) => {
                let fact: AtomicFact = self
                    .new_in_fact(obj.clone(), set_obj.clone(), default_line_file())
                    .into();
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
                        let in_fact = self.new_in_fact(
                            obj.clone(),
                            expected_fn_set.clone().into(),
                            default_line_file(),
                        );
                        let result = self.verify_anonymous_fn_in_fn_set_explicit(
                            anonymous_fn,
                            &expected_fn_set,
                            &in_fact,
                            verify_state,
                        )?;
                        let checked = self.verify_fact_well_defined_result(
                            &in_fact.clone().into(),
                            verify_state,
                        )?;
                        return Ok(Runtime::finish_fact_verification(checked, result));
                    }
                }
                let direct_result = self.verify_atomic_parameter_fact(&fact, verify_state)?;
                if direct_result.is_success() {
                    return Ok(direct_result);
                }

                // A literal tuple may satisfy a defined dependent structure
                // return type by its immediate field carriers and structure
                // laws. Example: `(n, entries)` returned as `&FiniteList<T,n>`.
                // Keep this constructor check local to typed object/function
                // admission; named members still use their stored membership.
                if let Obj::StructObj(struct_obj) = set_obj {
                    let in_fact = self.new_in_fact(obj, set_obj.clone(), default_line_file());
                    let result =
                        self.verify_in_fact_by_struct_obj(&in_fact, struct_obj, verify_state)?;
                    let checked = self
                        .verify_fact_well_defined_result(&in_fact.clone().into(), verify_state)?;
                    return Ok(Runtime::finish_fact_verification(checked, result));
                }

                Ok(direct_result)
            }
            ParamType::Set(_) => {
                let fact = self.new_is_set_fact(obj, default_line_file()).into();
                self.verify_atomic_parameter_fact(&fact, verify_state)
            }
            ParamType::NonemptySet(_) => {
                let fact = self
                    .new_is_nonempty_set_fact(obj, default_line_file())
                    .into();
                self.verify_atomic_parameter_fact(&fact, verify_state)
            }
            ParamType::FiniteSet(_) => {
                let fact = self.new_is_finite_set_fact(obj, default_line_file()).into();
                self.verify_atomic_parameter_fact(&fact, verify_state)
            }
        }
    }

    pub fn verify_args_satisfy_param_def_flat_types(
        &mut self,
        param_defs: &TypedParameterList,
        args: &[Obj],
        verify_state: &VerifyState,
        substitution_mode: SubstitutionMode,
    ) -> Result<VerifyArgsSatisfyParamDefResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args, substitution_mode)?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let infer_result = SuccessInferResult::new();
        let mut check_results = Vec::with_capacity(args.len());
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let verify_result =
                self.verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)?;
            if verify_result.is_unknown() {
                return Ok(VerifyArgsSatisfyParamDefResult::unknown(verify_result));
            }
            check_results.push(verify_result);
        }
        Ok(VerifyArgsSatisfyParamDefResult::success(
            check_results,
            infer_result,
        ))
    }
}
