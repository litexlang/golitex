use crate::prelude::*;

impl Runtime {
    // Injectivity means equal outputs force equal inputs.
    // Example: `$injective(A, B, f)` unfolds to
    // `forall x1, x2 A: f(x1) = f(x2) => x1 = x2`.
    pub(crate) fn verify_builtin_function_property_by_definition(
        &mut self,
        fact: &NormalAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(definition_facts) = self.builtin_function_property_definition_facts(fact)? else {
            return Ok(None);
        };

        let mut inside_results = Vec::with_capacity(definition_facts.len());
        for definition_fact in definition_facts {
            let result = self.verify_fact_full(&definition_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(Some(result));
            }
            inside_results.push(result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                fact.clone().into(),
                format!(
                    "{} by its builtin function-property definition",
                    fact.predicate
                ),
                inside_results,
            )
            .into(),
        ))
    }

    // Positive function-property facts expose their mathematical definitions to inference.
    // Example: `$bijective(A, B, f)` adds both `$injective(A, B, f)` and
    // `$surjective(A, B, f)`; those facts then add their forall/exist bodies.
    pub(crate) fn builtin_function_property_definition_facts(
        &mut self,
        fact: &NormalAtomicFact,
    ) -> Result<Option<Vec<Fact>>, RuntimeError> {
        if fact.body.len() != 3 {
            return Ok(None);
        }
        let predicate = fact.predicate.to_string();
        let domain = fact.body[0].clone();
        let codomain = fact.body[1].clone();
        let function = fact.body[2].clone();

        match predicate.as_str() {
            INJECTIVE => Ok(Some(vec![self.injective_definition_fact(
                domain,
                function,
                fact.line_file.clone(),
            )?])),
            SURJECTIVE => Ok(Some(vec![self.surjective_definition_fact(
                domain,
                codomain,
                function,
                fact.line_file.clone(),
            )?])),
            BIJECTIVE => Ok(Some(vec![
                NormalAtomicFact::new(
                    AtomicName::WithoutMod(INJECTIVE.to_string()),
                    fact.body.clone(),
                    fact.line_file.clone(),
                )
                .into(),
                NormalAtomicFact::new(
                    AtomicName::WithoutMod(SURJECTIVE.to_string()),
                    fact.body.clone(),
                    fact.line_file.clone(),
                )
                .into(),
            ])),
            _ => Ok(None),
        }
    }

    pub(crate) fn verify_builtin_function_property_arg_types(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((predicate, args)) = builtin_function_property_name_and_args(fact) else {
            return Ok(None);
        };
        if !matches!(predicate, INJECTIVE | SURJECTIVE | BIJECTIVE) || args.len() != 3 {
            return Ok(None);
        }

        let domain = args[0].clone();
        let codomain = args[1].clone();
        let function = args[2].clone();
        let mut infer_result = InferResult::new();
        for obj in [domain.clone(), codomain.clone()] {
            let param_type = ParamType::Set(Set::new());
            let result = self.verify_obj_satisfies_param_type(obj, &param_type, verify_state)?;
            if result.is_unknown() {
                return Ok(Some(result));
            }
            infer_result.new_infer_result_inside(result.infer_result());
        }

        let Some(function_body) = self.get_fn_range_function_body(&function) else {
            return Ok(Some(StmtResult::Unknown(StmtUnknown::new())));
        };
        if ParamGroupWithSet::number_of_params(&function_body.params_def_with_set) != 1
            || !function_body.dom_facts.is_empty()
        {
            return Ok(Some(StmtResult::Unknown(StmtUnknown::new())));
        }
        let Some(param_group) = function_body.params_def_with_set.first() else {
            return Ok(Some(StmtResult::Unknown(StmtUnknown::new())));
        };
        let domain_result =
            self.verify_objs_are_equal_known_only(param_group.set_obj(), &domain, fact.line_file());
        if domain_result.is_unknown() {
            return Ok(Some(domain_result));
        }
        infer_result.new_infer_result_inside(domain_result.infer_result());

        let codomain_result = self.verify_objs_are_equal_known_only(
            function_body.ret_set.as_ref(),
            &codomain,
            fact.line_file(),
        );
        if codomain_result.is_unknown() {
            return Ok(Some(codomain_result));
        }
        infer_result.new_infer_result_inside(codomain_result.infer_result());

        Ok(Some(
            NonFactualStmtSuccess::new(
                DoNothingStmt::new(fact.line_file()).into(),
                infer_result,
                Vec::new(),
            )
            .into(),
        ))
    }

    fn injective_definition_fact(
        &mut self,
        domain: Obj,
        function: Obj,
        line_file: LineFile,
    ) -> Result<Fact, RuntimeError> {
        let names = self.generate_random_unused_names(2);
        let x1 = obj_for_bound_param_in_scope(names[0].clone(), ParamObjType::Forall);
        let x2 = obj_for_bound_param_in_scope(names[1].clone(), ParamObjType::Forall);
        let Some(fx1) = function_applied_to_one_arg(&function, x1.clone()) else {
            return Err(function_property_application_error(&function, line_file));
        };
        let Some(fx2) = function_applied_to_one_arg(&function, x2.clone()) else {
            return Err(function_property_application_error(&function, line_file));
        };
        Ok(ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                names,
                ParamType::Obj(domain),
            )]),
            vec![EqualFact::new(fx1, fx2, line_file.clone()).into()],
            vec![EqualFact::new(x1, x2, line_file.clone()).into()],
            line_file,
        )?
        .into())
    }

    fn surjective_definition_fact(
        &mut self,
        domain: Obj,
        codomain: Obj,
        function: Obj,
        line_file: LineFile,
    ) -> Result<Fact, RuntimeError> {
        let names = self.generate_random_unused_names(2);
        let y_name = names[0].clone();
        let x_name = names[1].clone();
        let y = obj_for_bound_param_in_scope(y_name.clone(), ParamObjType::Forall);
        let x = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Exist);
        let Some(fx) = function_applied_to_one_arg(&function, x) else {
            return Err(function_property_application_error(&function, line_file));
        };
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_name],
                ParamType::Obj(domain),
            )]),
            vec![EqualFact::new(y, fx, line_file.clone()).into()],
            line_file.clone(),
        )?;
        Ok(ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![y_name],
                ParamType::Obj(codomain),
            )]),
            vec![],
            vec![ExistFactEnum::ExistFact(exist_body).into()],
            line_file,
        )?
        .into())
    }
}

fn builtin_function_property_name_and_args(fact: &AtomicFact) -> Option<(&str, Vec<Obj>)> {
    match fact {
        AtomicFact::NormalAtomicFact(f) => {
            let name = match &f.predicate {
                AtomicName::WithoutMod(name) => name.as_str(),
                AtomicName::WithMod(_, _) => return None,
            };
            Some((name, f.body.clone()))
        }
        AtomicFact::NotNormalAtomicFact(f) => {
            let name = match &f.predicate {
                AtomicName::WithoutMod(name) => name.as_str(),
                AtomicName::WithMod(_, _) => return None,
            };
            Some((name, f.body.clone()))
        }
        _ => None,
    }
}

fn function_applied_to_one_arg(function: &Obj, arg: Obj) -> Option<Obj> {
    let head = FnObjHead::from_callable_obj(function.clone())?;
    Some(FnObj::new(head, vec![vec![Box::new(arg)]]).into())
}

fn function_property_application_error(function: &Obj, line_file: LineFile) -> RuntimeError {
    WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        format!("{} is not a callable unary function", function),
        line_file,
    ))
    .into()
}
