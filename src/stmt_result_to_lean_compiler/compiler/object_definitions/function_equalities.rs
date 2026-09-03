//! Function equality declarations.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: a named function Result first enters the anonymous
    /// function's binder environment, installs the exact temporary FactIds
    /// retained by `assumption_infers`, consumes the recursive return-check
    /// Result there, and only then returns to the parent environment to
    /// publish the membership/equality FactIds.
    ///
    /// Native-real codomains render their body directly. Every other codomain
    /// uses the recursive return-check proof to select the exact carrier
    /// representative with `Litex.In.rep`; both routes are driven by the same
    /// child compiler environment.
    pub(in super::super) fn compile_have_fn_equal_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveFnEqualStmtResult,
    ) -> Result<bool, String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "named function has no structured body-to-environment verification Result".to_string()
        })?;
        let statement = &result.statement;
        let function_set = FnSet::from_body(statement.equal_to_anonymous_fn.body.clone())
            .map_err(|error| error.to_string())?;
        let function = LeanTargetFunctionTypeRepresentation::lower(&function_set)?;
        let source_body = statement.equal_to_anonymous_fn.equal_to.as_ref().clone();
        let lowered_body = LeanTargetObjectRepresentation::lower(&source_body)?;
        let source_return_set = statement
            .equal_to_anonymous_fn
            .body
            .ret_set
            .as_ref()
            .clone();
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            source_return_set,
            statement.line_file.clone(),
        )
        .into();

        let mut expected_parameter_facts = Vec::new();
        for group in statement
            .equal_to_anonymous_fn
            .body
            .set_bound_parameters
            .iter()
        {
            expected_parameter_facts.extend(group.facts());
        }
        let expected_domain_facts = statement
            .equal_to_anonymous_fn
            .body
            .dom_facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if expected_parameter_facts.len() != function.parameters.len()
            || expected_domain_facts.len() != function.domain_facts.len()
        {
            return Err("named real function changed its parameter/domain Result mapping".into());
        }
        if !verification.assumption_infers.rule_applications.is_empty()
            || verification
                .assumption_infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let mut expected_assumptions = expected_parameter_facts.clone();
        expected_assumptions.extend(expected_domain_facts.iter().cloned());
        let assumption_fact_ids = exact_ordered_fact_ids_from_store_results(
            &verification.assumption_infers,
            &expected_assumptions,
            "named real function local assumptions",
        )?;
        let (parameter_fact_ids, domain_fact_ids) =
            assumption_fact_ids.split_at(expected_parameter_facts.len());

        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_membership: Fact = InFact::new(
            function_object.clone(),
            function_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object,
            statement.equal_to_anonymous_fn.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if verification.function_membership.to_string() != expected_membership.to_string()
            || verification.defining_equality.to_string() != expected_defining_equality.to_string()
        {
            return Err(
                "named real function verification changed its outer membership/equality".into(),
            );
        }
        if !result.common.infers.rule_applications.is_empty()
            || result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &[
                expected_membership.clone(),
                expected_defining_equality.clone(),
            ],
            "named real function outer effects",
        )?;

        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<Option<CompiledNamedFunctionDefinitionBody>, String> = (|| {
            let mut parameter_premises = Vec::with_capacity(function.parameters.len());
            for (parameter_index, ((parameter, fact), fact_id)) in function
                .parameters
                .iter()
                .zip(expected_parameter_facts.iter())
                .zip(parameter_fact_ids.iter())
                .enumerate()
            {
                let suffix = if function_uses_telescope(&function) {
                    (parameter_index + 1).to_string()
                } else {
                    String::new()
                };
                let argument_name = format!("__arg{suffix}");
                let membership_name = format!("__arg{suffix}_in");
                if self
                    .environment_stack
                    .symbol_names
                    .insert(parameter.symbol_id, argument_name.clone())
                    .is_some()
                {
                    return Err("named real function reused one parameter SymbolId".into());
                }
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, membership_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, fact.clone());
                if let Some(real) =
                    membership_real_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_real_values
                        .insert(parameter.symbol_id, real);
                }
                if let Some(integer) =
                    membership_integer_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_integer_values
                        .insert(parameter.symbol_id, integer);
                }
                if let Some(rational) =
                    membership_rational_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_rational_values
                        .insert(parameter.symbol_id, rational);
                }
                if let Some(representation) =
                    membership_numeric_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_representations
                        .insert(parameter.symbol_id, representation);
                }
                if let Some(proof) =
                    membership_numeric_proof(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_representation_memberships
                        .insert(parameter.symbol_id, proof);
                }
                parameter_premises.push(LeanLocalFactPremise::new(*fact_id, fact.clone()));
            }

            let mut domain_premises = Vec::with_capacity(expected_domain_facts.len());
            for (domain_index, (fact, fact_id)) in expected_domain_facts
                .iter()
                .zip(domain_fact_ids.iter())
                .enumerate()
            {
                let selector = conjunction_selector(domain_index, expected_domain_facts.len())?;
                let proof_name = if expected_domain_facts.len() == 1 {
                    "__arg_domain".to_string()
                } else {
                    format!("__arg_domain{selector}")
                };
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, proof_name);
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, fact.clone());
                domain_premises.push(LeanLocalFactPremise::new(*fact_id, fact.clone()));
            }

            let return_check = verification
                .return_check
                .verified()
                .ok_or_else(|| "named real function return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string() {
                return Err("named real function changed its local return check".into());
            }
            let return_proof = self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .ok_or_else(|| {
                    "named function return check has no direct recursive Result proof adapter"
                        .to_string()
                })?;
            let (value, native_body_carrier) = render_named_function_value_from_result(
                &function,
                &lowered_body,
                &source_body,
                &return_proof,
                &self.environment_stack,
            )?;
            Ok(Some(CompiledNamedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value,
                native_body_carrier,
                parameter_premises,
                domain_premises,
            }))
        })(
        );
        self.environment_stack.pop_local_environment();
        let Some(compiled_body) = compiled_body? else {
            return Ok(false);
        };

        let name = lean_identifier(statement.name());
        let function_value_name = if function_uses_telescope(&compiled_body.function) {
            format!("(@{name})")
        } else {
            name.clone()
        };
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let function_set = render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let membership_name = format!("__fact{}", self.next_fact_name_index);
        let membership_proposition = render_fact(&expected_membership, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem {membership_name} : {membership_proposition} := by\n  exact Litex.In.own {function_set} {function_value_name}"
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[0], membership_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[0], expected_membership);
        self.environment_stack.function_bindings.insert(
            stored_fact_ids[0],
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: membership_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_name = format!("__fact{}", self.next_fact_name_index);
        let equality_proposition = format!(
            "Litex.Same {function_value_name} ({} : {function_type})",
            compiled_body.value
        );
        self.declarations.push(format!(
            "theorem {equality_name} : {equality_proposition} := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[1], equality_name);
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[1], expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            stored_fact_ids[1],
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                native_body_carrier: compiled_body.native_body_carrier,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                well_definedness: StmtResultWellDefinednessToLeanCompilationContext::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }
}
