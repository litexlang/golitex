//! Concrete and abstract proposition definitions.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_def_prop_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefPropStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("concrete predicate definition unexpectedly retained fact effects".into());
        }
        let definition = &result.statement;
        if definition.iff_facts.is_empty() {
            return Err("compiler rejects a bodyless concrete `prop`".into());
        }
        if self
            .environment_stack
            .predicate_bindings
            .contains_key(&definition.name)
        {
            return Err(format!(
                "duplicate compiler predicate definition `{}`",
                definition.name
            ));
        }
        let local = result.run_in_local_env.as_ref().ok_or_else(|| {
            "compiler rejects a concrete `prop` Result without verified local evidence".to_string()
        })?;
        if local.body.len() != definition.iff_facts.len()
            || local.binder.parameter_groups.len() != definition.typed_parameters.groups.len()
        {
            return Err("concrete predicate Result changed its binder or body arity".into());
        }
        for (retained, source) in local.body.iter().zip(definition.iff_facts.iter()) {
            if retained.proposition.to_string() != source.to_string()
                || retained.store.fact.to_string() != source.to_string()
                || retained.store.fact_id.is_none()
            {
                return Err(
                    "concrete predicate Result changed a verified body clause or its local FactId"
                        .into(),
                );
            }
        }
        let mut definition_environment = self.environment_stack.clone();
        definition_environment.push_inherited_environment();
        definition_environment.well_definedness =
            Some(self.construct_def_prop_well_definedness_to_lean_compilation_context(local)?);
        let mut binders = Vec::new();
        let mut requirements = Vec::new();
        let mut exact_parameters = Vec::new();
        let mut parameter_count = 0;
        // Primitive numeric sets and function sets have stable exact target
        // carriers. Proper numeric subtypes such as R+ remain heterogeneous:
        // their source value is what surrounding Litex inequalities mention,
        // while the membership proof is retained as dependent evidence.
        let parameter_is_exact = |set: &Obj| {
            matches!(
                set,
                Obj::FnSet(_)
                    | Obj::FiniteSeqSet(_)
                    | Obj::SeqSet(_)
                    | Obj::StandardSet(
                        StandardSet::N
                            | StandardSet::Z
                            | StandardSet::Q
                            | StandardSet::R
                            | StandardSet::C
                    )
            )
        };
        let dependent_parameter_evidence = definition.typed_parameters.groups.iter().any(
            |group| matches!(&group.param_type, ParamType::Obj(set) if !parameter_is_exact(set)),
        );
        for (group, retained_group) in definition
            .typed_parameters
            .groups
            .iter()
            .zip(local.binder.parameter_groups.iter())
        {
            if group.param_type.to_string() != retained_group.parameter_type.to_string()
                || group.params.len() != retained_group.parameters.len()
            {
                return Err("concrete predicate Result changed a typed parameter group".into());
            }
            for (binding, retained_parameter) in
                group.params.iter().zip(retained_group.parameters.iter())
            {
                parameter_count += 1;
                let parameter_name = lean_identifier(binding.name());
                match &group.param_type {
                    ParamType::Set(_) => {
                        exact_parameters.push(false);
                        binders.push(format!("({parameter_name} : Litex.Set)"));
                        definition_environment
                            .symbol_names
                            .insert(binding.id(), parameter_name);
                        // The source Result still owns and validates
                        // `$is_set(parameter)`. In Lean this obligation is
                        // already discharged by the binder's `Litex.Set`
                        // type, so its proposition/proof bridge is `True`.
                        requirements.push("True".to_string());
                    }
                    ParamType::Obj(set) => {
                        let rendered_set = render_obj(set, &definition_environment)?;
                        let exact_parameter = parameter_is_exact(set);
                        exact_parameters.push(exact_parameter);
                        if exact_parameter {
                            binders.push(format!("({parameter_name} : ({rendered_set}).Carrier)"));
                        } else if matches!(set, Obj::StandardSet(_)) {
                            // Litex arithmetic observes proper numeric
                            // subsets (R+, Q-, Z*, ...) through the source
                            // complex carrier. Their membership proof remains
                            // explicit, but the value itself must be usable by
                            // `Litex.Lt`/`Litex.Le` without an unsound cast
                            // from an arbitrary host type.
                            binders.push(format!("({parameter_name} : ℂ)"));
                        } else {
                            let carrier_name = format!("__carrier{parameter_count}");
                            binders.push(format!("{{{carrier_name} : Type}}"));
                            binders.push(format!("({parameter_name} : {carrier_name})"));
                        }
                        definition_environment
                            .symbol_names
                            .insert(binding.id(), parameter_name.clone());
                        let requirement = format!("Litex.In {parameter_name} {rendered_set}");
                        requirements.push(requirement);
                        let primary_fact_id =
                            fact_id_for_well_definedness_binder_premise(retained_parameter)?;
                        let proof_name = if dependent_parameter_evidence {
                            format!("__arg_type{parameter_count}")
                        } else {
                            format!("(Litex.In.own {rendered_set} {parameter_name})")
                        };
                        install_parameter_fact_aliases(
                            binding.id(),
                            primary_fact_id,
                            &retained_parameter.proposition,
                            &proof_name,
                            set,
                            &mut definition_environment,
                        )?;
                        let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                        if exact_parameter {
                            definition_environment
                                .exact_carrier_values
                                .insert(binding.id(), parameter_name.clone());
                            if let Some(real) = exact_set_real_value(&lowered_set, &parameter_name)
                            {
                                definition_environment
                                    .numeric_real_values
                                    .insert(binding.id(), real);
                            }
                            if let Some(integer) =
                                exact_set_integer_value(&lowered_set, &parameter_name)
                            {
                                definition_environment
                                    .numeric_integer_values
                                    .insert(binding.id(), integer);
                            }
                            if let Some(rational) =
                                exact_set_rational_value(&lowered_set, &parameter_name)
                            {
                                definition_environment
                                    .numeric_rational_values
                                    .insert(binding.id(), rational);
                            }
                            if let Some(numeric) =
                                exact_set_numeric_value(&lowered_set, &parameter_name)
                            {
                                definition_environment
                                    .numeric_representations
                                    .insert(binding.id(), numeric);
                            }
                        } else {
                            definition_environment
                                .exact_carrier_values
                                .remove(&binding.id());
                            definition_environment
                                .numeric_real_values
                                .remove(&binding.id());
                            definition_environment
                                .numeric_integer_values
                                .remove(&binding.id());
                            definition_environment
                                .numeric_rational_values
                                .remove(&binding.id());
                            definition_environment
                                .numeric_representations
                                .remove(&binding.id());
                            definition_environment
                                .numeric_representation_equalities
                                .remove(&binding.id());
                            definition_environment
                                .numeric_representation_memberships
                                .remove(&binding.id());
                        }
                        if exact_parameter
                            && matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_))
                        {
                            let mut found = false;
                            for function_binding in
                                definition_environment.function_bindings.values_mut()
                            {
                                if function_binding.symbol_id == binding.id() {
                                    function_binding.direct = true;
                                    function_binding.membership_proof_name = proof_name.clone();
                                    found = true;
                                }
                            }
                            if !found {
                                return Err(
                                    "exact predicate function parameter lost its checked function binding"
                                        .to_string(),
                                );
                            }
                        }
                    }
                    unsupported => {
                        return Err(format!(
                            "concrete predicate compiler does not support parameter type `{unsupported}`"
                        ));
                    }
                }
            }
        }
        let clauses = definition
            .iff_facts
            .iter()
            .map(|fact| render_fact(fact, &definition_environment))
            .collect::<Result<Vec<_>, _>>()?;
        let body = if dependent_parameter_evidence {
            let evidence_binders = requirements
                .iter()
                .enumerate()
                .map(|(index, requirement)| format!("(__arg_type{} : {requirement})", index + 1))
                .collect::<Vec<_>>()
                .join(" ");
            format!("\u{2203} {evidence_binders}, {}", conjunction(&clauses))
        } else {
            let mut components = requirements;
            components.extend(clauses);
            conjunction(&components)
        };
        let lean_name = lean_identifier(&definition.name);
        self.declarations.push(format!(
            "def {lean_name} {} : Prop :=\n  {}",
            binders.join(" "),
            body
        ));
        self.environment_stack.predicate_bindings.insert(
            definition.name.clone(),
            PredicateBinding {
                lean_name,
                same_congruence_name: None,
                parameter_count,
                exact_parameters,
                requirement_count: parameter_count,
                clause_count: definition.iff_facts.len(),
                dependent_parameter_evidence,
                definition: Some(definition.clone()),
                definition_well_definedness: definition_environment.well_definedness.clone(),
            },
        );
        Ok(())
    }

    pub(in super::super) fn compile_def_abstract_prop_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefAbstractPropStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("abstract predicate definition unexpectedly retained fact effects".into());
        }
        construct_lean_source_parts_for_abstract_predicate_definition(
            &result.statement.name,
            &result.statement.params,
            &mut self.declarations,
            &mut self.environment_stack,
        )
    }
}
