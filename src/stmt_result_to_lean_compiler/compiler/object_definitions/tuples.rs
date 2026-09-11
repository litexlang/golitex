//! Tuple declarations and indexed coordinate facts.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: compile the two retained dimension checks in the ambient
    /// environment, compile the coordinate value under its exact index
    /// binder, pop that child environment, then publish the three ordered
    /// tuple-definition store effects.
    pub(in super::super) fn compile_have_tuple_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveTupleStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let lowered_dimension = LeanTargetObjectRepresentation::lower(&statement.dimension)?;
        let LeanTargetObjectRepresentation::Number {
            normalized_value: normalized_dimension,
        } = &lowered_dimension
        else {
            return Ok(false);
        };
        let dimension = normalized_dimension
            .parse::<usize>()
            .map_err(|_| "indexed tuple dimension is not a machine natural".to_string())?;
        if dimension < 2 {
            return Err("indexed tuple dimension is smaller than two".into());
        }

        let expected_positive_dimension: Fact = self
            .runtime
            .new_in_fact(
                statement.dimension.clone(),
                StandardSet::NPos.into(),
                statement.line_file.clone(),
            )
            .into();
        let expected_at_least_two: Fact = self
            .runtime
            .new_less_equal_fact(
                Number::new("2".to_string()).into(),
                statement.dimension.clone(),
                statement.line_file.clone(),
            )
            .into();
        let positive_dimension = verification
            .dimension
            .positive_check
            .verified()
            .ok_or_else(|| "indexed tuple positive-dimension check is not factual".to_string())?;
        let at_least_two = verification
            .dimension
            .at_least_two_check
            .verified()
            .ok_or_else(|| "indexed tuple at-least-two check is not factual".to_string())?;
        for (check, expected, role) in [
            (
                positive_dimension,
                &expected_positive_dimension,
                "positive-dimension",
            ),
            (at_least_two, &expected_at_least_two, "at-least-two"),
        ] {
            if check.fact().to_string() != expected.to_string() {
                return Err(format!("indexed tuple {role} Result changed its target"));
            }
        }
        let Some(positive_dimension_proof) =
            self.construct_lean_proof_from_direct_fact_result(positive_dimension)?
        else {
            return Ok(false);
        };
        let Some(at_least_two_dimension_proof) =
            self.construct_lean_proof_from_direct_fact_result(at_least_two)?
        else {
            return Ok(false);
        };

        let lowered_value = LeanTargetObjectRepresentation::lower(&statement.value)?;
        if !indexed_tuple_value_is_complex(&lowered_value, statement.index_binding.id()) {
            return Ok(false);
        }
        let mut visited = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.value_well_definedness.as_ref(),
            &statement.value,
            &mut visited,
        )?;

        self.environment_stack.push_inherited_environment();
        let compiled_body = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__index".into());
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "(((__index.val : ℤ) : ℂ))".into(),
            );
            self.environment_stack
                .numeric_integer_values
                .insert(statement.index_binding.id(), "(__index.val : ℤ)".into());
            self.environment_stack
                .numeric_rational_values
                .insert(statement.index_binding.id(), "(__index.val : ℚ)".into());
            let mut installed_well_definedness_nodes = HashSet::new();
            install_object_well_definedness_store_results(
                verification.value_well_definedness.as_ref(),
                &mut self.environment_stack,
                &mut installed_well_definedness_nodes,
            )?;
            let value = render_lean_source_for_numeric_target_object_representation(
                &lowered_value,
                &self.environment_stack,
            )?;
            Ok::<_, String>(CompiledIndexedTupleDefinitionBody {
                dimension,
                value,
                positive_dimension_proof,
                at_least_two_dimension_proof,
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("indexed tuple stores retained unexpected typed infer rules".into());
        }
        let [is_tuple_output, dimension_output, coordinate_output] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("indexed tuple requires exactly three ordered store outputs".into());
        };
        for output in [is_tuple_output, dimension_output, coordinate_output] {
            if output.fact_id.is_none()
                || !output.inferred_facts.is_empty()
                || !output.inferred_fact_ids.is_empty()
            {
                return Err(
                    "indexed tuple store output lost its FactId or gained inferred children".into(),
                );
            }
        }

        let name = lean_identifier(statement.name());
        let positive_dimension_proposition =
            render_fact(&expected_positive_dimension, &self.environment_stack)?;
        let at_least_two_proposition =
            render_fact(&expected_at_least_two, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem __{name}_dimension_check1 : {positive_dimension_proposition} := by\n  exact {}",
            compiled_body.positive_dimension_proof
        ));
        self.declarations.push(format!(
            "theorem __{name}_dimension_check2 : {at_least_two_proposition} := by\n  exact {}",
            compiled_body.at_least_two_dimension_proof
        ));
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.IndexedTuple {} ℂ :=\n  ⟨fun __index => {}⟩",
            compiled_body.dimension, compiled_body.value
        ));
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for indexed tuple `{}`",
                statement.name()
            ));
        }
        self.environment_stack.indexed_tuple_bindings.insert(
            statement.symbol_binding.id(),
            IndexedTupleBinding {
                dimension: compiled_body.dimension,
            },
        );

        let target: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_is_tuple: Fact = self
            .runtime
            .new_is_tuple_fact(target.clone(), statement.line_file.clone())
            .into();
        if is_tuple_output
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_is_tuple.to_string()
        {
            return Err("indexed tuple first store is not its exact IsTuple fact".into());
        }
        let is_tuple_fact_id = is_tuple_output
            .fact_id
            .expect("stored tuple output FactId validated above");
        let is_tuple_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {is_tuple_theorem_name} : {} := by\n  exact ⟨inferInstance⟩",
            render_fact(&expected_is_tuple, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(is_tuple_fact_id, is_tuple_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(is_tuple_fact_id, expected_is_tuple);
        self.next_fact_name_index += 1;

        let expected_dimension: Fact = self
            .runtime
            .new_equal_fact(
                TupleDim::new(target.clone()).into(),
                statement.dimension.clone(),
                statement.line_file.clone(),
            )
            .into();
        if dimension_output
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_dimension.to_string()
        {
            return Err("indexed tuple second store is not its exact dimension fact".into());
        }
        let dimension_fact_id = dimension_output
            .fact_id
            .expect("stored tuple output FactId validated above");
        let dimension_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {dimension_theorem_name} : {} := by\n  exact Litex.Same.ofEq (by rfl)",
            render_fact(&expected_dimension, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(dimension_fact_id, dimension_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(dimension_fact_id, expected_dimension);
        self.next_fact_name_index += 1;

        self.compile_indexed_tuple_coordinate_store_result_to_lean_source(
            statement,
            compiled_body.dimension,
            coordinate_output,
        )?;
        Ok(true)
    }

    pub(in super::super) fn compile_indexed_tuple_coordinate_store_result_to_lean_source(
        &mut self,
        statement: &HaveTupleStmt,
        dimension: usize,
        coordinate_output: &SuccessStoreFactOutput,
    ) -> Result<(), String> {
        let coordinate_fact_id = coordinate_output
            .fact_id
            .ok_or_else(|| "indexed tuple coordinate store has no FactId".to_string())?;
        let Fact::ForallFact(forall) = &coordinate_output.itself_and_why_itself_is_stored.0 else {
            return Err("indexed tuple coordinate store is not a forall fact".into());
        };
        let parameters = forall.typed_parameters.collect_param_bindings_with_types();
        let [(binding, param_type)] = parameters.as_slice() else {
            return Err("indexed tuple coordinate store changed its one-index binder".into());
        };
        if !forall.dom_facts.is_empty() || forall.then_facts.len() != 1 {
            return Err(
                "indexed tuple coordinate store changed its domain or conclusion arity".into(),
            );
        }
        let Obj::ClosedRange(range) = parameter_set(param_type)? else {
            return Err("indexed tuple coordinate binder is not a closed range".into());
        };
        let lowered_start = LeanTargetObjectRepresentation::lower(range.start.as_ref())?;
        let lowered_end = LeanTargetObjectRepresentation::lower(range.end.as_ref())?;
        if lowered_start
            != (LeanTargetObjectRepresentation::Number {
                normalized_value: "1".into(),
            })
            || lowered_end != LeanTargetObjectRepresentation::lower(&statement.dimension)?
        {
            return Err("indexed tuple coordinate range changed its one-based dimension".into());
        }
        let conclusion = forall.then_facts[0].clone().to_fact();
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &conclusion else {
            return Err("indexed tuple coordinate conclusion is not an equality".into());
        };
        let Obj::ObjAtIndex(access) = &equality.left else {
            return Err("indexed tuple coordinate conclusion lost indexed access".into());
        };
        if !object_is_symbol(&access.obj, statement.symbol_binding.id())
            || !object_is_symbol(&access.index, binding.id())
        {
            return Err("indexed tuple coordinate conclusion changed its tuple or index".into());
        }

        let index = "__tuple_index";
        let membership = "__tuple_index_in";
        let exact_index = format!("(Litex.In.rep {index} {membership})");
        let numeric_index = format!("((({exact_index}).val : ℤ) : ℂ)");
        let mut nested = self.environment_stack.clone();
        nested.symbol_names.insert(binding.id(), index.into());
        nested
            .exact_tuple_indices
            .insert(binding.id(), exact_index.clone());
        nested
            .numeric_representations
            .insert(binding.id(), numeric_index.clone());

        let mut source_value_context = self.environment_stack.clone();
        source_value_context
            .symbol_names
            .insert(statement.index_binding.id(), index.into());
        source_value_context
            .numeric_representations
            .insert(statement.index_binding.id(), numeric_index);
        let expected_value = render_lean_source_for_numeric_target_object_representation(
            &LeanTargetObjectRepresentation::lower(&statement.value)?,
            &source_value_context,
        )?;
        let retained_value = render_lean_source_for_numeric_target_object_representation(
            &LeanTargetObjectRepresentation::lower(&equality.right)?,
            &nested,
        )?;
        if retained_value != expected_value {
            return Err("indexed tuple coordinate store changed its value expression".into());
        }

        let rendered_conclusion = render_fact(&conclusion, &nested)?;
        let range = format!("(Litex.closedRange (1 : ℤ) ({dimension} : ℤ))");
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    ∀ {{__tuple_index_carrier : Type}} ({index} : __tuple_index_carrier) ({membership} : Litex.In {index} {range}),\n      {rendered_conclusion} := by\n  intro __tuple_index_carrier {index} {membership}\n  exact Litex.Same.ofEq (by rfl)"
        ));
        self.environment_stack
            .fact_names
            .insert(coordinate_fact_id, theorem_name);
        self.environment_stack.fact_propositions.insert(
            coordinate_fact_id,
            coordinate_output.itself_and_why_itself_is_stored.0.clone(),
        );
        self.next_fact_name_index += 1;
        Ok(())
    }
}
