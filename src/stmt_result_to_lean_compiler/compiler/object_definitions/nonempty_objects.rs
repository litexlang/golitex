//! Object construction from nonempty sets.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_have_obj_in_nonempty_set_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjInNonemptySetStmtResult,
    ) -> Result<(), String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "object choice has no structured nonemptiness-to-membership result".to_string()
        })?;
        let parameter_groups = &result.statement.param_def.groups;
        if parameter_groups.len() != verification.groups.len() {
            return Err("object choice changed its parameter-group mapping".into());
        }
        let expected_choice_count = parameter_groups
            .iter()
            .map(|group| group.params.len())
            .sum::<usize>();
        if result.common.infers.store_fact_outputs.len() != expected_choice_count {
            return Err("object choice store count does not match its selected objects".into());
        }

        for (parameter_group, verified_group) in
            parameter_groups.iter().zip(verification.groups.iter())
        {
            let carrier = parameter_set(&parameter_group.param_type)?;
            if parameter_group.params.len() != verified_group.selected_type_facts.len() {
                return Err("object choice changed its binding-to-membership mapping".into());
            }
            let nonempty_check = verified_group.nonempty_check.as_deref().ok_or_else(|| {
                "object-carrier choice retained no nonemptiness proof".to_string()
            })?;
            let nonempty_proof = compile_standard_set_nonempty_fact_proof_from_result(
                nonempty_check,
                carrier,
                &self.environment_stack,
            )?;
            let rendered_carrier = render_obj(carrier, &self.environment_stack)?;

            for (binding, selected_type_fact) in parameter_group
                .params
                .iter()
                .zip(verified_group.selected_type_facts.iter())
            {
                let source_name = binding.name();
                let lean_name = lean_identifier(source_name);
                let defined_object: Obj =
                    Identifier::new_bound(source_name.to_string(), binding.as_ref()).into();
                let expected_membership: Fact = InFact::new(
                    defined_object,
                    carrier.clone(),
                    result.statement.line_file.clone(),
                )
                .into();
                if selected_type_fact.to_string() != expected_membership.to_string() {
                    return Err(format!(
                        "object choice changed selected membership `{selected_type_fact}`"
                    ));
                }
                let matching_stores = result
                    .common
                    .infers
                    .store_fact_outputs
                    .iter()
                    .filter(|store| {
                        store.itself_and_why_itself_is_stored.0.to_string()
                            == selected_type_fact.to_string()
                    })
                    .collect::<Vec<_>>();
                let [store] = matching_stores.as_slice() else {
                    return Err(
                        "object choice membership does not have exactly one store effect".into(),
                    );
                };
                let fact_id = store
                    .fact_id
                    .ok_or_else(|| "object choice membership has no FactId".to_string())?;
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), lean_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "duplicate compiler symbol identity for `{source_name}`"
                    ));
                }
                self.declarations.push(format!(
                    "noncomputable def {lean_name} : {rendered_carrier}.Carrier :=\n  Classical.choice ({nonempty_proof})"
                ));

                let proposition = render_fact(selected_type_fact, &self.environment_stack)?;
                let theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {theorem_name} : {proposition} := by\n  exact Litex.In.own {rendered_carrier} {lean_name}"
                ));
                self.environment_stack
                    .fact_names
                    .insert(fact_id, theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, selected_type_fact.clone());
                self.next_fact_name_index += 1;

                if matches!(carrier, Obj::StandardSet(StandardSet::N)) {
                    self.compile_natural_membership_infer_result(
                        selected_type_fact,
                        fact_id,
                        &result.common.infers,
                    )?;
                } else if store.inferred_facts.is_empty() && store.inferred_fact_ids.is_empty() {
                    // No child inference layer is expected for the other
                    // currently supported object carriers.
                } else {
                    return Err(format!(
                        "object choice for `{carrier}` retained unsupported inferred consequences"
                    ));
                }
            }
        }
        Ok(())
    }
}
