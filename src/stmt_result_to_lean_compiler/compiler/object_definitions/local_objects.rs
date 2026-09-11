//! Local object bindings.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_let_obj_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessLetObjStmtResult,
    ) -> Result<(), String> {
        let statement = &result.statement;
        let source_name = statement.symbol_binding.name();
        let lean_name = lean_identifier(source_name);
        let rendered_value = render_obj(&statement.value, &self.environment_stack)?;
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), lean_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{source_name}`"
            ));
        }
        self.declarations
            .push(format!("noncomputable def {lean_name} := {rendered_value}"));

        if !result.common.infers.rule_applications.is_empty() {
            return Err("let-object definition retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("let-object definition must retain exactly one defining store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("let-object defining store retained unexpected inferred facts".into());
        }
        let defined_object: Obj =
            Identifier::new_bound(source_name.to_string(), statement.symbol_binding.as_ref())
                .into();
        let defining_equality: Fact = self
            .runtime
            .new_equal_fact(
                defined_object,
                statement.value.clone(),
                statement.line_file.clone(),
            )
            .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != defining_equality.to_string() {
            return Err("let-object result changed its defining equality".into());
        }
        let defining_equality_fact_id = store
            .fact_id
            .ok_or_else(|| "let-object defining equality has no FactId".to_string())?;
        let rendered_equality = render_fact(&defining_equality, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, defining_equality.clone());
        self.environment_stack
            .transparent_object_definitions
            .insert(
                statement.symbol_binding.id(),
                CompilerTransparentObjectDefinition {
                    value: statement.value.clone(),
                    defining_equality,
                    defining_equality_fact_id,
                },
            );
        self.environment_stack
            .runtime_resolved_numeric_substitutions
            .insert(
                statement.symbol_binding.substitution_key(),
                statement.value.clone(),
            );
        self.environment_stack
            .runtime_resolved_numeric_definition_names
            .push(lean_name);
        self.next_fact_name_index += 1;
        Ok(())
    }
}
