//! Local inference proof naming and retention.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Render an inferred fact as a local `have`.  A forall conclusion is
    /// eta-expanded at this boundary instead of being assigned with a bare
    /// `exact`: heterogeneous Litex objects leave the carrier implicit, and
    /// Lean cannot always infer that carrier while unifying two alpha-
    /// equivalent dependent forall types.  Introducing the complete
    /// telescope and applying the retained proof fixes only that elaboration
    /// issue; it does not change the verified proposition or its FactId.
    pub(in super::super) fn render_compiled_inference_fact_proof_step_as_local_have_statement(
        &self,
        step: &CompiledInferenceFactProofStep,
    ) -> String {
        let Fact::ForallFact(forall) = &step.fact else {
            return step.render_as_local_have_statement();
        };

        let mut intro_names = Vec::new();
        let mut arguments = Vec::new();
        for (index, (_, parameter_type)) in forall
            .typed_parameters
            .collect_param_bindings_with_types()
            .iter()
            .enumerate()
        {
            let suffix = index + 1;
            let parameter = format!("__adapter_parameter{suffix}");
            match parameter_type {
                ParamType::Set(_) => {
                    intro_names.push(parameter.clone());
                    arguments.push(parameter);
                }
                ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    let requirement = format!("__adapter_type{suffix}");
                    intro_names.extend([parameter.clone(), requirement.clone()]);
                    arguments.extend([parameter, requirement]);
                }
                ParamType::Obj(set) if matches!(set, Obj::StandardSet(StandardSet::Z)) => {
                    intro_names.push(parameter.clone());
                    arguments.push(parameter);
                }
                ParamType::Obj(_) => {
                    if forall_parameter_uses_implicit_host_carrier(parameter_type) {
                        intro_names.push(format!("__adapter_carrier{suffix}"));
                    }
                    let requirement = format!("__adapter_type{suffix}");
                    intro_names.extend([parameter.clone(), requirement.clone()]);
                    arguments.extend([parameter, requirement]);
                }
            }
        }
        for index in 0..forall.dom_facts.len() {
            let domain = format!("__adapter_domain{}", index + 1);
            intro_names.push(domain.clone());
            arguments.push(domain);
        }
        if intro_names.is_empty() {
            return step.render_as_local_have_statement();
        }
        format!(
            "have {} : {} := by\n  intro {}\n  exact ({}) {}",
            step.local_lean_name,
            step.proposition,
            intro_names.join(" "),
            step.proof_expression,
            arguments.join(" ")
        )
    }

    /// Allocate one proof-local base name from the compiler-wide local-name
    /// counter. Source proof-step indices restart inside nested claims and
    /// forall bodies, so they are not valid Lean identifiers on their own:
    /// all emitted `have` declarations share one surrounding tactic scope.
    pub(in super::super) fn next_local_proof_step_base_name(&mut self) -> String {
        let name = format!(
            "__step{}_{}",
            self.next_fact_name_index, self.next_local_inference_name_index
        );
        self.next_local_inference_name_index += 1;
        name
    }

    pub(in super::super) fn next_local_inference_fact_proof_name(&mut self) -> String {
        let name = format!(
            "__infer{}_{}",
            self.next_fact_name_index, self.next_local_inference_name_index
        );
        self.next_local_inference_name_index += 1;
        name
    }

    pub(in super::super) fn retain_compiled_inference_fact_proof_step_in_current_environment(
        &mut self,
        compiled_steps: &mut Vec<CompiledInferenceFactProofStep>,
        step: CompiledInferenceFactProofStep,
        availability: CompiledInferenceFactAvailabilityInLeanEnvironment,
    ) {
        let lean_reference = match availability {
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName => {
                step.local_lean_name.clone()
            }
            CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression => {
                format!("({})", step.proof_expression)
            }
        };
        self.environment_stack
            .fact_names
            .insert(step.fact_id, lean_reference.clone());
        self.environment_stack
            .fact_propositions
            .insert(step.fact_id, step.fact.clone());
        self.environment_stack
            .fact_lean_propositions
            .insert(step.fact_id, step.proposition.clone());
        if let Ok((source_set, target_set)) = subset_parts(&step.fact) {
            self.environment_stack.subset_membership_transports.push(
                SubsetMembershipTransportBinding::new(
                    source_set.clone(),
                    target_set.clone(),
                    lean_reference.clone(),
                ),
            );
        }
        compiled_steps.push(step);
    }
}
