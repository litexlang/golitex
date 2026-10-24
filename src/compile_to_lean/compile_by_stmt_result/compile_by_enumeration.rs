use super::compile_enumeration_product::{enumeration_case_name, enumeration_parameters};
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{EnumerateAssignmentOutcome, EnumerateAssignmentSuccess};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_enumeration(
        &self,
        wd: &VerifyFactWellDefinedResult,
        assignments: &[EnumerateAssignmentSuccess],
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let goal = self.resolve_fact(
            store.primary_fact_id(),
            &SourcePosition {
                before: 2,
                ..*position
            },
        )?;
        let (
            Fact::ForallFact(fact),
            VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)),
        ) = (&goal, wd)
        else {
            return Err(LeanCompileError::unsupported("Enumeration/GoalWD"));
        };
        let parameters = enumeration_parameters(fact)?;
        if fact.then_facts.is_empty() || wd.then.len() != fact.then_facts.len() {
            return Err(LeanCompileError::unsupported("Enumeration/Coverage"));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::ForallWD(fact, wd), 0);
        let (binders, introductions, definitions) =
            self.compile_forall_head(fact, &wd.introduced_params, &wd.assumed_dom_facts, &scope)?;
        let head = parameters.len() + fact.dom_facts.len();
        let prior = SourcePosition {
            before: head,
            ..scope
        };
        let mut goals = Vec::new();
        for (source, formation) in fact.then_facts.iter().zip(&wd.then) {
            let source = Fact::from(source.clone());
            self.compile_fact_wd(formation, &source, &prior)?;
            let formed =
                SourcePosition::new(Some(&prior), SourceOwner::FactWD(formation), usize::MAX);
            goals.push(self.fact_proposition(&source, &formed)?);
        }
        let mut proposition = format!(
            "∀ {}, {}",
            binders.join(" "),
            self.scope_proposition(enumeration_conjunction(goals)?, &definitions)
        );
        let raw: HashMap<_, _> = parameters
            .iter()
            .map(|(p, _)| (p.id, format!("(Litex.denote _value_i{})", p.id.value())))
            .collect();
        let raw_goals = enumeration_conjunction(
            fact.then_facts
                .iter()
                .map(|f| self.compile_function_raw_predicate(&f.clone().into(), &prior, &raw))
                .collect::<Result<_, _>>()?,
        )?;
        let mut lines = if local {
            let mut domains = Vec::new();
            let mut names = Vec::new();
            let mut objects = Vec::new();
            let raw_map: HashMap<_, _> = parameters
                .iter()
                .map(|(p, _)| (p.id, format!("_enumerated_i{}", p.id.value())))
                .collect();
            for ((parameter, carrier), store) in parameters
                .iter()
                .zip(&wd.introduced_params.defined_params.store_and_infer_results)
            {
                let raw_id = &raw_map[&parameter.id];
                let member_name = format!("h_{}", store.primary_fact_id().value());
                let value =
                    self.compile_function_raw_expression_bound(carrier, &prior, &HashMap::new())?;
                domains.push(format!("({raw_id} : M.Value)"));
                domains.push(format!("({member_name} : M.mem {raw_id} {value})"));
                names.extend([raw_id.clone(), member_name.clone()]);
                objects.push(format!("let _value_i{} := Litex.semanticObject {raw_id} (M.member_isSet {member_name})", parameter.id.value()));
            }
            for domain in &fact.dom_facts {
                let name = format!("h_{}", domain.fact_id().value());
                domains.push(format!(
                    "({name} : {})",
                    self.compile_function_raw_predicate(domain, &prior, &raw_map)?
                ));
                names.push(name);
            }
            let raw_goal = enumeration_conjunction(
                fact.then_facts
                    .iter()
                    .map(|f| {
                        self.compile_function_raw_predicate(&f.clone().into(), &prior, &raw_map)
                    })
                    .collect::<Result<_, _>>()?,
            )?;
            proposition = format!("∀ {}, {raw_goal}", domains.join(" "));
            let mut lines = vec![format!("intro {}", names.join(" "))];
            lines.extend(objects);
            lines
        } else {
            vec![format!("intro {}", introductions.join(" "))]
        };
        lines.extend(definitions);
        let counts = self.validate_enumeration_product(&parameters, assignments, &prior)?;
        let proof = self.compile_enumeration_product(
            fact,
            &parameters,
            &counts,
            assignments,
            0,
            &raw_goals,
            &prior,
        )?;
        lines.push(format!("change {raw_goals}"));
        lines.push(format!("exact {proof}"));
        self.emit_by_completed_fact(
            &goal,
            (
                proposition,
                format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
            ),
            store,
            position,
            2,
            index,
            local,
        )
    }

    pub(super) fn compile_enumeration_assignment(
        &self,
        fact: &ForallFact,
        parameters: &[(&BoundName, &Obj)],
        assignment: &EnumerateAssignmentSuccess,
        values: &[&Obj],
        raw_goal: &str,
        caller: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let count = parameters.len();
        if values.len() != count {
            return Err(LeanCompileError::unsupported(
                "Enumeration/AssignmentStages",
            ));
        }
        let substitution = parameters
            .iter()
            .zip(values)
            .map(|((p, _), value)| (p.id, (*value).clone()))
            .collect::<HashMap<_, _>>();
        let scope = SourcePosition::new(
            Some(caller),
            SourceOwner::EnumerationAssignment(fact, assignment),
            0,
        );
        self.validate_parameter_store_capture(&assignment.introduced_params.defined_params)?;
        if assignment
            .introduced_params
            .auto_opened_struct_layers
            .is_some()
            || assignment
                .introduced_params
                .defined_params
                .store_and_infer_results
                .len()
                != count
            || assignment.binding_assumptions.len() != count
            || assignment.introduced_params.param_type_well_defined.len()
                != fact.typed_parameters.groups.len()
        {
            return Err(LeanCompileError::unsupported(
                "Enumeration/AssignmentStages",
            ));
        }
        for (group, formation) in fact
            .typed_parameters
            .groups
            .iter()
            .zip(&assignment.introduced_params.param_type_well_defined)
        {
            let (ParamType::Obj(carrier), ParamTypeWellDefinedProof::Obj(formation)) =
                (&group.param_type, formation)
            else {
                return Err(LeanCompileError::unsupported("Enumeration/ParameterWD"));
            };
            ensure_object(carrier, formation)?;
        }
        let outer = match caller.owner {
            SourceOwner::ForallWD(_, wd) => wd,
            _ => return Err(LeanCompileError::unsupported("Enumeration/Header")),
        };
        let mut lines = Vec::new();
        for (i, (parameter, carrier)) in parameters.iter().enumerate() {
            let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            let store = &assignment
                .introduced_params
                .defined_params
                .store_and_infer_results[i];
            let introduced = SourcePosition {
                before: i + 1,
                ..scope
            };
            let member = self.resolve_fact(store.primary_fact_id(), &introduced)?;
            let outer_id = outer
                .introduced_params
                .defined_params
                .store_and_infer_results[i]
                .primary_fact_id();
            if !matches!(&member, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == object.ir() && f.set.ir() == carrier.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "Enumeration/ParameterSubject",
                ));
            }
            self.validate_store(&store.store, &member)?;
            let proposition = self.fact_proposition(&member, &introduced)?;
            lines.push(self.emit_internal_fact(
                &member,
                &(proposition.clone(), format!("h_{}", outer_id.value())),
                &introduced,
            )?);
            lines.extend(self.compile_parameter_inferences(
                store,
                &member,
                &(proposition, format!("h_{}", member.fact_id().value())),
                &introduced,
            )?);
        }
        for (i, ((parameter, _), value)) in parameters.iter().zip(values).enumerate() {
            let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            let binding = &assignment.binding_assumptions[i];
            let prior = SourcePosition {
                before: count + i,
                ..scope
            };
            let complete = SourcePosition {
                before: count + i + 1,
                ..scope
            };
            let binding_fact =
                self.resolve_fact(binding.store_and_infer.primary_fact_id(), &complete)?;
            if !matches!(&binding_fact, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir() == object.ir() && f.right.ir() == value.ir())
            {
                return Err(LeanCompileError::unsupported("Enumeration/AssignmentOrder"));
            }
            self.compile_fact_wd(&binding.well_defined, &binding_fact, &prior)?;
            self.validate_store(&binding.store_and_infer.store, &binding_fact)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&binding.well_defined),
                usize::MAX,
            );
            let compiled = (
                self.fact_proposition(&binding_fact, &formed)?,
                enumeration_case_name(i, count),
            );
            lines.push(self.emit_internal_fact(&binding_fact, &compiled, &formed)?);
            lines.extend(self.compile_stored_inferences(
                &binding.store_and_infer,
                &binding_fact,
                &(compiled.0, format!("h_{}", binding_fact.fact_id().value())),
                &complete,
            )?);
        }
        let (premises, steps, goals) = match &assignment.outcome {
            EnumerateAssignmentOutcome::Proved {
                premise_assumptions,
                proof_steps,
                then_proofs,
            } => (
                premise_assumptions,
                proof_steps.as_slice(),
                then_proofs.as_slice(),
            ),
            EnumerateAssignmentOutcome::Skipped {
                premise_assumptions,
                ..
            } => (premise_assumptions, &[][..], &[][..]),
        };
        let raw: HashMap<_, _> = parameters
            .iter()
            .map(|(p, _)| (p.id, format!("(Litex.denote _value_i{})", p.id.value())))
            .collect();
        let bound = SourcePosition {
            before: 2 * count,
            ..scope
        };
        for (i, premise) in premises.iter().enumerate() {
            let original = fact
                .dom_facts
                .get(i)
                .ok_or_else(|| LeanCompileError::unsupported("Enumeration/PremiseArity"))?;
            let prior = SourcePosition {
                before: 2 * count + i,
                ..scope
            };
            let complete = SourcePosition {
                before: 2 * count + i + 1,
                ..scope
            };
            let actual = self.resolve_fact(premise.store_and_infer.primary_fact_id(), &complete)?;
            if !instantiated_fact_matches(original, &actual, &substitution) {
                return Err(LeanCompileError::unsupported("Enumeration/PremiseSubject"));
            }
            self.compile_fact_wd(&premise.well_defined, &actual, &prior)?;
            self.validate_store(&premise.store_and_infer.store, &actual)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&premise.well_defined),
                usize::MAX,
            );
            let actual_raw =
                self.compile_function_raw_predicate(&actual, &formed, &HashMap::new())?;
            let transport = self.compile_enumeration_transport(
                std::slice::from_ref(original),
                &parameters,
                values,
                &bound,
            )?;
            let term = format!(
                "(show {actual_raw} from Eq.mp {transport} h_{})",
                original.fact_id().value()
            );
            let compiled = (self.fact_proposition(&actual, &formed)?, term);
            lines.push(self.emit_internal_fact(&actual, &compiled, &formed)?);
            lines.extend(self.compile_stored_inferences(
                &premise.store_and_infer,
                &actual,
                &(compiled.0, format!("h_{}", actual.fact_id().value())),
                &complete,
            )?);
        }
        let head = 2 * count + premises.len();
        if let EnumerateAssignmentOutcome::Skipped {
            premise_index,
            negated_premise,
            ..
        } = &assignment.outcome
        {
            if *premise_index != premises.len() || *premise_index >= fact.dom_facts.len() {
                return Err(LeanCompileError::unsupported("Enumeration/SkippedPremise"));
            }
            let negated = source_subject(negated_premise)?;
            let Fact::AtomicFact(negative) = &negated else {
                return Err(LeanCompileError::unsupported("Enumeration/NegatedPremise"));
            };
            let Fact::AtomicFact(original) = &fact.dom_facts[*premise_index] else {
                return Err(LeanCompileError::unsupported("Enumeration/NegatedPremise"));
            };
            let expected = crate::ast::fact::negate_atomic_fact(original, negative.fact_id())
                .ok_or_else(|| LeanCompileError::unsupported("Enumeration/NegatedPremise"))?;
            if !instantiated_fact_matches(&expected.into(), &negated, &substitution) {
                return Err(LeanCompileError::unsupported(
                    "Enumeration/NegatedPremiseSubject",
                ));
            }
            let negative = self.compile_verify(
                negated_premise,
                &SourcePosition {
                    before: head,
                    ..scope
                },
            )?;
            let original_raw =
                self.compile_function_raw_predicate(&fact.dom_facts[*premise_index], caller, &raw)?;
            let transport = self.compile_enumeration_transport(
                std::slice::from_ref(&fact.dom_facts[*premise_index]),
                &parameters,
                values,
                &bound,
            )?;
            let negative_raw =
                self.compile_function_raw_predicate(&negated, caller, &HashMap::new())?;
            let contradiction = if crate::ast::fact::atomic_fact_has_positive_polarity(original) {
                "_negative _actual_guard"
            } else {
                "_actual_guard _negative"
            };
            lines.push(format!("have _excluded : ¬ ({original_raw}) := by\n  have _negative : {negative_raw} := {}\n  intro _source_guard\n  have _actual_guard := Eq.mp {transport} _source_guard\n  exact {contradiction}", negative.1));
            lines.push(format!(
                "exact False.elim (_excluded h_{})",
                fact.dom_facts[*premise_index].fact_id().value()
            ));
        } else {
            if premises.len() != fact.dom_facts.len() || goals.len() != fact.then_facts.len() {
                return Err(LeanCompileError::unsupported("Enumeration/ConclusionArity"));
            }
            for (i, step) in steps.iter().enumerate() {
                lines.push(self.compile_statement_in_scope(
                    step,
                    &SourcePosition {
                        before: head + i,
                        ..scope
                    },
                    i + 1,
                    true,
                )?);
            }
            let mut proofs = Vec::new();
            for (i, (source, proved)) in fact.then_facts.iter().zip(goals).enumerate() {
                let source = Fact::from(source.clone());
                let actual = source_subject(&proved.verify_result)?;
                if !instantiated_fact_matches(&source, &actual, &substitution) {
                    return Err(LeanCompileError::unsupported(
                        "Enumeration/ConclusionSubject",
                    ));
                }
                let prior = SourcePosition {
                    before: head + steps.len() + i,
                    ..scope
                };
                let compiled = self.compile_verify(&proved.verify_result, &prior)?;
                self.validate_store(&proved.store_and_infer.store, &actual)?;
                let raw = self.compile_function_raw_predicate(&actual, &prior, &HashMap::new())?;
                // This original conclusion is emitted below; the final
                // conjunction cites it instead of copying its proof again.
                proofs.push(format!("(show {raw} from h_{})", actual.fact_id().value()));
                lines.push(self.emit_internal_fact(&actual, &compiled, &prior)?);
                lines.extend(self.compile_stored_inferences(
                    &proved.store_and_infer,
                    &actual,
                    &(compiled.0, format!("h_{}", actual.fact_id().value())),
                    &SourcePosition {
                        before: head + steps.len() + i + 1,
                        ..scope
                    },
                )?);
            }
            let proof = enumeration_intro(proofs)?;
            lines.push(format!("show {raw_goal}"));
            let transport = self.compile_enumeration_transport(
                &fact
                    .then_facts
                    .iter()
                    .cloned()
                    .map(Fact::from)
                    .collect::<Vec<_>>(),
                &parameters,
                values,
                &bound,
            )?;
            lines.push(format!("exact Eq.mpr {transport} {proof}"));
        }
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}

pub(super) fn enumeration_conjunction(mut values: Vec<String>) -> Result<String, LeanCompileError> {
    let mut result = values
        .pop()
        .ok_or_else(|| LeanCompileError::unsupported("Enumeration/EmptyConclusions"))?;
    while let Some(left) = values.pop() {
        result = format!("({left} ∧ {result})");
    }
    Ok(result)
}
fn enumeration_intro(mut values: Vec<String>) -> Result<String, LeanCompileError> {
    let mut result = values
        .pop()
        .ok_or_else(|| LeanCompileError::unsupported("Enumeration/EmptyConclusions"))?;
    while let Some(left) = values.pop() {
        result = format!("(And.intro {left} {result})");
    }
    Ok(result)
}
