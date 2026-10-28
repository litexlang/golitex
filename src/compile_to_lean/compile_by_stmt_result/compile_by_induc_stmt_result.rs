use super::induction_evidence::InductionEvidence;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    ByInducBodySuccess, ByInducCaseSuccess, ExecByInducStmtResult,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_induc_result(
        &self,
        result: &ExecByInducStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecByInducStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Induction/Failed"));
        };
        self.compile_induction(proof.into(), position, index, local)
    }

    pub(in crate::compile_to_lean) fn compile_by_strong_induc_result(
        &self,
        result: &crate::execute::execute_by_stmt::ExecByStrongInducStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let crate::execute::execute_by_stmt::ExecByStrongInducStmtResult::Success(proof) = result
        else {
            return Err(LeanCompileError::unsupported("StrongInduction/Failed"));
        };
        self.compile_induction(proof.into(), position, index, local)
    }

    fn compile_induction(
        &self,
        proof: InductionEvidence<'_>,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if !is_exact_zero(&proof.induc_from)
            || proof.goals.is_empty()
            || proof.goals.len() != proof.goals_wd.len()
        {
            return Err(LeanCompileError::unsupported(
                "Induction/ZeroLowerBoundAndGoals",
            ));
        }
        let from = source_subject(&proof.from_in_z)?;
        if !matches!(&from, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == *proof.induc_from && f.set == Obj::StandardSet(StandardSet::Z))
        {
            return Err(LeanCompileError::unsupported("Induction/FromSubject"));
        }
        let from_compiled = self.compile_verify(&proof.from_in_z, position)?;
        let header = SourcePosition::new(Some(position), SourceOwner::Induction(proof), 0);
        self.validate_parameter_store_capture(&proof.introduced_parameter.defined_params)?;
        let introduced = SourcePosition {
            before: 1,
            ..header
        };
        let store = induction_parameter_store(&proof.introduced_parameter)?;
        let carrier = induction_carrier(&proof.introduced_parameter)?;
        if let ParamTypeWellDefinedProof::Obj(wd) =
            &proof.introduced_parameter.param_type_well_defined[0]
        {
            self.compile_wd(wd, &header)?;
        }
        let (mut binders, mut introductions) =
            self.introduce_member_parameter(&proof.parameter, carrier, store, &introduced)?;
        let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
        let h_z = format!("h_{}", fact.fact_id().value());
        let mut definitions = self.compile_parameter_inferences(
            store,
            &fact,
            &(self.fact_proposition(&fact, &introduced)?, h_z.clone()),
            &introduced,
        )?;
        let domain = &proof.goal_domain;
        let source_domain = self.resolve_fact(
            domain.store_and_infer.primary_fact_id(),
            &SourcePosition {
                before: 2,
                ..header
            },
        )?;
        validate_induction_domain(&source_domain, &proof.parameter, &proof.induc_from)?;
        self.compile_fact_wd(&domain.well_defined, &source_domain, &introduced)?;
        let domain_formed = SourcePosition::new(
            Some(&introduced),
            SourceOwner::FactWD(&domain.well_defined),
            usize::MAX,
        );
        let h_lower = format!("h_{}", source_domain.fact_id().value());
        let domain_prop = self.fact_proposition(&source_domain, &domain_formed)?;
        binders.push(format!("({h_lower} : {domain_prop})"));
        introductions.push(h_lower.clone());
        let complete = SourcePosition {
            before: 2,
            ..header
        };
        definitions.extend(self.compile_stored_inferences(
            &domain.store_and_infer,
            &source_domain,
            &(domain_prop, h_lower.clone()),
            &complete,
        )?);
        let mut propositions = Vec::new();
        for (j, (goal, wd)) in proof.goals.iter().zip(proof.goals_wd).enumerate() {
            let VerifyFactWellDefinedResult::Success(wd) = wd else {
                return Err(LeanCompileError::unsupported("Induction/GoalWD"));
            };
            let prior = SourcePosition {
                before: 2 + j,
                ..header
            };
            self.compile_fact_wd(wd, goal, &prior)?;
            let formed = SourcePosition::new(Some(&prior), SourceOwner::FactWD(wd), usize::MAX);
            propositions.push(self.fact_proposition(goal, &formed)?);
        }
        let goal_prop = induction_conjunction(propositions)?;
        let meaning = self.scope_proposition(goal_prop, &definitions);
        let proposition = format!("∀ {}, {meaning}", binders.join(" "));
        let raw_id = format!("_raw_i{}", proof.parameter.id.value());
        let raw = HashMap::from([(proof.parameter.id, raw_id.clone())]);
        let raw_goal = induction_conjunction(
            proof
                .goals
                .iter()
                .map(|goal| self.compile_function_raw_predicate(goal, position, &raw))
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let predicate = format!("(fun ({raw_id} : M.Value) => {raw_goal})");
        let (base, step) = match &proof.body {
            ByInducBodySuccess::Structured { base, step }
            | ByInducBodySuccess::Unstructured { base, step } => (base, step),
        };
        let base =
            self.compile_induction_case(&proof, base, &header, &predicate, &from_compiled.1, true)?;
        let step = self.compile_induction_case(
            &proof,
            step,
            &header,
            &predicate,
            "_induction_integer",
            false,
        )?;
        // A local Lean constant cannot quantify over a fresh universe level.
        // Its induction predicate already acts on the common semantic values;
        // keep that local interface and observe the original generic object
        // when the exact stored conclusion is cited. Global exports keep their
        // ordinary source-object binders.
        let (proposition, mut body) = if local {
            let raw_domain = self.compile_function_raw_predicate(&source_domain, position, &raw)?;
            (
                format!("∀ ({raw_id} : M.Value) ({h_z} : M.mem {raw_id} (M.standard .integer)) ({h_lower} : {raw_domain}), {raw_goal}"),
                vec![
                    format!("intro {raw_id} {h_z} {h_lower}"),
                    format!("let _value_i{} := Litex.semanticObject (M := M) {raw_id} (M.member_isSet {h_z})", proof.parameter.id.value()),
                ],
            )
        } else {
            (
                proposition,
                vec![format!("intro {}", introductions.join(" "))],
            )
        };
        body.extend(definitions);
        let bridge = if proof.strong {
            "integerStrongInductionFromZero"
        } else {
            "integerInductionFromZero"
        };
        body.push(format!(
            "exact Litex.{bridge} {predicate} {base} {step} _value_i{} {h_z} {h_lower}",
            proof.parameter.id.value()
        ));
        let compiled = (
            proposition,
            format!("(by\n  {}\n)", body.join("\n").replace('\n', "\n  ")),
        );
        let final_site = SourcePosition {
            before: 1,
            ..*position
        };
        let source = self.resolve_fact(proof.stored.primary_fact_id(), &final_site)?;
        let Fact::ForallFact(final_fact) = &source else {
            return Err(LeanCompileError::unsupported("Induction/FinalForall"));
        };
        let groups = &final_fact.typed_parameters.groups;
        if groups.len() != 1
            || groups[0].params != vec![proof.parameter.clone()]
            || groups[0].param_type != ParamType::Obj(carrier.clone())
            || final_fact.dom_facts.len() != 1
            || final_fact.then_facts.len() != proof.goals.len()
        {
            return Err(LeanCompileError::unsupported("Induction/FinalShape"));
        }
        if !instantiated_fact_matches(&source_domain, &final_fact.dom_facts[0], &HashMap::new())
            || !final_fact
                .then_facts
                .iter()
                .zip(proof.goals)
                .all(|(a, b)| instantiated_fact_matches(&Fact::from(a.clone()), b, &HashMap::new()))
        {
            return Err(LeanCompileError::unsupported("Induction/FinalSubject"));
        }
        self.compile_completed_fact_statement(
            &source,
            compiled,
            &proof.stored,
            position,
            index,
            local,
        )
    }

    fn compile_strong_induction_hypothesis(
        &self,
        induction: &InductionEvidence<'_>,
        source: &Fact,
        wd: &FactWellDefinedProof,
        index: usize,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (Fact::ForallFact(fact), FactWellDefinedProof::ForallFact(wd)) = (source, wd) else {
            return Err(LeanCompileError::unsupported(
                "StrongInduction/HypothesisFamily",
            ));
        };
        let [group] = fact.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "StrongInduction/HypothesisParameters",
            ));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "StrongInduction/HypothesisParameters",
            ));
        };
        let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let current = Obj::Identifier(IdentifierObj::from_bound_name(induction.parameter));
        if group.param_type != ParamType::Obj(Obj::StandardSet(StandardSet::Z))
            || fact.dom_facts.len() != 2
            || fact.then_facts.len() != 1
            || !matches!(&fact.dom_facts[0], Fact::AtomicFact(AtomicFact::GreaterEqualFact(f))
                if f.left.ir() == object.ir() && f.right.ir() == induction.induc_from.ir())
            || !matches!(&fact.dom_facts[1], Fact::AtomicFact(AtomicFact::LessEqualFact(f))
                if f.left.ir() == object.ir() && f.right.ir() == current.ir())
            || !instantiated_fact_matches(
                &induction.goals[index],
                &fact.then_facts[0].clone().into(),
                &HashMap::from([(induction.parameter.id, object)]),
            )
        {
            return Err(LeanCompileError::unsupported(
                "StrongInduction/HypothesisSubject",
            ));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::ForallWD(fact, wd), 0);
        let (binders, introductions, mut lines) = self.compile_forall_head(
            fact,
            &wd.detailed_ref().introduced_params,
            &wd.detailed_ref().assumed_dom_facts,
            &scope,
        )?;
        let store = wd
            .detailed_ref()
            .introduced_params
            .defined_params
            .store_and_infer_results
            .first()
            .ok_or_else(|| {
                LeanCompileError::unsupported("StrongInduction/HypothesisParameterStore")
            })?;
        let member = format!("h_{}", store.primary_fact_id().value());
        let low = format!("h_{}", fact.dom_facts[0].fact_id().value());
        let high = format!("h_{}", fact.dom_facts[1].fact_id().value());
        let proof = format!(
            "(_induction_hypothesis (Litex.denote _value_i{}) {member} {low} {high})",
            parameter.id.value()
        );
        let then = Fact::from(fact.then_facts[0].clone());
        let formation = wd
            .detailed_ref()
            .then
            .first()
            .ok_or_else(|| LeanCompileError::unsupported("StrongInduction/HypothesisGoalWD"))?;
        let complete = SourcePosition { before: 3, ..scope };
        let formed =
            SourcePosition::new(Some(&complete), SourceOwner::FactWD(formation), usize::MAX);
        let conclusion = self.fact_proposition(&then, &formed)?;
        let proposition = format!(
            "∀ {}, {}",
            binders.join(" "),
            self.scope_proposition(conclusion, &lines)
        );
        lines.insert(0, format!("intro {}", introductions.join(" ")));
        lines.push(format!(
            "exact {}",
            conjunction_projection(&proof, index, induction.goals.len())
        ));
        Ok((
            proposition,
            format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
        ))
    }

    fn compile_induction_case(
        &self,
        induction: &InductionEvidence<'_>,
        case: &ByInducCaseSuccess,
        header: &SourcePosition<'_>,
        predicate: &str,
        integer_proof: &str,
        base: bool,
    ) -> Result<String, LeanCompileError> {
        if case.goals_verified.len() != induction.goals.len()
            || case.assumptions.len() != if base { 1 } else { 1 + induction.goals.len() }
        {
            return Err(LeanCompileError::unsupported("Induction/CaseStages"));
        }
        let scope = SourcePosition::new(
            Some(header),
            SourceOwner::InductionCase(*induction, case),
            0,
        );
        self.validate_parameter_store_capture(&case.introduced_parameter.defined_params)?;
        let introduced = SourcePosition { before: 1, ..scope };
        let store = induction_parameter_store(&case.introduced_parameter)?;
        induction_carrier(&case.introduced_parameter)?;
        if let ParamTypeWellDefinedProof::Obj(wd) =
            &case.introduced_parameter.param_type_well_defined[0]
        {
            self.compile_wd(wd, &scope)?;
        }
        let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
        let original = Obj::Identifier(IdentifierObj::from_bound_name(&induction.parameter));
        if !matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == original.ir() && f.set == Obj::StandardSet(StandardSet::Z))
        {
            return Err(LeanCompileError::unsupported("Induction/CaseParameter"));
        }
        self.validate_store(&store.store, &fact)?;
        let id = induction.parameter.id.value();
        let raw = format!("_raw_i{id}");
        let h = format!("h_{}", fact.fact_id().value());
        let mut lines = if base {
            Vec::new()
        } else {
            vec![format!(
                "intro {raw} _induction_integer _induction_nonnegative _induction_hypothesis"
            )]
        };
        if base {
            lines.push(format!("let {raw} : M.Value := M.number 0"));
        }
        lines.extend([
            format!("have {h} : M.mem {raw} (M.standard .integer) := {integer_proof}"),
            format!("let _value_i{id} := Litex.semanticObject (M := M) {raw} (M.member_isSet {h})"),
            format!(
                "have {h} : {} := {h}",
                self.fact_proposition(&fact, &introduced)?
            ),
        ]);
        lines.extend(self.compile_parameter_inferences(
            store,
            &fact,
            &(self.fact_proposition(&fact, &introduced)?, h),
            &introduced,
        )?);
        for (j, assumption) in case.assumptions.iter().enumerate() {
            let prior = SourcePosition {
                before: 1 + j,
                ..scope
            };
            let complete = SourcePosition {
                before: 2 + j,
                ..scope
            };
            let source =
                self.resolve_fact(assumption.store_and_infer.primary_fact_id(), &complete)?;
            self.compile_fact_wd(&assumption.well_defined, &source, &prior)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&assumption.well_defined),
                usize::MAX,
            );
            let strong_hypothesis = if induction.strong && j > 0 {
                Some(self.compile_strong_induction_hypothesis(
                    induction,
                    &source,
                    &assumption.well_defined,
                    j - 1,
                    &prior,
                )?)
            } else {
                None
            };
            let proposition = if let Some(compiled) = &strong_hypothesis {
                compiled.0.clone()
            } else {
                self.fact_proposition(&source, &formed)?
            };
            let proof = if j == 0 {
                if base {
                    if !matches!(&source, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir() == original.ir() && f.right == *induction.induc_from)
                    {
                        return Err(LeanCompileError::unsupported("Induction/BaseAssumption"));
                    }
                    "(by rfl)".to_string()
                } else {
                    validate_induction_domain(
                        &source,
                        &induction.parameter,
                        &induction.induc_from,
                    )?;
                    "_induction_nonnegative".to_string()
                }
            } else if induction.strong {
                strong_hypothesis.unwrap().1
            } else {
                if !instantiated_fact_matches(&induction.goals[j - 1], &source, &HashMap::new()) {
                    return Err(LeanCompileError::unsupported("Induction/HypothesisSubject"));
                }
                conjunction_projection("_induction_hypothesis", j - 1, induction.goals.len())
            };
            let compiled = (proposition, proof);
            lines.push(self.emit_internal_fact(&source, &compiled, &formed)?);
            lines.extend(self.compile_stored_inferences(
                &assumption.store_and_infer,
                &source,
                &(compiled.0, format!("h_{}", source.fact_id().value())),
                &complete,
            )?);
        }
        let prefix = 1 + case.assumptions.len();
        for (j, statement) in case.proof_steps.iter().enumerate() {
            lines.push(self.compile_statement_in_scope(
                statement,
                &SourcePosition {
                    before: prefix + j,
                    ..scope
                },
                j + 1,
                true,
            )?);
        }
        let complete = SourcePosition {
            before: prefix + case.proof_steps.len(),
            ..scope
        };
        let mut proofs = Vec::new();
        let at = if base {
            induction.induc_from.clone()
        } else {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(original),
                right: Box::new(Obj::Literal(Literal::Number(Number::new("1".into())))),
            }))
        };
        let substitution = HashMap::from([(induction.parameter.id, at)]);
        for (j, (goal, result)) in induction.goals.iter().zip(&case.goals_verified).enumerate() {
            if !instantiated_fact_matches(goal, &source_subject(result)?, &substitution) {
                return Err(LeanCompileError::unsupported(
                    "Induction/CaseConclusionSubject",
                ));
            }
            proofs.push(
                self.compile_verify(
                    result,
                    &SourcePosition {
                        before: complete.before + j,
                        ..complete
                    },
                )?
                .1,
            );
        }
        let mut conclusion = proofs
            .pop()
            .ok_or_else(|| LeanCompileError::unsupported("Induction/EmptyCaseGoals"))?;
        while let Some(left) = proofs.pop() {
            conclusion = format!("(And.intro {left} {conclusion})");
        }
        let target = if base {
            "(M.number 0)".to_string()
        } else {
            format!("(M.addValue {raw} (M.number 1))")
        };
        lines.push(format!("show {predicate} {target}"));
        lines.push(format!("exact {conclusion}"));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}

fn induction_parameter_store(
    intro: &IntroduceTypedParametersResult,
) -> Result<&StoreFactAndInferResult, LeanCompileError> {
    if intro.auto_opened_struct_layers.is_some()
        || intro.defined_params.store_and_infer_results.len() != 1
        || intro.param_type_well_defined.len() != 1
    {
        return Err(LeanCompileError::unsupported("Induction/ParameterCapture"));
    }
    Ok(&intro.defined_params.store_and_infer_results[0])
}

fn induction_carrier(intro: &IntroduceTypedParametersResult) -> Result<&Obj, LeanCompileError> {
    let Some(ParamTypeWellDefinedProof::Obj(wd)) = intro.param_type_well_defined.first() else {
        return Err(LeanCompileError::unsupported("Induction/ParameterWD"));
    };
    let obj = wd.obj();
    if obj != &Obj::StandardSet(StandardSet::Z) {
        return Err(LeanCompileError::unsupported("Induction/IntegerCarrier"));
    }
    Ok(obj)
}

fn validate_induction_domain(
    fact: &Fact,
    parameter: &BoundName,
    from: &Obj,
) -> Result<(), LeanCompileError> {
    if matches!(fact, Fact::AtomicFact(AtomicFact::GreaterEqualFact(f)) if f.left.ir() == Obj::Identifier(IdentifierObj::from_bound_name(parameter)).ir() && &f.right == from)
    {
        Ok(())
    } else {
        Err(LeanCompileError::unsupported("Induction/DomainSubject"))
    }
}

fn induction_conjunction(mut parts: Vec<String>) -> Result<String, LeanCompileError> {
    let mut result = parts
        .pop()
        .ok_or_else(|| LeanCompileError::unsupported("Induction/EmptyGoals"))?;
    while let Some(left) = parts.pop() {
        result = format!("(({left}) ∧ ({result}))");
    }
    Ok(result)
}
