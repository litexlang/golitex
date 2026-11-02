//! Divergence: replay the sum of the original coordinate partial derivatives.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::selector::{
    DivergenceAtWellDefinedProof, MultivariableSelectorSelectionProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainRequirementProof, PredicateDomainWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
impl LitexToLeanCompiler {
    pub(super) fn compile_divergence_wd(
        &self,
        object: &DivergenceAt,
        proof: &DivergenceAtWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [
            object.function.as_ref(),
            object.point.as_ref(),
            object.dimension.as_ref(),
        ];
        let stages = &proof.stages;
        if stages.argument_well_defined.len() != 3 {
            return Err(invalid("WDArguments"));
        }
        let mut binders = Vec::new();
        let mut certified_arguments = Vec::new();
        for (i, (arg, child)) in args.iter().zip(&stages.argument_well_defined).enumerate() {
            ensure_object(arg, child)?;
            let compiled = self.compile_wd(
                child,
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )?;
            binders.push(format!("let _multivariable_arg_{i} := {compiled}"));
            certified_arguments.push(format!("({compiled})"));
        }
        let mut lines = self.compile_divergence_domain(
            args[0],
            args[1],
            args[2],
            None,
            &stages.function_domain,
            &stages.domains,
            position,
        )?;
        let selected = match &stages.selection {
            MultivariableSelectorSelectionProof::Candidate(c) => {
                let (q, negative) = parts(&c.fact).ok_or_else(|| invalid("CandidateKind"))?;
                if negative
                    || q.function.ir() != args[0].ir()
                    || q.point.ir() != args[1].ir()
                    || q.dimension.ir() != args[2].ir()
                {
                    return Err(invalid("CandidateSubject"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                    c.searched_proof.as_ref()
                else {
                    return Err(invalid("CandidateCitation"));
                };
                let term = self.compile_known_atomic(known, &c.fact, position)?;
                let value = self.compile_function_raw_expression_bound(
                    &q.value,
                    position,
                    &HashMap::new(),
                )?;
                format!("(Litex.divergenceExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], args[2], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by\n  have _original_divergence_exists : {ty} := {term}\n  obtain ⟨v,hv,hc⟩ := _original_divergence_exists\n  exact ⟨v,hv,hc⟩\n)")
            }
        };
        lines.push(format!(
            "exact ⟨h_{},_multivariable_real,h_{},_divergence_point_domain,{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[4].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.divergenceRepresentation (M := M)) (Litex.DivergenceObj.mk {}) (by\n  {}\n))",
            binders.join("; "),
            certified_arguments.join(" "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_divergence_equality(
        &self,
        fact: &EqualFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_multivariable::MultivariableEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_multivariable::MultivariableEqualityProof as P;
        let P::SelectedValue(proof) = proof else {
            return Err(invalid("EqualityRoute"));
        };
        let (selected, value, obj, reverse) = match (&fact.left, &fact.right) {
            (s @ Obj::DerivativeOperator(DerivativeOperator::Divergence(o)), v) => (s, v, o, false),
            (v, s @ Obj::DerivativeOperator(DerivativeOperator::Divergence(o))) => (s, v, o, true),
            _ => return Err(invalid("SelectedSubject")),
        };
        let (candidate, negative) =
            parts(&proof.candidate.fact).ok_or_else(|| invalid("EqualityCandidate"))?;
        if negative
            || candidate.function.ir() != obj.function.ir()
            || candidate.point.ir() != obj.point.ir()
            || candidate.dimension.ir() != obj.dimension.ir()
        {
            return Err(invalid("EqualityCandidateSubject"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
            proof.candidate.searched_proof.as_ref()
        else {
            return Err(invalid("EqualityCitation"));
        };
        let h = self.compile_known_atomic(known, &proof.candidate.fact, position)?;
        let q = EqualFact {
            fact_id: fact.fact_id,
            left: candidate.value.clone(),
            right: value.clone(),
            line_file: None,
        };
        let eq = self.compile_equality_search(&q, &proof.value_equality, position)?;
        let selected = self.compile_object_reference(selected, position)?;
        let raw = self.compile_function_raw_expression_bound(
            &candidate.value,
            position,
            &HashMap::new(),
        )?;
        let term = format!("((Litex.divergenceEqCandidate {selected} {raw} {h}).trans {eq})");
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_divergence_domain(
        &self,
        f: &Obj,
        p: &Obj,
        n: &Obj,
        value: Option<&Obj>,
        source: &CompleteFunctionDomainProof,
        requirements: &[PredicateDomainWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("Signature"))?;
        if requirements.len() != 6 + usize::from(value.is_some()) {
            return Err(invalid("DomainStages"));
        }
        let args = 3 + usize::from(value.is_some());
        let mut lines = self.compile_multivariable_limit_domain(
            f,
            p,
            n,
            Some(n),
            None,
            source,
            &requirements[..5],
            args,
            position,
        )?;
        for (i, r) in requirements.iter().enumerate().skip(5) {
            let valid = match (i, &r.requirement) {
                (5, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    q.element.ir() == p.ir() && q.set.ir() == domain.ir()
                }
                (6, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    value.is_some_and(|v| q.element.ir() == v.ir())
                        && q.set == Obj::StandardSet(StandardSet::R)
                }
                _ => false,
            };
            if !valid {
                return Err(invalid("RequirementSubject"));
            }
            let PredicateDomainRequirementProof::Verified(proof) = &r.result else {
                return Err(invalid("RequirementCapture"));
            };
            if source_subject(proof)? != r.requirement {
                return Err(invalid("RequirementProof"));
            }
            let (ty, term) = self.compile_verify(
                proof,
                &SourcePosition {
                    before: args + i,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        let f = self.compile_object_reference(f, position)?;
        let p = self.compile_object_reference(p, position)?;
        lines.push(format!("have _divergence_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := (_multivariable_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _multivariable_signature.domain_isSet _multivariable_member).symm) ▸ h_{}",requirements[5].requirement.fact_id().value()));
        Ok(lines)
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_divergence_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (InferAtomicFactResult::MultivariableAnalysisFact(rules), Fact::AtomicFact(a)) =
            (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let (r, negative) = parts(a).ok_or_else(|| invalid("InferencePredicate"))?;
        let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        if negative
            || p.source_fact_id != seed.fact_id()
            || p.derived.len() != if p.function_domain.is_some() { 2 } else { 1 }
        {
            return Err(invalid("InferenceIdentity"));
        }
        let facts = p
            .derived
            .iter()
            .map(|s| {
                let f = self.resolve_fact(s.primary_fact_id(), position)?;
                self.validate_store(&s.store, &f)?;
                Ok(f)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let values = [&r.function, &r.point, &r.dimension, &r.value]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let [f, point, n, _] = values.as_slice() else {
            unreachable!()
        };
        let mut lines = Vec::new();
        if let Some(source) = &p.function_domain {
            let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
                &source.signature,
            )
            .ok_or_else(|| invalid("InferenceSignature"))?;
            validate_clauses(r, &domain, &facts[..1])?;
            let (view, equal) =
                self.compile_multivariable_limit_view(&r.function, source, position)?;
            let ty = self.compile_function_raw_predicate(&facts[0], position, &HashMap::new())?;
            let term=format!("(by\n{view}\n  obtain ⟨diagonal,h_diagonal,h_parts,h_sum⟩ := ({}).2\n  refine ⟨diagonal,h_diagonal,?_,h_sum⟩\n  intro k h_k\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  refine ⟨h_k,h_k,?_⟩\n  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D k) {point} {n} k (Litex.FunctionSemantics.callValue (Litex.denote diagonal) k)) {equal}.symm).mp (h_parts k h_k)\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(&r.function, &r.point, &r.dimension, target)?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let term = format!(
            "(by obtain ⟨v,hv,hc⟩ := Litex.divergenceExistsOfCandidate {} {}; exact ⟨v,hv,hc⟩)",
            values.join(" "),
            compiled.1
        );
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }

    pub(super) fn compile_divergence_definition(
        &self,
        r: &DivergenceAtRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::DivergenceAtRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &proof.function_domain.signature,
        )
        .ok_or_else(|| invalid("DefinitionSignature"))?;
        validate_clauses(r, &domain, &proof.requirement_facts)?;
        let [child] = proof.proof_of_requirement_facts.as_slice() else {
            return Err(invalid("DefinitionProofCount"));
        };
        if source_subject(child)? != proof.requirement_facts[0] {
            return Err(invalid("DefinitionProofSubject"));
        }
        let (ty, term) = self.compile_verify(child, &position.atomic_search_prior(0)?)?;
        let member = position
            .with_visible_membership(&r.value, &Obj::StandardSet(StandardSet::R), &mut |p, at| {
                self.compile_verify(p, at).map(|v| v.1)
            })?
            .ok_or_else(|| invalid("DefinitionValueMembership"))?;
        let (view, equal) =
            self.compile_multivariable_limit_view(&r.function, &proof.function_domain, position)?;
        let values = [&r.function, &r.point, &r.dimension]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let [f, point, n] = values.as_slice() else {
            unreachable!()
        };
        Ok(format!("(by\n{view}\n  have _divergence_clause : {ty} := {term}\n  obtain ⟨diagonal,h_diagonal,h_parts,h_sum⟩ := _divergence_clause\n  refine ⟨{member},diagonal,h_diagonal,?_,h_sum⟩\n  intro k h_k\n  obtain ⟨_,_,h_partial⟩ := (Litex.SetSemantics.sep_members _ _ _).mp (h_parts k h_k)\n  exact (congrArg (fun D => Litex.HasPartialDerivativeAtValue M (Litex.componentFunctionValue {f} D k) {point} {n} k (Litex.FunctionSemantics.callValue (Litex.denote diagonal) k)) {equal}).mp h_partial\n)"))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DivergenceAt/{stage}"))
}

pub(super) fn validate_clauses(
    r: &DivergenceAtRelation,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    use crate::execute::execute_fact_stmt::multivariable::helper::{apply, indices};
    let [Fact::ExistFact(e)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    let v = parameter(
        &e.typed_parameters,
        &super::compile_multivariable_scalar_limit::vector_set(&r.dimension),
    )?;
    let v_obj = Obj::Identifier(IdentifierObj::from_bound_name(v));
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(all)), QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(sum))] =
        e.facts.as_slice()
    else {
        return Err(invalid("DefinitionBody"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(good)) = &all.right else {
        return Err(invalid("DefinitionIndexSet"));
    };
    let index = indices(r.dimension.clone());
    if all.left.ir() != index.ir() || good.param_set.ir() != index.ir() {
        return Err(invalid("DefinitionIndices"));
    }
    let [QuantifierFreeFact::AtomicFact(a)] = good.facts.as_slice() else {
        return Err(invalid("DefinitionPartial"));
    };
    let (p, negative) = super::compile_partial_derivative::parts(a)
        .ok_or_else(|| invalid("DefinitionPartialKind"))?;
    let k = Obj::Identifier(IdentifierObj::from_bound_name(&good.param_binding));
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(component)) = &p.function else {
        return Err(invalid("DefinitionComponent"));
    };
    let [input] = component.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("DefinitionComponentParameters"));
    };
    if input.params.len() != 1
        || input.param_type.ir() != domain.ir()
        || !component.body.dom_facts.is_empty()
        || component.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("DefinitionComponentDomain"));
    }
    let input_obj = Obj::Identifier(IdentifierObj::from_bound_name(&input.params[0]));
    let body = apply(&apply(&r.function, vec![input_obj]), vec![k.clone()]);
    let ids = [v.id, good.param_binding.id, input.params[0].id];
    if ids[0] == ids[1]
        || ids[0] == ids[2]
        || ids[1] == ids[2]
        || [&r.function, &r.point, &r.dimension, &r.value, domain]
            .iter()
            .any(|o| ids.iter().any(|id| contains_parameter(o, *id)))
    {
        return Err(invalid("DefinitionCapture"));
    }
    if negative
        || component.equal_to.ir() != body.ir()
        || p.point.ir() != r.point.ir()
        || p.dimension.ir() != r.dimension.ir()
        || p.coordinate.ir() != k.ir()
        || p.value.ir() != apply(&v_obj, vec![k]).ir()
    {
        return Err(invalid("DefinitionSubject"));
    }
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) = &sum.left else {
        return Err(invalid("DefinitionSum"));
    };
    if s.set.ir() != index.ir() || s.func.ir() != v_obj.ir() || sum.right.ir() != r.value.ir() {
        return Err(invalid("DefinitionSumSubject"));
    }
    Ok(())
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&DivergenceAtRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::DivergenceAt(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::DivergenceAt(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn existence(f: &Obj, p: &Obj, n: &Obj, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if [f, p, n].iter().any(|o| contains_parameter(o, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(a)] if parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.dimension.ir()==n.ir()&&r.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir()))
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
