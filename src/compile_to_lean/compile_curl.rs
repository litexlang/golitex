//! Curl: replay the six coordinate partials in the original three-dimensional convention.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::selector::{
    CurlAtWellDefinedProof, MultivariableSelectorSelectionProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainRequirementProof, PredicateDomainWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
impl LitexToLeanCompiler {
    pub(super) fn compile_curl_wd(
        &self,
        object: &CurlAt,
        proof: &CurlAtWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [object.function.as_ref(), object.point.as_ref()];
        let stages = &proof.stages;
        if stages.argument_well_defined.len() != 2 {
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
        let mut lines = self.compile_curl_domain(
            args[0],
            args[1],
            None,
            &stages.function_domain,
            &stages.domains,
            position,
        )?;
        let selected = match &stages.selection {
            MultivariableSelectorSelectionProof::Candidate(c) => {
                let (q, negative) = parts(&c.fact).ok_or_else(|| invalid("CandidateKind"))?;
                if negative || q.function.ir() != args[0].ir() || q.point.ir() != args[1].ir() {
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
                format!("(Litex.curlExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by\n  have _original_curl_exists : {ty} := {term}\n  obtain ⟨v,hv,hc⟩ := _original_curl_exists\n  exact ⟨v,hv,hc⟩\n)")
            }
        };
        lines.push(format!(
            "exact ⟨_multivariable_real,h_{},_curl_point_domain,{selected}⟩",
            stages.domains[4].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.curlRepresentation (M := M)) (Litex.CurlObj.mk {}) (by\n  {}\n))",
            binders.join("; "),
            certified_arguments.join(" "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_curl_equality(
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
            (s @ Obj::DerivativeOperator(DerivativeOperator::Curl(o)), v) => (s, v, o, false),
            (v, s @ Obj::DerivativeOperator(DerivativeOperator::Curl(o))) => (s, v, o, true),
            _ => return Err(invalid("SelectedSubject")),
        };
        let (candidate, negative) =
            parts(&proof.candidate.fact).ok_or_else(|| invalid("EqualityCandidate"))?;
        if negative
            || candidate.function.ir() != obj.function.ir()
            || candidate.point.ir() != obj.point.ir()
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
        let term = format!("((Litex.curlEqCandidate {selected} {raw} {h}).trans {eq})");
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_curl_domain(
        &self,
        f: &Obj,
        p: &Obj,
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
        let n = crate::execute::execute_fact_stmt::multivariable::helper::number(3);
        let args = 2 + usize::from(value.is_some());
        let mut lines = self.compile_multivariable_limit_domain(
            f,
            p,
            &n,
            Some(&n),
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
                        && q.set.ir()
                            == super::compile_multivariable_scalar_limit::vector_set(&n).ir()
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
        lines.push(format!("have _curl_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := (_multivariable_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _multivariable_signature.domain_isSet _multivariable_member).symm) ▸ h_{}",requirements[5].requirement.fact_id().value()));
        Ok(lines)
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_curl_inferences(
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
        let values = [&r.function, &r.point, &r.value]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let [f, point, value] = values.as_slice() else {
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
            // These component functions are part of the checked defining clause,
            // not new object constructors. Render its equivalent semantic predicate.
            let domain =
                self.compile_function_raw_expression_bound(&domain, position, &HashMap::new())?;
            let ty = format!("Litex.CurlDefinitionValue M {f} {domain} {point} {value}");
            let term=format!("(by\n{view}\n  exact (congrArg (fun D => Litex.CurlDefinitionValue M {f} D {point} {value}) {equal}.symm).mp ({}).2\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(&r.function, &r.point, target)?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let term = format!(
            "(by obtain ⟨v,hv,hc⟩ := Litex.curlExistsOfCandidate {} {}; exact ⟨v,hv,hc⟩)",
            values.join(" "),
            compiled.1
        );
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }

    pub(super) fn compile_curl_definition(
        &self,
        r: &CurlAtRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::CurlAtRelationDefinitionProof,
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
            .with_visible_membership(
                &r.value,
                &super::compile_multivariable_scalar_limit::vector_set(
                    &crate::execute::execute_fact_stmt::multivariable::helper::number(3),
                ),
                &mut |p, at| self.compile_verify(p, at).map(|v| v.1),
            )?
            .ok_or_else(|| invalid("DefinitionValueMembership"))?;
        let (view, equal) =
            self.compile_multivariable_limit_view(&r.function, &proof.function_domain, position)?;
        let values = [&r.function, &r.point, &r.value]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let [f, point, value] = values.as_slice() else {
            unreachable!()
        };
        Ok(format!("(by\n{view}\n  have _curl_clause : {ty} := {term}\n  exact ⟨{member},(congrArg (fun D => Litex.CurlDefinitionValue M {f} D {point} {value}) {equal}).mp _curl_clause⟩\n)"))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("CurlAt/{stage}"))
}

pub(super) fn validate_clauses(
    r: &CurlAtRelation,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    use crate::execute::execute_fact_stmt::multivariable::helper::{apply, number};
    let [Fact::ExistFact(e)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    let v = parameter(
        &e.typed_parameters,
        &super::compile_multivariable_scalar_limit::vector_set(&number(6)),
    )?;
    let v_obj = Obj::Identifier(IdentifierObj::from_bound_name(v));
    if e.facts.len() != 9
        || [&r.function, &r.point, &r.value, domain]
            .iter()
            .any(|o| contains_parameter(o, v.id))
    {
        return Err(invalid("DefinitionBody"));
    }
    for (slot, (component, axis)) in [(3, 2), (2, 3), (1, 3), (3, 1), (2, 1), (1, 2)]
        .into_iter()
        .enumerate()
    {
        let QuantifierFreeFact::AtomicFact(a) = &e.facts[slot] else {
            return Err(invalid("DefinitionPartial"));
        };
        let (p, negative) = super::compile_partial_derivative::parts(a)
            .ok_or_else(|| invalid("DefinitionPartialKind"))?;
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &p.function else {
            return Err(invalid("DefinitionComponent"));
        };
        let [input] = f.body.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("DefinitionComponentParameters"));
        };
        if input.params.len() != 1
            || input.param_type.ir() != domain.ir()
            || !f.body.dom_facts.is_empty()
            || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
        {
            return Err(invalid("DefinitionComponentDomain"));
        }
        let x = &input.params[0];
        if x.id == v.id
            || [&r.function, &r.point, &r.value, domain]
                .iter()
                .any(|o| contains_parameter(o, x.id))
        {
            return Err(invalid("DefinitionCapture"));
        }
        let body = apply(
            &apply(
                &r.function,
                vec![Obj::Identifier(IdentifierObj::from_bound_name(x))],
            ),
            vec![number(component)],
        );
        if negative
            || f.equal_to.ir() != body.ir()
            || p.point.ir() != r.point.ir()
            || p.dimension.ir() != number(3).ir()
            || p.coordinate.ir() != number(axis).ir()
            || p.value.ir() != apply(&v_obj, vec![number((slot + 1) as i64)]).ir()
        {
            return Err(invalid("DefinitionSubject"));
        }
    }
    for (slot, (axis, left, right)) in [(1, 1, 2), (2, 3, 4), (3, 5, 6)].into_iter().enumerate() {
        let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &e.facts[slot + 6] else {
            return Err(invalid("DefinitionComponentValue"));
        };
        let difference = crate::rational_expression::helper::sub_objs(
            apply(&v_obj, vec![number(left)]),
            apply(&v_obj, vec![number(right)]),
        );
        if eq.left.ir() != apply(&r.value, vec![number(axis)]).ir()
            || eq.right.ir() != difference.ir()
        {
            return Err(invalid("DefinitionOrientation"));
        }
    }
    Ok(())
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&CurlAtRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::CurlAt(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::CurlAt(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn existence(f: &Obj, p: &Obj, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(
        &e.typed_parameters,
        &super::compile_multivariable_scalar_limit::vector_set(
            &crate::execute::execute_fact_stmt::multivariable::helper::number(3),
        ),
    )?;
    if [f, p].iter().any(|o| contains_parameter(o, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(a)] if parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir()))
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
