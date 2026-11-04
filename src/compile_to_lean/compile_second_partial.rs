//! Second partials retain the original local first-derivative witness and domains.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
impl LitexToLeanCompiler {
    pub(super) fn compile_second_partial_domain(
        &self,
        f: &Obj,
        p: &Obj,
        n: &Obj,
        first: &Obj,
        second: &Obj,
        value: Option<&Obj>,
        source: &crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof,
        requirements: &[crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainRequirementProof;
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("Signature"))?;
        if requirements.len() != 7 + usize::from(value.is_some()) {
            return Err(invalid("DomainStages"));
        }
        let argument_count = 5 + usize::from(value.is_some());
        let mut lines = self.compile_multivariable_limit_domain(
            f,
            p,
            n,
            None,
            None,
            source,
            &requirements[..4],
            argument_count,
            position,
        )?;
        for (i, r) in requirements.iter().enumerate().skip(4) {
            let valid =
                match (i, &r.requirement) {
                    (4, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                        q.element.ir() == p.ir() && q.set.ir() == domain.ir()
                    }
                    (5, Fact::AtomicFact(AtomicFact::InFact(q))) => q.element.ir() == first.ir()
                        && q.set.ir()
                            == crate::execute::execute_fact_stmt::multivariable::helper::indices(
                                n.clone(),
                            )
                            .ir(),
                    (6, Fact::AtomicFact(AtomicFact::InFact(q))) => q.element.ir() == second.ir()
                        && q.set.ir()
                            == crate::execute::execute_fact_stmt::multivariable::helper::indices(
                                n.clone(),
                            )
                            .ir(),
                    (7, Fact::AtomicFact(AtomicFact::InFact(q))) => {
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
                    before: argument_count + i,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        let p = self.compile_object_reference(p, position)?;
        let f = self.compile_object_reference(f, position)?;
        lines.push(format!("have _partial_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := (_multivariable_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _multivariable_signature.domain_isSet _multivariable_member).symm) ▸ h_{}",requirements[4].requirement.fact_id().value()));
        Ok(lines)
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_second_partial_inferences(
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
        let values = [
            &r.function,
            &r.point,
            &r.dimension,
            &r.first_coordinate,
            &r.second_coordinate,
            &r.value,
        ]
        .into_iter()
        .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
        .collect::<Result<Vec<_>, _>>()?;
        let [f, point, n, first, second, value] = values.as_slice() else {
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
            // The local first-derivative witness belongs to the checked defining clause,
            // not new object constructors. Render its equivalent semantic predicate.
            let domain =
                self.compile_function_raw_expression_bound(&domain, position, &HashMap::new())?;
            let ty = format!("Litex.SecondPartialDefinitionValue M {f} {domain} {point} {n} {first} {second} {value}");
            let term=format!("(by\n{view}\n  exact (congrArg (fun D => Litex.SecondPartialDefinitionValue M {f} D {point} {n} {first} {second} {value}) {equal}.symm).mp ({})\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(r, target)?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let term = format!(
            "(by obtain ⟨v,hv,hc⟩ := Litex.secondPartialExistsOfCandidate {} {}; exact ⟨v,hv,hc⟩)",
            values.join(" "),
            compiled.1
        );
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }

    pub(super) fn compile_second_partial_definition(
        &self,
        r: &SecondPartialDerivativeAtRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::SecondPartialDerivativeAtRelationDefinitionProof,
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
        let (view, equal) =
            self.compile_multivariable_limit_view(&r.function, &proof.function_domain, position)?;
        let values = [
            &r.function,
            &r.point,
            &r.dimension,
            &r.first_coordinate,
            &r.second_coordinate,
            &r.value,
        ]
        .into_iter()
        .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
        .collect::<Result<Vec<_>, _>>()?;
        let [f, point, n, first, second, value] = values.as_slice() else {
            unreachable!()
        };
        Ok(format!("(by\n{view}\n  have _second_partial_clause : {ty} := {term}\n  exact (congrArg (fun D => Litex.SecondPartialDefinitionValue M {f} D {point} {n} {first} {second} {value}) {equal}).mp _second_partial_clause\n)"))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SecondPartialDerivativeAt/{stage}"))
}
pub(super) fn parts(a: &AtomicFact) -> Option<(&SecondPartialDerivativeAtRelation, bool)> {
    match a {
        AtomicFact::MultivariableAnalysisFact(q) => {
            if let MultivariableAnalysisRelation::SecondPartialDerivativeAt(r) = &q.relation {
                Some((r, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(q) => {
            if let MultivariableAnalysisRelation::SecondPartialDerivativeAt(r) = &q.relation {
                Some((r, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn arguments(r: &SecondPartialDerivativeAtRelation) -> [&Obj; 6] {
    [
        &r.function,
        &r.point,
        &r.dimension,
        &r.first_coordinate,
        &r.second_coordinate,
        &r.value,
    ]
}
fn existence(r: &SecondPartialDerivativeAtRelation, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if arguments(r)[..5]
        .iter()
        .any(|o| contains_parameter(o, v.id))
    {
        return Err(invalid("ExistenceCapture"));
    }
    let [QuantifierFreeFact::AtomicFact(a)] = e.facts.as_slice() else {
        return Err(invalid("ExistenceBody"));
    };
    let (p, negative) = parts(a).ok_or_else(|| invalid("ExistenceCandidate"))?;
    if negative
        || !arguments(r)[..5]
            .iter()
            .zip(&arguments(p)[..5])
            .all(|(x, y)| x.ir() == y.ir())
        || p.value.ir() != identifier(v).ir()
    {
        return Err(invalid("ExistenceSubject"));
    }
    Ok(())
}
fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
pub(super) fn validate_clauses(
    r: &SecondPartialDerivativeAtRelation,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    use crate::execute::execute_fact_stmt::multivariable::helper::apply;
    let [Fact::ExistFact(e)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    let [local, first] = e.typed_parameters.groups.as_slice() else {
        return Err(invalid("DefinitionBinders"));
    };
    let ([set_name], [function_name]) = (local.params.as_slice(), first.params.as_slice()) else {
        return Err(invalid("DefinitionParameters"));
    };
    let set = identifier(set_name);
    let function = identifier(function_name);
    if !matches!(&local.param_type,ParamType::Obj(Obj::SetOperator(SetOperator::PowerSet(p))) if p.set.ir()==super::compile_multivariable_scalar_limit::vector_set(&r.dimension).ir())
    {
        return Err(invalid("DefinitionLocalCarrier"));
    }
    let ParamType::Obj(Obj::FunctionSpace(FunctionSpace::FnSet(signature))) = &first.param_type
    else {
        return Err(invalid("DefinitionFirstFunction"));
    };
    let [input] = signature.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("DefinitionFirstParameters"));
    };
    if input.params.len() != 1
        || input.param_type.ir() != set.ir()
        || !signature.dom_facts.is_empty()
        || signature.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("DefinitionFirstDomain"));
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset)), QuantifierFreeFact::AtomicFact(AtomicFact::InFact(point)), QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(firsts)), QuantifierFreeFact::AtomicFact(last)] =
        e.facts.as_slice()
    else {
        return Err(invalid("DefinitionBody"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(good)) = &firsts.right else {
        return Err(invalid("DefinitionGoodPoints"));
    };
    let [QuantifierFreeFact::AtomicFact(partial)] = good.facts.as_slice() else {
        return Err(invalid("DefinitionPointwiseBody"));
    };
    let (p, negative) = super::compile_partial_derivative::parts(partial)
        .ok_or_else(|| invalid("DefinitionFirstPartial"))?;
    let (last, negative_last) = super::compile_partial_derivative::parts(last)
        .ok_or_else(|| invalid("DefinitionSecondPartial"))?;
    let q = identifier(&good.param_binding);
    if subset.left.ir() != set.ir()
        || subset.right.ir() != domain.ir()
        || point.element.ir() != r.point.ir()
        || point.set.ir() != set.ir()
        || firsts.left.ir() != set.ir()
        || good.param_set.ir() != set.ir()
    {
        return Err(invalid("DefinitionLocalDomain"));
    }
    let ids = [set_name.id, function_name.id, good.param_binding.id];
    if ids[0] == ids[1]
        || ids[0] == ids[2]
        || ids[1] == ids[2]
        || arguments(r)
            .iter()
            .chain([domain].iter())
            .any(|o| ids.iter().any(|id| contains_parameter(o, *id)))
    {
        return Err(invalid("DefinitionCapture"));
    }
    if negative
        || p.function.ir() != r.function.ir()
        || p.point.ir() != q.ir()
        || p.dimension.ir() != r.dimension.ir()
        || p.coordinate.ir() != r.first_coordinate.ir()
        || p.value.ir() != apply(&function, vec![q]).ir()
    {
        return Err(invalid("DefinitionFirstSubject"));
    }
    if negative_last
        || last.function.ir() != function.ir()
        || last.point.ir() != r.point.ir()
        || last.dimension.ir() != r.dimension.ir()
        || last.coordinate.ir() != r.second_coordinate.ir()
        || last.value.ir() != r.value.ir()
    {
        return Err(invalid("DefinitionSecondSubject"));
    }
    Ok(())
}
