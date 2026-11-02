//! Exact clause validation and replay of the Riemann definition's stored facts.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_riemann_integral::{
    endpoint_rewrites, invalid, is_enclosure, validate_domain_requirement, validate_existence,
};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply;
use crate::execute::execute_fact_stmt::riemann_integral::helper::{
    id, max, min, mul, num, sorted_interval, sub,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferFunctionRiemannIntegrableFactResult,
    InferHasRiemannIntegralFactResult,
};
use std::collections::HashMap;

pub(super) fn index_signature<'a>(
    signature: &'a FnSet,
    start: &Obj,
    end: &Obj,
) -> Result<&'a BoundName, LeanCompileError> {
    let [g] = signature.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("IndexSignature"));
    };
    let [k] = g.params.as_slice() else {
        return Err(invalid("IndexArity"));
    };
    if *g.param_type != Obj::StandardSet(StandardSet::Z)
        || *signature.ret_set != Obj::StandardSet(StandardSet::R)
        || contains_parameter(start, k.id)
        || contains_parameter(end, k.id)
    {
        return Err(invalid("IndexCarrier"));
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(lo)), QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(hi))] =
        signature.dom_facts.as_slice()
    else {
        return Err(invalid("IndexGuards"));
    };
    if lo.left.ir() != start.ir()
        || lo.right.ir() != id(k).ir()
        || hi.left.ir() != id(k).ir()
        || hi.right.ir() != end.ir()
    {
        return Err(invalid("IndexGuardBounds"));
    }
    Ok(k)
}
fn sum_matches(sum: &Obj, n: &Obj, p: &Obj, height: &Obj) -> Result<(), LeanCompileError> {
    let Obj::IteratedOperator(IteratedOperator::Sum(sum)) = sum else {
        return Err(invalid("DarbouxSum"));
    };
    if *sum.start != num("1") || sum.end.ir() != n.ir() {
        return Err(invalid("SumEndpoints"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
        return Err(invalid("SumFunction"));
    };
    let k = index_signature(&f.body, &num("1"), n)?;
    if [p, height].iter().any(|v| contains_parameter(v, k.id)) {
        return Err(invalid("SumCapture"));
    }
    let width = sub(
        analysis_apply(p.clone(), id(k)),
        analysis_apply(p.clone(), sub(id(k), num("1"))),
    );
    if f.equal_to.ir() != mul(analysis_apply(height.clone(), id(k)), width).ir() {
        return Err(invalid("SumBody"));
    }
    Ok(())
}
pub(super) fn validate_clauses(
    source: &HasRiemannIntegralFact,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    if facts.len() != 6 {
        return Err(invalid("DefinitionClauses"));
    }
    for (i, f) in facts[..3].iter().enumerate() {
        validate_domain_requirement(f, i, &source.lower, &source.upper, domain)?;
    }
    let interval = sorted_interval(source.lower.clone(), source.upper.clone());
    let Fact::AtomicFact(AtomicFact::RealSetBoundedFact(bounded)) = &facts[3] else {
        return Err(invalid("DefinitionBounded"));
    };
    let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &bounded.set else {
        return Err(invalid("BoundedRange"));
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(restricted)) = range.function.as_ref() else {
        return Err(invalid("RestrictedFunction"));
    };
    let [g] = restricted.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("RestrictedParameters"));
    };
    let [x] = g.params.as_slice() else {
        return Err(invalid("RestrictedArity"));
    };
    if bounded.boundedness != RealBoundedness::Both
        || g.param_type.ir() != interval.ir()
        || !restricted.body.dom_facts.is_empty()
        || *restricted.body.ret_set != Obj::StandardSet(StandardSet::R)
        || !call_matches(&restricted.equal_to, &source.function, &id(x))
        || [&source.function, &source.lower, &source.upper]
            .iter()
            .any(|o| contains_parameter(o, x.id))
    {
        return Err(invalid("BoundedRestriction"));
    }
    let Fact::OrFact(zero) = &facts[4] else {
        return Err(invalid("ZeroIntervalClause"));
    };
    if !matches!(zero.facts.as_slice(),[AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(ne)),AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
        if ne.left.ir()==source.lower.ir()&&ne.right.ir()==source.upper.ir()&&eq.left.ir()==source.value.ir()&&is_zero(&eq.right))
    {
        return Err(invalid("ZeroIntervalValue"));
    }
    let Fact::ForallFact(eps) = &facts[5] else {
        return Err(invalid("ApproximationForall"));
    };
    let e = parameter(&eps.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    let a = min(source.lower.clone(), source.upper.clone());
    let b = max(source.lower.clone(), source.upper.clone());
    if !matches!(eps.dom_facts.as_slice(),[Fact::AtomicFact(AtomicFact::LessFact(q))] if q.left.ir()==a.ir()&&q.right.ir()==b.ir())
    {
        return Err(invalid("ApproximationInterval"));
    }
    let [ExistOrAndChainAtomicFact::ExistFact(w)] = eps.then_facts.as_slice() else {
        return Err(invalid("ApproximationExistence"));
    };
    if w.typed_parameters.groups.len() != 6 {
        return Err(invalid("ApproximationWitnesses"));
    }
    let mut names = Vec::new();
    let mut sets = Vec::new();
    for g in &w.typed_parameters.groups {
        let [name] = g.params.as_slice() else {
            return Err(invalid("WitnessArity"));
        };
        let ParamType::Obj(set) = &g.param_type else {
            return Err(invalid("WitnessCarrier"));
        };
        if name.id == e.id
            || names.iter().any(|p: &&BoundName| p.id == name.id)
            || [
                &source.function,
                &source.lower,
                &source.upper,
                &source.value,
                domain,
            ]
            .iter()
            .any(|o| contains_parameter(o, name.id))
        {
            return Err(invalid("WitnessCapture"));
        }
        names.push(name);
        sets.push(set);
    }
    if [
        &source.function,
        &source.lower,
        &source.upper,
        &source.value,
        domain,
    ]
    .iter()
    .any(|o| contains_parameter(o, e.id))
    {
        return Err(invalid("EpsilonCapture"));
    }
    if sets[0] != &Obj::StandardSet(StandardSet::NPos)
        || sets[4] != &Obj::StandardSet(StandardSet::R)
        || sets[5] != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("WitnessNumericalCarriers"));
    }
    let n = id(names[0]);
    let p = id(names[1]);
    let lower = id(names[2]);
    let upper = id(names[3]);
    for (i, start) in [(1, "0"), (2, "1"), (3, "1")] {
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = sets[i] else {
            return Err(invalid("WitnessFunctionCarrier"));
        };
        index_signature(signature, &num(start), &n)?;
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(enclosure)), QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(ls)), QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(us)), QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(lo)), QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(hi)), QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(gap))] =
        w.facts.as_slice()
    else {
        return Err(invalid("ApproximationClauses"));
    };
    let expected = [&source.function, &a, &b, &n, &p, &lower, &upper];
    if !is_enclosure(&enclosure.predicate)
        || enclosure.body.len() != 7
        || !enclosure
            .body
            .iter()
            .zip(expected)
            .all(|(x, y)| x.ir() == y.ir())
    {
        return Err(invalid("ApproximationEnclosure"));
    }
    if ls.left.ir() != id(names[4]).ir() || us.left.ir() != id(names[5]).ir() {
        return Err(invalid("SumWitnessEquations"));
    }
    sum_matches(&ls.right, &n, &p, &lower)?;
    sum_matches(&us.right, &n, &p, &upper)?;
    let sign = Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
        arg: Box::new(sub(source.upper.clone(), source.lower.clone())),
    }));
    let oriented = mul(sign, source.value.clone());
    if lo.left.ir() != id(names[4]).ir()
        || lo.right.ir() != oriented.ir()
        || hi.left.ir() != oriented.ir()
        || hi.right.ir() != id(names[5]).ir()
        || gap.left.ir() != sub(id(names[5]), id(names[4])).ir()
        || gap.right.ir() != id(e).ir()
    {
        return Err(invalid("ApproximationBracket"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_riemann_definition(
        &self,
        source: &HasRiemannIntegralFact,
        wd: &AtomicFactWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinHasRiemannIntegralDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
        let PredicateDomainProof::FunctionAnalysis(formation) = &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("DefinitionFormation"));
        };
        if formation.function_domain.domain.ir() != proof.function_domain.domain.ir()
            || formation.requirements.len() != 4
            || proof.proof_of_requirement_facts.len() != 6
        {
            return Err(invalid("DefinitionDomainStages"));
        }
        validate_clauses(
            source,
            &proof.function_domain.domain,
            &proof.requirement_facts,
        )?;
        let real =
            self.compile_real_function_domain(&source.function, &proof.function_domain, position)?;
        let mut lines = vec![format!("have _integral_definition_real := {real}")];
        let mut names = Vec::new();
        for (i, (fact, checked)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("DefinitionProofSubject"));
            }
            let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(i)?)?;
            let name = format!("h_{}", fact.fact_id().value());
            lines.push(format!("have {name} : {ty} := {term}"));
            names.push(name);
        }
        let formed = position.atomic_search_prior(6)?;
        let (view, equal) = self.compile_function_limit_domain_view(
            &source.function,
            &proof.function_domain,
            &formed,
        )?;
        let reductions =
            self.compile_riemann_endpoint_reductions(&source.lower, &source.upper, &formed)?;
        let mut clauses = names.clone();
        for index in [2, 3, 5] {
            let mut steps = Vec::new();
            if index == 2 {
                steps.push(format!("have _integral_domain_eq := {equal}"));
                steps.push("rw [← _integral_domain_eq]".into());
            }
            if let Some((proofs, names)) = &reductions {
                steps.push(proofs.clone());
                if index == 2 {
                    steps.push("unfold Litex.riemannIntervalValue".into());
                } else if index == 3 {
                    steps.push(
                        "unfold Litex.riemannRestrictedRangeValue Litex.riemannIntervalValue"
                            .into(),
                    );
                }
                steps.push(endpoint_rewrites(names, "").replace("\n  ", "\n"));
            }
            if index == 5 {
                // The source forall accepts an Obj in any representation; the
                // semantic definition quantifies over M.Value. Its membership
                // supplies exactly the sethood needed to wrap that same value.
                steps.push("intro _epsilon _epsilon_member _interval_order".into());
                steps.push(format!(
                    "exact {} (Litex.semanticObject (M := M) _epsilon (M.member_isSet _epsilon_member)) _epsilon_member _interval_order",
                    names[index],
                ));
            } else {
                steps.push(format!("exact {}", names[index]));
            }
            clauses[index] = format!("(by\n  {}\n)", steps.join("\n").replace('\n', "\n  "));
        }
        let value_real = formation.requirements[3].requirement.fact_id().value();
        lines.push(format!("exact ⟨h_{value_real}, {}⟩", clauses.join(", ")));
        Ok(format!(
            "(by\n{view}\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    pub(super) fn compile_riemann_integrability_definition(
        &self,
        source: &FunctionRiemannIntegrableFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionRiemannIntegrableDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([fact], [checked]) = (
            proof.requirement_facts.as_slice(),
            proof.proof_of_requirement_facts.as_slice(),
        ) else {
            return Err(invalid("IntegrabilityDefinitionStages"));
        };
        validate_existence(&source.function, &source.lower, &source.upper, fact)?;
        if source_subject(checked)? != *fact {
            return Err(invalid("IntegrabilityDefinitionProof"));
        }
        self.compile_verify(checked, &position.atomic_search_prior(0)?)
            .map(|(_, term)| term)
    }

    pub(super) fn compile_riemann_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::HasRiemannIntegralFact(rules),
            Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let [InferHasRiemannIntegralFactResult::Definition(proof)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        if proof.source_fact_id != seed.fact_id()
            || proof.derived.len()
                != if proof.function_domain.is_some() {
                    8
                } else {
                    2
                }
        {
            return Err(invalid("InferenceIdentity"));
        }
        let facts = proof
            .derived
            .iter()
            .map(|s| {
                let f = self.resolve_fact(s.primary_fact_id(), position)?;
                self.validate_store(&s.store, &f)?;
                Ok(f)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let mut lines = Vec::new();
        if let Some(domain) = &proof.function_domain {
            validate_clauses(source, &domain.domain, &facts[..6])?;
            let (view, equal) =
                self.compile_function_limit_domain_view(&source.function, domain, position)?;
            let reductions =
                self.compile_riemann_endpoint_reductions(&source.lower, &source.upper, position)?;
            for (i, fact) in facts[..6].iter().enumerate() {
                let ty = if i == 3 {
                    let Fact::AtomicFact(AtomicFact::RealSetBoundedFact(b)) = fact else {
                        unreachable!()
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnRange(r)) = &b.set else {
                        unreachable!()
                    };
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = r.function.as_ref()
                    else {
                        unreachable!()
                    };
                    let graph =
                        self.compile_function_literal_value(f, position, &HashMap::new())?;
                    format!("Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue {graph})")
                } else {
                    self.compile_function_raw_predicate(fact, position, &HashMap::new())?
                };
                let projection = format!(
                    "({}).{}",
                    compiled.1,
                    match i {
                        0 => "2.1",
                        1 => "2.2.1",
                        2 => "2.2.2.1",
                        3 => "2.2.2.2.1",
                        4 => "2.2.2.2.2.1",
                        _ => "2.2.2.2.2.2",
                    }
                );
                let term = if i == 2 {
                    let normalization = reductions.as_ref().map(|(proofs, names)| {
                        format!("\n  {}\n  unfold Litex.riemannIntervalValue at _integral_clause\n  {}",
                            proofs.replace('\n', "\n  "),
                            endpoint_rewrites(names, " at _integral_clause"))
                    }).unwrap_or_default();
                    format!("(by\n{view}\n  have _integral_domain_eq := {equal}\n  have _integral_clause := {projection}\n  rw [← _integral_domain_eq] at _integral_clause{normalization}\n  exact _integral_clause\n)")
                } else if (i == 3 || i == 5) && reductions.is_some() {
                    let (proofs, names) = reductions.as_ref().unwrap();
                    let reductions = proofs.replace('\n', "\n  ");
                    let rewrites = endpoint_rewrites(names, " at _integral_clause");
                    let unfold = if i == 3 {
                        "\n  unfold Litex.riemannRestrictedRangeValue Litex.riemannIntervalValue at _integral_clause"
                    } else {
                        ""
                    };
                    format!("(by\n  {reductions}\n  have _integral_clause := {projection}{unfold}\n  {rewrites}\n  exact _integral_clause\n)")
                } else {
                    projection
                };
                lines.push(self.emit_internal_fact(fact, &(ty, term), position)?);
            }
        }
        let tail = &facts[facts.len() - 2..];
        validate_existence(&source.function, &source.lower, &source.upper, &tail[0])?;
        if !matches!(&tail[1],Fact::AtomicFact(AtomicFact::FunctionRiemannIntegrableFact(f)) if f.function.ir()==source.function.ir()&&f.lower.ir()==source.lower.ir()&&f.upper.ir()==source.upper.ir())
        {
            return Err(invalid("InferredIntegrability"));
        }
        let args = [
            &source.function,
            &source.lower,
            &source.upper,
            &source.value,
        ]
        .into_iter()
        .map(|x| self.compile_function_raw_expression_bound(x, position, &HashMap::new()))
        .collect::<Result<Vec<_>, _>>()?;
        let term = format!(
            "(Litex.riemannIntegralExistsOfCandidate {} {})",
            args.join(" "),
            compiled.1
        );
        for fact in tail {
            let ty = self.compile_function_raw_predicate(fact, position, &HashMap::new())?;
            lines.push(self.emit_internal_fact(fact, &(ty, term.clone()), position)?);
        }
        Ok(lines)
    }
    pub(super) fn compile_riemann_integrability_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::FunctionRiemannIntegrableFact(rules),
            Fact::AtomicFact(AtomicFact::FunctionRiemannIntegrableFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("IntegrabilityInference"));
        };
        let [InferFunctionRiemannIntegrableFactResult::Definition(p)] = rules.as_slice() else {
            return Err(invalid("IntegrabilityRule"));
        };
        let [stored] = p.derived.as_slice() else {
            return Err(invalid("IntegrabilityStores"));
        };
        if p.source_fact_id != seed.fact_id() {
            return Err(invalid("IntegrabilitySource"));
        }
        let fact = self.resolve_fact(stored.primary_fact_id(), position)?;
        self.validate_store(&stored.store, &fact)?;
        validate_existence(&source.function, &source.lower, &source.upper, &fact)?;
        let ty = self.compile_function_raw_predicate(&fact, position, &HashMap::new())?;
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(ty, compiled.1.clone()),
            position,
        )?])
    }
}
