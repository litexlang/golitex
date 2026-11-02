//! Finite Euclidean scalar limits: replay original formation, WD and selection.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::selector::{
    MultivariableScalarLimitWellDefinedProof, MultivariableSelectorSelectionProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainRequirementProof, PredicateDomainWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MultivariableScalarLimit/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&ScalarMultivariableLimitRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::ScalarLimit(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::ScalarLimit(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
pub(super) fn vector_set(dimension: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
        set: Box::new(Obj::StandardSet(StandardSet::R)),
        n: Box::new(dimension.clone()),
    }))
}
pub(super) fn vector_carrier(obj: &Obj, n: &Obj) -> bool {
    match obj {
        Obj::SetFormer(SetFormer::FiniteSeqSet(s)) => {
            s.set.as_ref() == &Obj::StandardSet(StandardSet::R) && s.n.ir() == n.ir()
        }
        Obj::FunctionSpace(FunctionSpace::FnSet(s)) => {
            LitexToLeanCompiler::validate_finite_seq_signature(
                &FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::R)),
                    n: Box::new(n.clone()),
                },
                s,
            )
            .is_ok()
        }
        _ => false,
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
impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_limit_view(
        &self,
        f: &Obj,
        source: &CompleteFunctionDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("Signature"))?;
        let sig = self.compile_complete_domain_signature(source, position)?;
        let member = self.compile_complete_domain_member(f, source, position)?;
        self.compile_named_limit_domain_view(
            f,
            &domain,
            &source.signature,
            &sig,
            &member,
            "multivariable_",
            position,
        )
    }
    pub(super) fn compile_multivariable_limit_domain(
        &self,
        f: &Obj,
        p: &Obj,
        n: &Obj,
        m: Option<&Obj>,
        value: Option<&Obj>,
        source: &CompleteFunctionDomainProof,
        requirements: &[PredicateDomainWellDefinedProof],
        argument_count: usize,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let [group] = source.signature.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("Signature"));
        };
        if group.params.len() != 1
            || requirements.len() != 4 + usize::from(m.is_some()) + usize::from(value.is_some())
        {
            return Err(invalid("DomainStages"));
        }
        let input = group.param_type.as_ref();
        let output = source.signature.ret_set.as_ref();
        let mut input_equality = false;
        let mut output_equality = false;
        let output_index = 2 + usize::from(m.is_some());
        let point_index = output_index + 1;
        for (i, r) in requirements.iter().enumerate() {
            let valid = if i == 0 {
                matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(q)) if q.element.ir()==n.ir() && q.set==Obj::StandardSet(StandardSet::NPos))
            } else if i == 1 {
                match &r.requirement {
                    Fact::AtomicFact(AtomicFact::SubsetFact(q)) => {
                        q.left.ir() == input.ir() && vector_carrier(&q.right, n)
                    }
                    Fact::AtomicFact(AtomicFact::EqualFact(q)) => {
                        input_equality = true;
                        vector_carrier(input, n)
                            && vector_carrier(&q.left, n)
                            && vector_carrier(&q.right, n)
                    }
                    _ => false,
                }
            } else if m.is_some() && i == 2 {
                matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(q)) if q.element.ir()==m.unwrap().ir() && q.set==Obj::StandardSet(StandardSet::NPos))
            } else if i == output_index {
                match &r.requirement {
                    Fact::AtomicFact(AtomicFact::SubsetFact(q)) => {
                        q.left.ir() == output.ir()
                            && m.map_or(q.right == Obj::StandardSet(StandardSet::R), |m| {
                                vector_carrier(&q.right, m)
                            })
                    }
                    Fact::AtomicFact(AtomicFact::EqualFact(q)) => {
                        output_equality = true;
                        m.is_some_and(|m| {
                            vector_carrier(output, m)
                                && vector_carrier(&q.left, m)
                                && vector_carrier(&q.right, m)
                        })
                    }
                    _ => false,
                }
            } else if i == point_index {
                matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(q)) if q.element.ir()==p.ir()&&q.set.ir()==vector_set(n).ir())
            } else if i == point_index + 1 {
                matches!(&r.requirement,Fact::AtomicFact(AtomicFact::InFact(q)) if value.is_some_and(|v|q.element.ir()==v.ir())&&m.map_or(q.set==Obj::StandardSet(StandardSet::R),|m|q.set.ir()==vector_set(m).ir()))
            } else {
                false
            };
            if !valid {
                return Err(invalid("RequirementSubject"));
            }
        }
        let (view, _) = self.compile_multivariable_limit_view(f, source, position)?;
        let mut lines = vec![view
            .lines()
            .map(|line| line.strip_prefix("  ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n")];
        let args = argument_count;
        for (i, r) in requirements.iter().enumerate() {
            let prior = SourcePosition {
                before: args + i,
                ..*position
            };
            let PredicateDomainRequirementProof::Verified(proof) = &r.result else {
                return Err(invalid("RequirementCapture"));
            };
            if source_subject(proof)? != r.requirement {
                return Err(invalid("RequirementProof"));
            }
            let (ty, term) = self.compile_verify(proof, &prior)?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                r.requirement.fact_id().value()
            ));
        }
        let ft = self.compile_object_reference(f, position)?;
        let nt = self.compile_object_reference(n, position)?;
        let hi = requirements[1].requirement.fact_id().value();
        let ho = requirements[output_index].requirement.fact_id().value();
        let convert = if input_equality {
            format!("exact (congrArg (fun A => M.mem x A) h_{hi}).mp hx")
        } else {
            format!("exact h_{hi} x hx")
        };
        let base_member = if source.signature.dom_facts.is_empty() {
            "exact hx".to_owned()
        } else {
            "exact ((Litex.SetSemantics.sep_members _ _ _).mp hx).1".to_owned()
        };
        let base = self.compile_object_reference(input, position)?;
        let output_conversion = if output_equality {
            format!("exact (congrArg (fun A => M.mem y A) h_{ho}).mp hy")
        } else {
            format!("exact h_{ho} y hy")
        };
        let predicate = if let Some(m) = m {
            format!("Litex.VectorMultivariableFunctionValue M (Litex.denote {ft}) (Litex.denote {nt}) (Litex.denote {})",self.compile_object_reference(m,position)?)
        } else {
            format!(
                "Litex.RealMultivariableFunctionValue M (Litex.denote {ft}) (Litex.denote {nt})"
            )
        };
        lines.push(format!("have _multivariable_real : {predicate} := by\n  refine ⟨_multivariable_signature,_multivariable_member,?_,?_⟩\n  · intro x hx\n    have hx : M.mem x _multivariable_source_domain := _multivariable_domain_match ▸ hx\n    have hx : M.mem x (Litex.denote {base}) := by\n      {base_member}\n    {convert}\n  · intro y hy\n    {output_conversion}"));
        Ok(lines)
    }
    pub(super) fn compile_multivariable_scalar_wd(
        &self,
        object: &MultivariableScalarLimit,
        proof: &MultivariableScalarLimitWellDefinedProof,
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
        for (i, (arg, child)) in args.iter().zip(&stages.argument_well_defined).enumerate() {
            ensure_object(arg, child)?;
            binders.push(format!(
                "let _multivariable_arg_{i} := {}",
                self.compile_wd(
                    child,
                    &SourcePosition {
                        before: i,
                        ..*position
                    }
                )?
            ));
        }
        let mut lines = self.compile_multivariable_limit_domain(
            args[0],
            args[1],
            args[2],
            None,
            None,
            &stages.function_domain,
            &stages.domains,
            3,
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
                format!("(Litex.multivariableScalarExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], args[2], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by obtain ⟨v,hv,hc⟩ := (show {ty} from {term}); exact ⟨v,hv,hc⟩)")
            }
        };
        lines.push(format!(
            "exact ⟨h_{},_multivariable_real,h_{},{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[3].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.multivariableScalarLimitRepresentation (M := M)) (Litex.MultivariableScalarLimitObj.mk _multivariable_arg_0 _multivariable_arg_1 _multivariable_arg_2) (by\n  {}\n))",
            binders.join("; "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_multivariable_scalar_equality(
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
            (s @ Obj::LimitOperator(LimitOperator::MultivariableScalar(o)), v) => (s, v, o, false),
            (v, s @ Obj::LimitOperator(LimitOperator::MultivariableScalar(o))) => (s, v, o, true),
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
        let term = format!(
            "((Litex.multivariableScalarLimitEqCandidate {selected} {raw} {h}).trans {eq})"
        );
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

fn ident(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn fresh(p: &BoundName, objects: &[&Obj], prior: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if prior.contains(&p.id) || objects.iter().any(|o| contains_parameter(o, p.id)) {
        Err(invalid("DefinitionCapture"))
    } else {
        Ok(())
    }
}
pub(super) fn distance(object: &Obj, a: &Obj, b: &Obj, n: &Obj) -> Result<(), LeanCompileError> {
    let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(e)) = object else {
        return Err(invalid("DistanceNorm"));
    };
    if e.dimension.ir() != n.ir() {
        return Err(invalid("DistanceDimension"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = e.vector.as_ref() else {
        return Err(invalid("DistanceVector"));
    };
    LitexToLeanCompiler::validate_finite_seq_signature(
        &FiniteSeqSet {
            set: Box::new(Obj::StandardSet(StandardSet::R)),
            n: Box::new(n.clone()),
        },
        &f.body,
    )?;
    let k = &f.body.set_bound_parameters.groups[0].params[0];
    fresh(k, &[a, b, n], &[])?;
    if !matches!(f.equal_to.as_ref(),Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) if crate::execute::execute_fact_stmt::function_domain::function_application(a,vec![Box::new(ident(k))]).is_ok_and(|call|call.ir()==s.left.ir())&&crate::execute::execute_fact_stmt::function_domain::function_application(b,vec![Box::new(ident(k))]).is_ok_and(|call|call.ir()==s.right.ir()))
    {
        return Err(invalid("DistanceCoordinates"));
    }
    Ok(())
}
fn order(fact: &QuantifierFreeFact) -> Result<(&Obj, &Obj), LeanCompileError> {
    let QuantifierFreeFact::AtomicFact(f) = fact else {
        return Err(invalid("DefinitionAtomicOrder"));
    };
    let (a, b, strict) = source_order_oriented(f)?;
    if !strict {
        return Err(invalid("DefinitionStrictOrder"));
    }
    Ok((a, b))
}
pub(super) fn validate_clauses(
    function: &Obj,
    point: &Obj,
    dimension: &Obj,
    output_dimension: Option<&Obj>,
    value: &Obj,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    let mut protected = vec![function, point, dimension, value, domain];
    protected.extend(output_dimension);
    let [Fact::ForallFact(acc), Fact::ForallFact(eps)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    for f in [acc, eps] {
        if !f.dom_facts.is_empty() || f.typed_parameters.groups.len() != 1 {
            return Err(invalid("DefinitionPremises"));
        }
    }
    let radius = parameter(&acc.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    fresh(radius, &protected, &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(witness)] = acc.then_facts.as_slice() else {
        return Err(invalid("AccumulationWitness"));
    };
    let x = parameter(&witness.typed_parameters, domain)?;
    fresh(x, &protected, &[radius.id])?;
    let [lower, upper] = witness.facts.as_slice() else {
        return Err(invalid("AccumulationBounds"));
    };
    let (z, d) = order(lower)?;
    if !matches!(z,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0") {
        return Err(invalid("AccumulationPuncture"));
    }
    distance(d, &ident(x), point, dimension)?;
    let (d, b) = order(upper)?;
    distance(d, &ident(x), point, dimension)?;
    if b.ir() != ident(radius).ir() {
        return Err(invalid("AccumulationRadius"));
    }
    let epsilon = parameter(&eps.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
    fresh(epsilon, &protected, &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = eps.then_facts.as_slice() else {
        return Err(invalid("DeltaWitness"));
    };
    let delta = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(delta, &protected, &[epsilon.id])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("EpsilonInclusion"));
    };
    let (Obj::SetFormer(SetFormer::SetBuilder(near)), Obj::SetFormer(SetFormer::SetBuilder(good))) =
        (&inclusion.left, &inclusion.right)
    else {
        return Err(invalid("EpsilonSets"));
    };
    if near.param_set.ir() != domain.ir() || good.param_set.ir() != domain.ir() {
        return Err(invalid("EpsilonDomain"));
    }
    fresh(&near.param_binding, &protected, &[epsilon.id, delta.id])?;
    fresh(&good.param_binding, &protected, &[epsilon.id, delta.id])?;
    let [lower, upper] = near.facts.as_slice() else {
        return Err(invalid("EpsilonBounds"));
    };
    let (z, d) = order(lower)?;
    if !matches!(z,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0") {
        return Err(invalid("EpsilonPuncture"));
    }
    distance(d, &ident(&near.param_binding), point, dimension)?;
    let (d, b) = order(upper)?;
    distance(d, &ident(&near.param_binding), point, dimension)?;
    if b.ir() != ident(delta).ir() {
        return Err(invalid("EpsilonRadius"));
    }
    let [error] = good.facts.as_slice() else {
        return Err(invalid("EpsilonError"));
    };
    let (a, b) = order(error)?;
    if b.ir() != ident(epsilon).ir() {
        return Err(invalid("EpsilonTarget"));
    }
    if let Some(m) = output_dimension {
        let call = Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::from_obj(function.clone())),
            body: vec![vec![Box::new(ident(&good.param_binding))]],
        });
        distance(a, &call, value, m)?;
    } else if !matches!(a,Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) if matches!(a.arg.as_ref(),Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) if super::compile_sequence_analysis::call_matches(&s.left,function,&ident(&good.param_binding))&&s.right.ir()==value.ir()))
    {
        return Err(invalid("EpsilonFormula"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_scalar_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (InferAtomicFactResult::MultivariableAnalysisFact(rules), Fact::AtomicFact(atomic)) =
            (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let (r, negative) = parts(atomic).ok_or_else(|| invalid("InferencePredicate"))?;
        if negative {
            return Err(invalid("NegativeInference"));
        }
        let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        if p.source_fact_id != seed.fact_id()
            || p.derived.len() != if p.function_domain.is_some() { 3 } else { 1 }
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
        let f =
            self.compile_function_raw_expression_bound(&r.function, position, &HashMap::new())?;
        let pt = self.compile_function_raw_expression_bound(&r.point, position, &HashMap::new())?;
        let n =
            self.compile_function_raw_expression_bound(&r.dimension, position, &HashMap::new())?;
        let v = self.compile_function_raw_expression_bound(&r.value, position, &HashMap::new())?;
        let mut lines = Vec::new();
        if let Some(domain) = &p.function_domain {
            let actual = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
                &domain.signature,
            )
            .ok_or_else(|| invalid("InferenceSignature"))?;
            validate_clauses(
                &r.function,
                &r.point,
                &r.dimension,
                None,
                &r.value,
                &actual,
                &facts[..2],
            )?;
            let (view, equal) =
                self.compile_multivariable_limit_view(&r.function, domain, position)?;
            let ty = self.compile_function_raw_predicate(&facts[0], position, &HashMap::new())?;
            let term=format!("(by\n{view}\n  obtain ⟨r,hr,ha,he⟩ := {}\n  intro radius h_radius\n  obtain ⟨input,hi,hpos,hclose⟩ := ha radius h_radius\n  rw [← {equal}] at hi\n  exact ⟨input,hi,hpos,hclose⟩\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
            let ty = self.compile_function_raw_predicate(&facts[1], position, &HashMap::new())?;
            let term=format!("(by\n{view}\n  obtain ⟨r,hr,ha,he⟩ := {}\n  intro epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := he epsilon h_epsilon\n  refine ⟨delta,hd,?_⟩\n  intro input h_input\n  obtain ⟨hi,_,hpos,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_input\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ({equal} ▸ hi) hpos hclose⟩\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[1], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(&r.function, &r.point, &r.dimension, target)?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let term=format!("(by\n  obtain ⟨value,hv,hc⟩ := Litex.multivariableScalarExistsOfCandidate {f} {pt} {n} {v} {}\n  exact ⟨value,hv,hc⟩\n)",compiled.1);
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_scalar_definition(
        &self,
        r: &ScalarMultivariableLimitRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::ScalarMultivariableLimitRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &proof.function_domain.signature,
        )
        .ok_or_else(|| invalid("DefinitionSignature"))?;
        validate_clauses(
            &r.function,
            &r.point,
            &r.dimension,
            None,
            &r.value,
            &domain,
            &proof.requirement_facts,
        )?;
        if proof.proof_of_requirement_facts.len() != 2 {
            return Err(invalid("DefinitionProofCount"));
        }
        let (view, equal) =
            self.compile_multivariable_limit_view(&r.function, &proof.function_domain, position)?;
        let mut lines = vec![view];
        for (i, (fact, child)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if source_subject(child)? != *fact {
                return Err(invalid("DefinitionProofSubject"));
            }
            let (ty, term) = self.compile_verify(child, &position.atomic_search_prior(i)?)?;
            lines.push(format!("  have _multivariable_clause_{i} : {ty} := {term}"));
        }
        let value = self.compile_object_reference(&r.value, position)?;
        let real = self.compile_real_membership_certificate(&r.value, position)?;
        lines.push(format!("  have _multivariable_value_real : Litex.In {value} Litex.R := {real}\n  refine ⟨Litex.NativeBridge.asReal {value} _multivariable_value_real,Litex.NativeBridge.asReal_spec {value} _multivariable_value_real,?_,?_⟩\n  · intro radius h_radius\n    obtain ⟨input,hi,hpos,hclose⟩ := _multivariable_clause_0 (Litex.semanticObject radius (M.member_isSet h_radius)) h_radius\n    exact ⟨input,{equal} ▸ hi,hpos,hclose⟩\n  · intro epsilon h_epsilon\n    obtain ⟨delta,hd,hcontrol⟩ := _multivariable_clause_1 (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n    refine ⟨delta,hd,?_⟩\n    intro input hi hpos hclose\n    have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n    have _good := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hpos,hclose⟩)\n    exact ((Litex.SetSemantics.sep_members _ _ _).mp _good).2.2"));
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}
