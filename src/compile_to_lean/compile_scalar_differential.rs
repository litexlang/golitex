//! Scalar differentials: replay the interior and punctured remainder definition.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::execute::execute_fact_stmt::multivariable::selector::{
    MultivariableSelectorSelectionProof, ScalarDifferentialAtWellDefinedProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainRequirementProof, PredicateDomainWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ScalarDifferentialAt/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&ScalarDifferentialAtRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::ScalarDifferentialAt(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::ScalarDifferentialAt(p) = &f.relation {
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
    let v = parameter(&e.typed_parameters, &matrix_set(n))?;
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
    pub(super) fn compile_scalar_differential_wd(
        &self,
        object: &ScalarDifferentialAt,
        proof: &ScalarDifferentialAtWellDefinedProof,
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
        let mut lines = self.compile_scalar_differential_domain(
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
                format!("(Litex.scalarDifferentialExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) {value} {term})")
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
            "exact ⟨h_{},_multivariable_real,h_{},_scalar_differential_point_domain,{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[3].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.scalarDifferentialRepresentation (M := M)) (Litex.ScalarDifferentialObj.mk _multivariable_arg_0 _multivariable_arg_1 _multivariable_arg_2) (by\n  {}\n))",
            binders.join("; "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_scalar_differential_equality(
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
            (s @ Obj::DerivativeOperator(DerivativeOperator::ScalarDifferential(o)), v) => {
                (s, v, o, false)
            }
            (v, s @ Obj::DerivativeOperator(DerivativeOperator::ScalarDifferential(o))) => {
                (s, v, o, true)
            }
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
        let term =
            format!("((Litex.scalarDifferentialEqCandidate {selected} {raw} {h}).trans {eq})");
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

pub(super) fn matrix_set(n: &Obj) -> Obj {
    super::compile_jacobian::matrix_set(
        &crate::execute::execute_fact_stmt::multivariable::helper::number(1),
        n,
    )
}

impl LitexToLeanCompiler {
    pub(super) fn compile_scalar_differential_domain(
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
        if requirements.len() != 5 + usize::from(value.is_some()) {
            return Err(invalid("DomainStages"));
        }
        let args = 3 + usize::from(value.is_some());
        let mut lines = self.compile_multivariable_limit_domain(
            f,
            p,
            n,
            None,
            None,
            source,
            &requirements[..4],
            args,
            position,
        )?;
        for (i, r) in requirements.iter().enumerate().skip(4) {
            let valid = match (i, &r.requirement) {
                (4, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    q.element.ir() == p.ir() && q.set.ir() == domain.ir()
                }
                (5, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    value.is_some_and(|v| q.element.ir() == v.ir())
                        && q.set.ir() == matrix_set(n).ir()
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
        lines.push(format!("have _scalar_differential_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := (_multivariable_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _multivariable_signature.domain_isSet _multivariable_member).symm) ▸ h_{}",requirements[4].requirement.fact_id().value()));
        Ok(lines)
    }
}

pub(super) fn validate_differential_clauses(
    function: &Obj,
    point: &Obj,
    dimension: &Obj,
    output_dimension: Option<&Obj>,
    value: &Obj,
    domain: &Obj,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    use super::compile_multivariable_scalar_limit::{distance, vector_set};
    use crate::execute::execute_fact_stmt::multivariable::helper::{
        apply, identifier, norm, number,
    };
    let mut protected = vec![function, point, dimension, value, domain];
    protected.extend(output_dimension);
    let fresh = |p: &BoundName, prior: &[IdentifierId]| {
        if prior.contains(&p.id) || protected.iter().any(|o| contains_parameter(o, p.id)) {
            Err(invalid("DefinitionCapture"))
        } else {
            Ok(())
        }
    };
    fn strict(f: &QuantifierFreeFact) -> Result<(&Obj, &Obj), LeanCompileError> {
        let QuantifierFreeFact::AtomicFact(a) = f else {
            return Err(invalid("DefinitionOrder"));
        };
        let (a, b, strict) = source_order_oriented(a)?;
        if !strict {
            return Err(invalid("DefinitionStrictOrder"));
        }
        Ok((a, b))
    }
    let [Fact::ExistFact(interior), Fact::ForallFact(remainder)] = facts else {
        return Err(invalid("DefinitionClauses"));
    };
    let radius = parameter(
        &interior.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(radius, &[])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(ball_domain))] =
        interior.facts.as_slice()
    else {
        return Err(invalid("InteriorInclusion"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(ball)) = &ball_domain.left else {
        return Err(invalid("InteriorBall"));
    };
    if ball_domain.right.ir() != domain.ir() || ball.param_set.ir() != vector_set(dimension).ir() {
        return Err(invalid("InteriorDomain"));
    }
    fresh(&ball.param_binding, &[radius.id])?;
    let [bound] = ball.facts.as_slice() else {
        return Err(invalid("InteriorBounds"));
    };
    let (d, b) = strict(bound)?;
    distance(d, &identifier(&ball.param_binding), point, dimension)?;
    if b.ir() != identifier(radius).ir() {
        return Err(invalid("InteriorRadius"));
    }
    if !remainder.dom_facts.is_empty() {
        return Err(invalid("RemainderPremises"));
    }
    let eps = parameter(
        &remainder.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(eps, &[])?;
    let [ExistOrAndChainAtomicFact::ExistFact(exists)] = remainder.then_facts.as_slice() else {
        return Err(invalid("RemainderDelta"));
    };
    let delta = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(delta, &[eps.id])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("RemainderInclusion"));
    };
    let (Obj::SetFormer(SetFormer::SetBuilder(near)), Obj::SetFormer(SetFormer::SetBuilder(good))) =
        (&inclusion.left, &inclusion.right)
    else {
        return Err(invalid("RemainderSets"));
    };
    if near.param_set.ir() != domain.ir() || good.param_set.ir() != domain.ir() {
        return Err(invalid("RemainderDomain"));
    }
    fresh(&near.param_binding, &[eps.id, delta.id])?;
    fresh(&good.param_binding, &[eps.id, delta.id])?;
    let [lower, upper] = near.facts.as_slice() else {
        return Err(invalid("RemainderBounds"));
    };
    let (zero, d) = strict(lower)?;
    if zero.ir() != number(0).ir() {
        return Err(invalid("RemainderPuncture"));
    }
    distance(d, &identifier(&near.param_binding), point, dimension)?;
    let (d, b) = strict(upper)?;
    distance(d, &identifier(&near.param_binding), point, dimension)?;
    if b.ir() != identifier(delta).ir() {
        return Err(invalid("RemainderRadius"));
    }
    let [error] = good.facts.as_slice() else {
        return Err(invalid("RemainderError"));
    };
    let (error, bound) = strict(error)?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(bound)) = bound else {
        return Err(invalid("RemainderScaling"));
    };
    if bound.left.ir() != identifier(eps).ir() {
        return Err(invalid("RemainderEpsilon"));
    }
    let input = identifier(&good.param_binding);
    distance(&bound.right, &input, point, dimension)?;
    let (error, row, rows, at_input, at_point) = if let Some(m) = output_dimension {
        let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(e)) = error else {
            return Err(invalid("RemainderNorm"));
        };
        if e.dimension.ir() != m.ir() {
            return Err(invalid("RemainderOutputDimension"));
        }
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = e.vector.as_ref() else {
            return Err(invalid("RemainderCoordinates"));
        };
        LitexToLeanCompiler::validate_finite_seq_signature(
            &FiniteSeqSet {
                set: Box::new(Obj::StandardSet(StandardSet::R)),
                n: Box::new(m.clone()),
            },
            &body.body,
        )?;
        let row = &body.body.set_bound_parameters.groups[0].params[0];
        fresh(row, &[eps.id, delta.id, good.param_binding.id])?;
        let row = identifier(row);
        (
            body.equal_to.as_ref(),
            row.clone(),
            m.clone(),
            apply(&apply(function, vec![input.clone()]), vec![row.clone()]),
            apply(&apply(function, vec![point.clone()]), vec![row]),
        )
    } else {
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(error)) = error else {
            return Err(invalid("RemainderAbsolute"));
        };
        (
            error.arg.as_ref(),
            number(1),
            number(1),
            apply(function, vec![input.clone()]),
            apply(function, vec![point.clone()]),
        )
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(error)) = error else {
        return Err(invalid("RemainderSubtraction"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(change)) = error.left.as_ref() else {
        return Err(invalid("RemainderFunctionChange"));
    };
    if change.left.ir() != at_input.ir() || change.right.ir() != at_point.ir() {
        return Err(invalid("RemainderFunctionSubject"));
    }
    let Obj::FnObj(call) = error.right.as_ref() else {
        return Err(invalid("RemainderLinearCall"));
    };
    let FnObjHead::Object(linear) = call.head.as_ref() else {
        return Err(invalid("RemainderLinearHead"));
    };
    let Obj::MatrixOperator(MatrixOperator::Apply(linear)) = linear.as_ref() else {
        return Err(invalid("RemainderMatrixApply"));
    };
    if !matches!(call.body.as_slice(),[args] if matches!(args.as_slice(),[one] if one.ir()==row.ir()))
        || linear.matrix.ir() != value.ir()
        || linear.rows.ir() != rows.ir()
        || linear.cols.ir() != dimension.ir()
    {
        return Err(invalid("RemainderMatrixSubject"));
    }
    distance(
        &norm(*linear.vector.clone(), dimension.clone()),
        &input,
        point,
        dimension,
    )?;
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_scalar_differential_inferences(
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
            || p.derived.len() != if p.function_domain.is_some() { 3 } else { 1 }
        {
            return Err(invalid("InferenceIdentity"));
        }
        let facts = p
            .derived
            .iter()
            .map(|store| {
                let f = self.resolve_fact(store.primary_fact_id(), position)?;
                self.validate_store(&store.store, &f)?;
                Ok(f)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let mut lines = Vec::new();
        if let Some(domain) = &p.function_domain {
            let actual = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
                &domain.signature,
            )
            .ok_or_else(|| invalid("InferenceSignature"))?;
            validate_differential_clauses(
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
            let term=format!("(by\n{view}\n  obtain ⟨radius,hr,interior⟩ := ({}).2.1\n  refine ⟨radius,hr,?_⟩\n  intro input hi\n  obtain ⟨hv,_,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp hi\n  have hd : M.mem input _multivariable_source_domain := {equal}.symm ▸ interior input hv hclose\n  exact hd\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
            let ty = self.compile_function_raw_predicate(&facts[1], position, &HashMap::new())?;
            let term=format!("(by\n{view}\n  intro epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := ({}).2.2 epsilon h_epsilon\n  refine ⟨delta,hd,?_⟩\n  intro input h_input\n  obtain ⟨hi,_,hpos,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_input\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ({equal} ▸ hi) hpos hclose⟩\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[1], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(&r.function, &r.point, &r.dimension, target)?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let args = [&r.function, &r.point, &r.dimension, &r.value]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let term=format!("(by obtain ⟨v,hv,hc⟩ := Litex.scalarDifferentialExistsOfCandidate {args} {}; exact ⟨v,hv,hc⟩)",compiled.1);
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }
    pub(super) fn compile_scalar_differential_definition(
        &self,
        r: &ScalarDifferentialAtRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::ScalarDifferentialAtRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &proof.function_domain.signature,
        )
        .ok_or_else(|| invalid("DefinitionSignature"))?;
        validate_differential_clauses(
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
            lines.push(format!("  have _differential_clause_{i} : {ty} := {term}"));
        }
        let member = position
            .with_visible_membership(&r.value, &matrix_set(&r.dimension), &mut |p, at| {
                self.compile_verify(p, at).map(|v| v.1)
            })?
            .ok_or_else(|| invalid("DefinitionValueMembership"))?;
        lines.push(format!("  refine ⟨{member},?_,?_⟩\n  · obtain ⟨radius,hr,interior⟩ := _differential_clause_0\n    refine ⟨radius,hr,?_⟩\n    intro input hi hclose\n    exact {equal} ▸ interior input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hclose⟩)\n  · intro epsilon h_epsilon\n    obtain ⟨delta,hd,hcontrol⟩ := _differential_clause_1 (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n    refine ⟨delta,hd,?_⟩\n    intro input hi hpos hclose\n    have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n    have good := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hpos,hclose⟩)\n    exact ((Litex.SetSemantics.sep_members _ _ _).mp good).2.2"));
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}
