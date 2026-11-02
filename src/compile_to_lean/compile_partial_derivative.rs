//! Coordinate partial derivatives with source interior and punctured quotient evidence.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::selector::{
    MultivariableSelectorSelectionProof, PartialDerivativeAtWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("PartialDerivativeAt/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&PartialDerivativeAtRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::PartialDerivativeAt(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::PartialDerivativeAt(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn existence(f: &Obj, p: &Obj, n: &Obj, m: &Obj, fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if [f, p, n, m].iter().any(|o| contains_parameter(o, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(a)] if parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.dimension.ir()==n.ir()&&r.coordinate.ir()==m.ir()&&r.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir()))
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_partial_derivative_wd(
        &self,
        object: &PartialDerivativeAt,
        proof: &PartialDerivativeAtWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [
            object.function.as_ref(),
            object.point.as_ref(),
            object.dimension.as_ref(),
            object.coordinate.as_ref(),
        ];
        let stages = &proof.stages;
        if stages.argument_well_defined.len() != 4 {
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
        let mut lines = self.compile_partial_derivative_domain(
            args[0],
            args[1],
            args[2],
            args[3],
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
                    || q.coordinate.ir() != args[3].ir()
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
                format!("(Litex.partialDerivativeExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) (Litex.denote _multivariable_arg_3) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], args[2], args[3], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by obtain ⟨v,hv,hc⟩ := (show {ty} from {term}); exact ⟨v,hv,hc⟩)")
            }
        };
        lines.push(format!(
            "exact ⟨h_{},_multivariable_real,h_{},_partial_point_domain,h_{},{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[3].requirement.fact_id().value(),
            stages.domains[5].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.partialDerivativeRepresentation (M := M)) (Litex.PartialDerivativeObj.mk _multivariable_arg_0 _multivariable_arg_1 _multivariable_arg_2 _multivariable_arg_3) (by\n  {}\n))",
            binders.join("; "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_partial_derivative_equality(
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
            (s @ Obj::DerivativeOperator(DerivativeOperator::Partial(o)), v) => (s, v, o, false),
            (v, s @ Obj::DerivativeOperator(DerivativeOperator::Partial(o))) => (s, v, o, true),
            _ => return Err(invalid("SelectedSubject")),
        };
        let (candidate, negative) =
            parts(&proof.candidate.fact).ok_or_else(|| invalid("EqualityCandidate"))?;
        if negative
            || candidate.function.ir() != obj.function.ir()
            || candidate.point.ir() != obj.point.ir()
            || candidate.dimension.ir() != obj.dimension.ir()
            || candidate.coordinate.ir() != obj.coordinate.ir()
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
            format!("((Litex.partialDerivativeEqCandidate {selected} {raw} {h}).trans {eq})");
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

fn index_set(n: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "1".into(),
        }))),
        end: Box::new(n.clone()),
    }))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_partial_derivative_domain(
        &self,
        f: &Obj,
        p: &Obj,
        n: &Obj,
        coordinate: &Obj,
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
        if requirements.len() != 6 + usize::from(value.is_some()) {
            return Err(invalid("DomainStages"));
        }
        let argument_count = 4 + usize::from(value.is_some());
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
            let valid = match (i, &r.requirement) {
                (4, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    q.element.ir() == p.ir() && q.set.ir() == domain.ir()
                }
                (5, Fact::AtomicFact(AtomicFact::InFact(q))) => {
                    q.element.ir() == coordinate.ir() && q.set.ir() == index_set(n).ir()
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
fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
fn call(function: &Obj, arguments: Vec<Obj>) -> Result<Obj, LeanCompileError> {
    crate::execute::execute_fact_stmt::function_domain::function_application(
        function,
        arguments.into_iter().map(Box::new).collect(),
    )
    .map_err(|_| invalid("CallShape"))
}
fn zero(obj: &Obj) -> bool {
    matches!(obj,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0")
}
fn fresh(p: &BoundName, objects: &[&Obj], prior: &[IdentifierId]) -> Result<(), LeanCompileError> {
    if prior.contains(&p.id) || objects.iter().any(|o| contains_parameter(o, p.id)) {
        Err(invalid("DefinitionCapture"))
    } else {
        Ok(())
    }
}
fn path(object: &Obj, point: &Obj, n: &Obj, axis: &Obj, h: &Obj) -> Result<(), LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = object else {
        return Err(invalid("CoordinatePath"));
    };
    LitexToLeanCompiler::validate_finite_seq_signature(
        &FiniteSeqSet {
            set: Box::new(Obj::StandardSet(StandardSet::R)),
            n: Box::new(n.clone()),
        },
        &f.body,
    )?;
    let k = &f.body.set_bound_parameters.groups[0].params[0];
    fresh(k, &[point, n, axis, h], &[])?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = f.equal_to.as_ref() else {
        return Err(invalid("CoordinateAdd"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(step)) = sum.right.as_ref() else {
        return Err(invalid("CoordinateStep"));
    };
    let identity = Obj::MatrixOperator(MatrixOperator::IdentityMatrix(IdentityMatrix {
        order: Box::new(n.clone()),
    }));
    if sum.left.ir() != call(point, vec![identifier(k)])?.ir()
        || step.left.ir() != h.ir()
        || step.right.ir() != call(&identity, vec![identifier(k), axis.clone()])?.ir()
    {
        return Err(invalid("CoordinateFormula"));
    }
    Ok(())
}
/// Validate the two actual source clauses before using their proved semantic bridge.
pub(super) fn clauses<'a>(
    r: &PartialDerivativeAtRelation,
    domain: &Obj,
    facts: &'a [Fact],
) -> Result<&'a Obj, LeanCompileError> {
    let [Fact::ExistFact(interior), Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(limit))] =
        facts
    else {
        return Err(invalid("DefinitionClauses"));
    };
    let protected = [
        &r.function,
        &r.point,
        &r.dimension,
        &r.coordinate,
        &r.value,
        domain,
    ];
    let radius = parameter(
        &interior.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    fresh(radius, &protected, &[])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        interior.facts.as_slice()
    else {
        return Err(invalid("InteriorInclusion"));
    };
    let (
        Obj::SetFormer(SetFormer::SetBuilder(near)),
        Obj::SetFormer(SetFormer::SetBuilder(section)),
    ) = (&inclusion.left, &inclusion.right)
    else {
        return Err(invalid("InteriorSets"));
    };
    if near.param_set.as_ref() != &Obj::StandardSet(StandardSet::R)
        || section.param_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("InteriorCarrier"));
    }
    fresh(&near.param_binding, &protected, &[radius.id])?;
    fresh(&section.param_binding, &protected, &[radius.id])?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(bound))] = near.facts.as_slice()
    else {
        return Err(invalid("InteriorBound"));
    };
    if !matches!(&bound.left,Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) if a.arg.ir()==identifier(&near.param_binding).ir())
        || bound.right.ir() != identifier(radius).ir()
    {
        return Err(invalid("InteriorRadius"));
    }
    let [QuantifierFreeFact::AtomicFact(AtomicFact::InFact(member))] = section.facts.as_slice()
    else {
        return Err(invalid("SectionMembership"));
    };
    if member.set.ir() != domain.ir() {
        return Err(invalid("SectionDomain"));
    }
    path(
        &member.element,
        &r.point,
        &r.dimension,
        &r.coordinate,
        &identifier(&section.param_binding),
    )?;
    if !matches!(&limit.approach,LimitApproach::AtPoint(p) if zero(p))
        || limit.value.ir() != r.value.ir()
    {
        return Err(invalid("QuotientLimit"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(quotient)) = &limit.function else {
        return Err(invalid("QuotientFunction"));
    };
    let [group] = quotient.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("QuotientSignature"));
    };
    if group.params.len() != 1
        || group.param_type.as_ref() != &Obj::StandardSet(StandardSet::R)
        || quotient.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(invalid("QuotientSignature"));
    }
    let h = &group.params[0];
    fresh(h, &protected, &[])?;
    let h_obj = identifier(h);
    let [not_zero, source_member] = quotient.body.dom_facts.as_slice() else {
        return Err(invalid("QuotientGuards"));
    };
    let not_zero = super::compile_function_template::function_guard_fact(not_zero)?;
    let source_member = super::compile_function_template::function_guard_fact(source_member)?;
    if !matches!(&not_zero,Fact::AtomicFact(AtomicFact::NotEqualFact(q)) if q.left.ir()==h_obj.ir()&&zero(&q.right))
    {
        return Err(invalid("QuotientNonzero"));
    }
    let Fact::AtomicFact(AtomicFact::InFact(member)) = source_member else {
        return Err(invalid("QuotientDomain"));
    };
    if member.set.ir() != domain.ir() {
        return Err(invalid("QuotientDomain"));
    }
    path(
        &member.element,
        &r.point,
        &r.dimension,
        &r.coordinate,
        &h_obj,
    )?;
    let Obj::ArithmeticOperator(ArithmeticOperator::Div(fraction)) = quotient.equal_to.as_ref()
    else {
        return Err(invalid("QuotientDivision"));
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(difference)) = fraction.left.as_ref()
    else {
        return Err(invalid("QuotientDifference"));
    };
    if fraction.right.ir() != h_obj.ir()
        || difference.left.ir() != call(&r.function, vec![member.element.clone()])?.ir()
        || difference.right.ir() != call(&r.function, vec![r.point.clone()])?.ir()
    {
        return Err(invalid("QuotientFormula"));
    }
    Ok(&limit.function)
}
impl LitexToLeanCompiler {
    // Predicate WD already certifies the point as a vector, including points
    // declared in a subset. Preserve its source value while rendering the
    // generated coordinate path; do not require its declared set to be a FnSet.
    pub(super) fn partial_raw_bindings(
        &self,
        r: &PartialDerivativeAtRelation,
        position: &SourcePosition<'_>,
    ) -> Result<HashMap<IdentifierId, String>, LeanCompileError> {
        let mut bindings = HashMap::new();
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &r.point {
            bindings.insert(
                *id,
                format!(
                    "(Litex.denote {})",
                    self.compile_object_reference(&r.point, position)?
                ),
            );
        }
        Ok(bindings)
    }
    fn partial_raw_arguments(
        &self,
        r: &PartialDerivativeAtRelation,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        [&r.function, &r.point, &r.dimension, &r.coordinate]
            .into_iter()
            .map(|o| {
                self.compile_function_raw_expression_bound(
                    o,
                    position,
                    &self.partial_raw_bindings(r, position)?,
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|v| v.join(" "))
    }
    pub(super) fn partial_quotient_match(
        &self,
        r: &PartialDerivativeAtRelation,
        quotient: &Obj,
        equal: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(quotient)) = quotient else {
            return Err(invalid("QuotientFunction"));
        };
        let q = self.compile_function_literal_value(
            quotient,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        let args = self.partial_raw_arguments(r, position)?;
        let function = self.compile_object_reference(&r.function, position)?;
        let bindings = self.partial_raw_bindings(r, position)?;
        let tail = [&r.point, &r.dimension, &r.coordinate]
            .into_iter()
            .map(|o| self.compile_function_raw_expression_bound(o, position, &bindings))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        // Only constructed function values need to expose the certified object
        // alias; identifiers already have exactly the native RHS syntax.
        let expose = if matches!(&r.function, Obj::Identifier(_)) {
            String::new()
        } else {
            format!("    change _ = Litex.partialQuotientValue (Litex.denote {function}) {tail}\n")
        };
        Ok(format!("  have _partial_quotient_match : {q} = Litex.partialQuotientValue {args} := by\n{expose}    unfold Litex.partialQuotientValue\n    rw [← {equal}]\n    rfl"))
    }
    pub(super) fn compile_partial_derivative_inferences(
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
                let fact = self.resolve_fact(store.primary_fact_id(), position)?;
                self.validate_store(&store.store, &fact)?;
                Ok(fact)
            })
            .collect::<Result<Vec<_>, LeanCompileError>>()?;
        let mut lines = Vec::new();
        if let Some(source) = &p.function_domain {
            let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
                &source.signature,
            )
            .ok_or_else(|| invalid("InferenceSignature"))?;
            let quotient = clauses(r, &domain, &facts[..2])?;
            let (view, equal) =
                self.compile_multivariable_limit_view(&r.function, source, position)?;
            let ty = self.compile_function_raw_predicate(
                &facts[0],
                position,
                &self.partial_raw_bindings(r, position)?,
            )?;
            let function = self.compile_object_reference(&r.function, position)?;
            let term=format!("(by\n{view}\n  obtain ⟨radius,hr,hcontrol⟩ := ({}).1\n  refine ⟨radius,hr,?_⟩\n  intro h h_near\n  obtain ⟨hR,_,hsmall⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_near\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  have h_member := hcontrol h hR hsmall\n  have h_member : M.mem _ (Litex.FunctionSemantics.domainValue (Litex.denote {function})) := h_member\n  rw [← {equal}] at h_member\n  exact ⟨hR,hR,h_member⟩\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(q)) = quotient else {
                return Err(invalid("QuotientFunction"));
            };
            let q = self.compile_function_literal_value(
                q,
                position,
                &self.partial_raw_bindings(r, position)?,
            )?;
            let value = self.compile_function_raw_expression_bound(
                &r.value,
                position,
                &self.partial_raw_bindings(r, position)?,
            )?;
            let ty = format!("Litex.HasFiniteFunctionLimitValue M .both {q} (M.number 0) {value}");
            let quotient_match = self.partial_quotient_match(r, quotient, &equal, position)?;
            let term = format!(
                "(by\n{view}\n{quotient_match}\n  rw [_partial_quotient_match]\n  exact ({}).2\n)",
                compiled.1
            );
            lines.push(self.emit_internal_fact(&facts[1], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(&r.function, &r.point, &r.dimension, &r.coordinate, target)?;
        let ty = self.compile_function_raw_predicate(
            target,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        let args = self.partial_raw_arguments(r, position)?;
        let value = self.compile_function_raw_expression_bound(
            &r.value,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        let term = format!(
            "(by obtain ⟨v,hv,hc⟩ := Litex.partialDerivativeExistsOfCandidate {args} {value} {}; exact ⟨v,hv,hc⟩)",
            compiled.1
        );
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }
    pub(super) fn compile_partial_derivative_definition(
        &self,
        r: &PartialDerivativeAtRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::PartialDerivativeAtRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &proof.function_domain.signature,
        )
        .ok_or_else(|| invalid("DefinitionSignature"))?;
        let quotient = clauses(r, &domain, &proof.requirement_facts)?;
        if proof.proof_of_requirement_facts.len() != 2 {
            return Err(invalid("DefinitionProofCount"));
        }
        let (view, equal) =
            self.compile_multivariable_limit_view(&r.function, &proof.function_domain, position)?;
        let mut lines = vec![
            view,
            self.partial_quotient_match(r, quotient, &equal, position)?,
        ];
        for (i, (fact, child)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            if source_subject(child)? != *fact {
                return Err(invalid("DefinitionProofSubject"));
            }
            let prior = position.atomic_search_prior(i)?;
            let (_, term) = self.compile_verify(child, &prior)?;
            let ty = if i == 0 {
                self.compile_function_raw_predicate(
                    fact,
                    &prior,
                    &self.partial_raw_bindings(r, &prior)?,
                )?
            } else {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(q)) = quotient else {
                    return Err(invalid("QuotientFunction"));
                };
                let q = self.compile_function_literal_value(
                    q,
                    &prior,
                    &self.partial_raw_bindings(r, &prior)?,
                )?;
                let v = self.compile_function_raw_expression_bound(
                    &r.value,
                    &prior,
                    &self.partial_raw_bindings(r, &prior)?,
                )?;
                format!("Litex.HasFiniteFunctionLimitValue M .both {q} (M.number 0) {v}")
            };
            lines.push(format!("  have _partial_clause_{i} : {ty} := {term}"));
        }
        let point = self.compile_function_raw_expression_bound(
            &r.point,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        let dimension = self.compile_function_raw_expression_bound(
            &r.dimension,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        let coordinate = self.compile_function_raw_expression_bound(
            &r.coordinate,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        let value = self.compile_function_raw_expression_bound(
            &r.value,
            position,
            &self.partial_raw_bindings(r, position)?,
        )?;
        lines.push(format!("  refine ⟨?_,?_⟩\n  · obtain ⟨radius,hr,hcontrol⟩ := _partial_clause_0\n    refine ⟨radius,hr,?_⟩\n    intro h hR hsmall\n    have member := hcontrol h ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hR,hR,hsmall⟩)\n    have h_member := ((Litex.SetSemantics.sep_members _ _ _).mp member).2.2\n    exact (congrArg (fun D => M.mem (Litex.coordinatePathValue {point} {dimension} {coordinate} h) D) {equal}).mp h_member\n  · exact (congrArg (fun q => Litex.HasFiniteFunctionLimitValue M .both q (M.number 0) {value}) _partial_quotient_match).mp _partial_clause_1"));
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}
