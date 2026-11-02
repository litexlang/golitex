//! Finite Euclidean vector-valued limits: replay original formation, WD and selection.
use super::compile_multivariable_scalar_limit::{validate_clauses, vector_set};
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::selector::{
    MultivariableSelectorSelectionProof, MultivariableVectorLimitWellDefinedProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferMultivariableAnalysisFactResult};
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MultivariableVectorLimit/{stage}"))
}
pub(super) fn parts(fact: &AtomicFact) -> Option<(&VectorMultivariableLimitRelation, bool)> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::VectorLimit(p) = &f.relation {
                Some((p, false))
            } else {
                None
            }
        }
        AtomicFact::NotMultivariableAnalysisFact(f) => {
            if let MultivariableAnalysisRelation::VectorLimit(p) = &f.relation {
                Some((p, true))
            } else {
                None
            }
        }
        _ => None,
    }
}
pub(super) fn existence(
    f: &Obj,
    p: &Obj,
    n: &Obj,
    m: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &vector_set(m))?;
    if [f, p, n, m].iter().any(|o| contains_parameter(o, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(e.facts.as_slice(),[QuantifierFreeFact::AtomicFact(a)] if parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.input_dimension.ir()==n.ir()&&r.output_dimension.ir()==m.ir()&&r.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(v)).ir()))
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_vector_wd(
        &self,
        object: &MultivariableVectorLimit,
        proof: &MultivariableVectorLimitWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let args = [
            object.function.as_ref(),
            object.point.as_ref(),
            object.input_dimension.as_ref(),
            object.output_dimension.as_ref(),
        ];
        let stages = &proof.stages;
        if stages.argument_well_defined.len() != 4 {
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
            binders.push(format!("let _multivariable_arg_{i} := {}", compiled));
            certified_arguments.push(format!("({compiled})"));
        }
        let mut lines = self.compile_multivariable_limit_domain(
            args[0],
            args[1],
            args[2],
            Some(args[3]),
            None,
            &stages.function_domain,
            &stages.domains,
            4,
            position,
        )?;
        let selected = match &stages.selection {
            MultivariableSelectorSelectionProof::Candidate(c) => {
                let (q, negative) = parts(&c.fact).ok_or_else(|| invalid("CandidateKind"))?;
                if negative
                    || q.function.ir() != args[0].ir()
                    || q.point.ir() != args[1].ir()
                    || q.input_dimension.ir() != args[2].ir()
                    || q.output_dimension.ir() != args[3].ir()
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
                format!("(Litex.multivariableVectorExistsOfCandidate (Litex.denote _multivariable_arg_0) (Litex.denote _multivariable_arg_1) (Litex.denote _multivariable_arg_2) (Litex.denote _multivariable_arg_3) {value} {term})")
            }
            MultivariableSelectorSelectionProof::Existence { fact, proof } => {
                existence(args[0], args[1], args[2], args[3], fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProof"));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(by\n  have _original_vector_limit_exists : {ty} := {term}\n  obtain ⟨v,hv,hc⟩ := _original_vector_limit_exists\n  exact ⟨v,hv,hc⟩\n)")
            }
        };
        lines.push(format!(
            "exact ⟨h_{},h_{},_multivariable_real,h_{},{selected}⟩",
            stages.domains[0].requirement.fact_id().value(),
            stages.domains[2].requirement.fact_id().value(),
            stages.domains[4].requirement.fact_id().value()
        ));
        Ok(format!(
            "({}; @Litex.Obj.mk M _ (Litex.multivariableVectorLimitRepresentation (M := M)) (Litex.MultivariableVectorLimitObj.mk {}) (by\n  {}\n))",
            binders.join("; "),
            certified_arguments.join(" "),
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
    pub(super) fn compile_multivariable_vector_equality(
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
            (s @ Obj::LimitOperator(LimitOperator::MultivariableVector(o)), v) => (s, v, o, false),
            (v, s @ Obj::LimitOperator(LimitOperator::MultivariableVector(o))) => (s, v, o, true),
            _ => return Err(invalid("SelectedSubject")),
        };
        let (candidate, negative) =
            parts(&proof.candidate.fact).ok_or_else(|| invalid("EqualityCandidate"))?;
        if negative
            || candidate.function.ir() != obj.function.ir()
            || candidate.point.ir() != obj.point.ir()
            || candidate.input_dimension.ir() != obj.input_dimension.ir()
            || candidate.output_dimension.ir() != obj.output_dimension.ir()
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
            "((Litex.multivariableVectorLimitEqCandidate {selected} {raw} {h}).trans {eq})"
        );
        Ok(if reverse {
            format!("{term}.symm")
        } else {
            term
        })
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_vector_inferences(
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
        let n = self.compile_function_raw_expression_bound(
            &r.input_dimension,
            position,
            &HashMap::new(),
        )?;
        let m = self.compile_function_raw_expression_bound(
            &r.output_dimension,
            position,
            &HashMap::new(),
        )?;
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
                &r.input_dimension,
                Some(&r.output_dimension),
                &r.value,
                &actual,
                &facts[..2],
            )?;
            let (view, equal) =
                self.compile_multivariable_limit_view(&r.function, domain, position)?;
            let ty = self.compile_multivariable_clause_value_proposition(&facts[0], position)?;
            let term=format!("(by\n{view}\n  obtain ⟨hv,ha,he⟩ := {}\n  intro radius h_radius\n  obtain ⟨input,hi,hpos,hclose⟩ := ha (Litex.denote radius) h_radius\n  rw [← {equal}] at hi\n  exact ⟨input,hi,hpos,hclose⟩\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[0], &(ty, term), position)?);
            let ty = self.compile_multivariable_clause_value_proposition(&facts[1], position)?;
            let term=format!("(by\n{view}\n  obtain ⟨hv,ha,he⟩ := {}\n  intro epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := he (Litex.denote epsilon) h_epsilon\n  refine ⟨delta,hd,?_⟩\n  intro input h_input\n  obtain ⟨hi,_,hpos,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_input\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ({equal} ▸ hi) hpos hclose⟩\n)",compiled.1);
            lines.push(self.emit_internal_fact(&facts[1], &(ty, term), position)?);
        }
        let target = facts.last().unwrap();
        existence(
            &r.function,
            &r.point,
            &r.input_dimension,
            &r.output_dimension,
            target,
        )?;
        let ty = self.compile_function_raw_predicate(target, position, &HashMap::new())?;
        let term=format!("(by\n  obtain ⟨value,hv,hc⟩ := Litex.multivariableVectorExistsOfCandidate {f} {pt} {n} {m} {v} {}\n  exact ⟨value,hv,hc⟩\n)",compiled.1);
        lines.push(self.emit_internal_fact(target, &(ty, term), position)?);
        Ok(lines)
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_vector_definition(
        &self,
        r: &VectorMultivariableLimitRelation,
        proof:&crate::execute::execute_fact_stmt::multivariable::definition::VectorMultivariableLimitRelationDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &proof.function_domain.signature,
        )
        .ok_or_else(|| invalid("DefinitionSignature"))?;
        validate_clauses(
            &r.function,
            &r.point,
            &r.input_dimension,
            Some(&r.output_dimension),
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
        let member = self.compile_object_reference(&vector_set(&r.output_dimension), position)?;
        let value_member = position
            .with_visible_membership(
                &r.value,
                &vector_set(&r.output_dimension),
                &mut |proof, producer| self.compile_verify(proof, producer).map(|c| c.1),
            )?
            .ok_or_else(|| invalid("DefinitionValueMembership"))?;
        lines.push(format!("  have _multivariable_value_member : Litex.In {value} {member} := {value_member}\n  refine ⟨_multivariable_value_member,?_,?_⟩\n  · intro radius h_radius\n    obtain ⟨input,hi,hpos,hclose⟩ := _multivariable_clause_0 (Litex.semanticObject radius (M.member_isSet h_radius)) h_radius\n    exact ⟨input,{equal} ▸ hi,hpos,hclose⟩\n  · intro epsilon h_epsilon\n    obtain ⟨delta,hd,hcontrol⟩ := _multivariable_clause_1 (Litex.semanticObject epsilon (M.member_isSet h_epsilon)) h_epsilon\n    refine ⟨delta,hd,?_⟩\n    intro input hi hpos hclose\n    have hi : M.mem input _multivariable_source_domain := {equal}.symm ▸ hi\n    have _good := hcontrol input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hpos,hclose⟩)\n    exact ((Litex.SetSemantics.sep_members _ _ _).mp _good).2.2"));
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}

impl LitexToLeanCompiler {
    pub(super) fn validate_multivariable_selector_domain(
        &self,
        subject: &Obj,
        proof: &crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof,
    ) -> Result<(), LeanCompileError> {
        use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
        let CompleteFunctionDomainSourceProof::MultivariableSelector(source) = &proof.source else {
            return Err(invalid("CallableSource"));
        };
        if source.selector.ir() != subject.ir() {
            return Err(invalid("CallableSubject"));
        }
        ensure_object(subject, &source.well_defined)?;
        let (carrier, _) = multivariable_selector_carrier(subject)?;
        self.validate_function_carrier_signature(&carrier, &proof.signature)
    }
}

/// Certified selectors retain their source scalar, vector or matrix carrier.
pub(super) fn multivariable_selector_carrier(
    object: &Obj,
) -> Result<(Obj, &'static str), LeanCompileError> {
    match object {
        Obj::LimitOperator(LimitOperator::MultivariableVector(o)) => Ok((
            vector_set(&o.output_dimension),
            "multivariableVectorLimitInVector",
        )),
        Obj::DerivativeOperator(DerivativeOperator::Gradient(o)) => {
            Ok((vector_set(&o.dimension), "gradientInVector"))
        }
        Obj::DerivativeOperator(DerivativeOperator::ScalarDifferential(o)) => Ok((
            super::compile_scalar_differential::matrix_set(&o.dimension),
            "scalarDifferentialInMatrix",
        )),
        Obj::DerivativeOperator(DerivativeOperator::Hessian(o)) => Ok((
            super::compile_jacobian::matrix_set(&o.dimension, &o.dimension),
            "hessianInMatrix",
        )),
        Obj::DerivativeOperator(DerivativeOperator::TotalDifferential(o)) => Ok((
            super::compile_jacobian::matrix_set(&o.output_dimension, &o.input_dimension),
            "totalDifferentialInMatrix",
        )),
        Obj::DerivativeOperator(DerivativeOperator::Jacobian(o)) => Ok((
            super::compile_jacobian::matrix_set(&o.output_dimension, &o.input_dimension),
            "jacobianInMatrix",
        )),
        Obj::DerivativeOperator(DerivativeOperator::Laplacian(_)) => {
            Ok((Obj::StandardSet(StandardSet::R), "laplacianInR"))
        }
        Obj::DerivativeOperator(DerivativeOperator::Divergence(_)) => {
            Ok((Obj::StandardSet(StandardSet::R), "divergenceInR"))
        }
        Obj::DerivativeOperator(DerivativeOperator::Curl(_)) => Ok((
            vector_set(&crate::execute::execute_fact_stmt::multivariable::helper::number(3)),
            "curlInVector",
        )),
        _ => Err(invalid("CallableFamily")),
    }
}
