//! Replay classical derivative formation and proof-consuming selector WD.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_derivative::{
    DerivativeAtWellDefinedProof, DerivativeConvergenceProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FunctionAnalysisPredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;

pub(super) fn derivative_parts(fact: &AtomicFact) -> Option<(&Obj, &Obj, Option<&Obj>, bool)> {
    Some(match fact {
        AtomicFact::HasDerivativeAtFact(f) => (&f.function, &f.point, Some(&f.value), false),
        AtomicFact::NotHasDerivativeAtFact(f) => (&f.function, &f.point, Some(&f.value), true),
        AtomicFact::FunctionDifferentiableAtFact(f) => (&f.function, &f.point, None, false),
        AtomicFact::NotFunctionDifferentiableAtFact(f) => (&f.function, &f.point, None, true),
        _ => return None,
    })
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Derivative/{stage}"))
}

pub(super) fn validate_derivative_existence(
    function: &Obj,
    point: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = fact else {
        return Err(invalid("Existence"));
    };
    let value = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if [function, point]
        .iter()
        .any(|a| contains_parameter(a, value.id))
    {
        return Err(invalid("ExistenceCapture"));
    }
    if !matches!(f.facts.as_slice(),[QuantifierFreeFact::AtomicFact(AtomicFact::HasDerivativeAtFact(p))]
        if p.function.ir()==function.ir()&&p.point.ir()==point.ir()&&p.value.ir()==Obj::Identifier(IdentifierObj::from_bound_name(value)).ir())
    {
        return Err(invalid("ExistenceCandidate"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_derivative_domain(
        &self,
        fact: &AtomicFact,
        proof: &FunctionAnalysisPredicateDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (function, point, value, _) =
            derivative_parts(fact).ok_or_else(|| invalid("PredicateFamily"))?;
        if proof.requirements.len() != 1 + usize::from(value.is_some()) {
            return Err(invalid("Requirements"));
        }
        let domain =
            self.compile_real_function_domain(function, &proof.function_domain, position)?;
        let f = self.compile_object_reference(function, position)?;
        let mut lines = vec![format!(
            "have _derivative_domain : Litex.RealFunctionValue M (Litex.denote {f}) := {domain}"
        )];
        let args = atomic_fact_args_ref(fact);
        for (index, requirement) in proof.requirements.iter().enumerate() {
            let (element, set) = if index == 0 {
                (point, &proof.function_domain.domain)
            } else {
                (
                    value.expect("validated value arity"),
                    &Obj::StandardSet(StandardSet::R),
                )
            };
            if !matches!(&requirement.requirement,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==element.ir()&&p.set.ir()==set.ir())
            {
                return Err(invalid("RequirementSubject"));
            }
            let prior = SourcePosition {
                before: args.len() + index,
                ..*position
            };
            let (ty, term) = match &requirement.result {
                PredicateDomainRequirementProof::Verified(p) => {
                    if source_subject(p)? != requirement.requirement {
                        return Err(invalid("RequirementProofSubject"));
                    }
                    self.compile_verify(p, &prior)?
                }
                PredicateDomainRequirementProof::CheckedArgument(p) => (
                    self.compile_function_raw_predicate(
                        &requirement.requirement,
                        &prior,
                        &std::collections::HashMap::new(),
                    )?,
                    self.compile_checked_domain_argument(
                        &requirement.requirement,
                        p,
                        &args,
                        index,
                        &prior,
                    )?,
                ),
            };
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                requirement.requirement.fact_id().value()
            ));
        }
        Ok(lines)
    }
    pub(super) fn compile_derivative_wd(
        &self,
        object: &DerivativeAt,
        proof: &DerivativeAtWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_object(&object.function, &proof.function_wd)?;
        ensure_object(&object.point, &proof.point_wd)?;
        let function = self.compile_wd(&proof.function_wd, position)?;
        let point = self.compile_wd(&proof.point_wd, position)?;
        let real = self.compile_real_function_domain(&object.function, &proof.domain, position)?;
        if !matches!(source_subject(&proof.point_in_domain)?,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==object.point.ir()&&p.set.ir()==proof.domain.domain.ir())
        {
            return Err(invalid("PointDomain"));
        }
        let (point_ty, point_member) = self.compile_verify(&proof.point_in_domain, position)?;
        let (view, equal) =
            self.compile_function_limit_domain_view(&object.function, &proof.domain, position)?;
        let existence = match &proof.convergence {
            DerivativeConvergenceProof::Candidate(candidate) => {
                let AtomicFact::HasDerivativeAtFact(p) = &candidate.fact else {
                    return Err(invalid("Candidate"));
                };
                if p.function.ir() != object.function.ir() || p.point.ir() != object.point.ir() {
                    return Err(invalid("CandidateSubject"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
                    candidate.searched_proof.as_ref()
                else {
                    return Err(invalid("CandidateCitation"));
                };
                let h = self.compile_known_atomic(c, &candidate.fact, position)?;
                format!("(Litex.derivativeExistsValueOfCandidate (Litex.denote _derivative_function) (Litex.denote _derivative_point) (Litex.denote {}) {h})",self.compile_object_reference(&p.value,position)?)
            }
            DerivativeConvergenceProof::Existence { fact, proof } => {
                validate_derivative_existence(&object.function, &object.point, fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProofSubject"));
                }
                self.compile_verify(proof, position)?.1
            }
        };
        // Keep the value's payload transparent to beta congruence. Only its
        // original domain and existence evidence belongs in the proof field.
        Ok(format!("(let _derivative_function := {function}; let _derivative_point := {point}; @Litex.Obj.mk M _ (Litex.derivativeRepresentation (M := M)) (Litex.DerivativeObj.mk _derivative_function _derivative_point) (by\n{view}\n  have _derivative_real : Litex.RealFunctionValue M (Litex.denote _derivative_function) := {real}\n  have _derivative_member : {point_ty} := {point_member}\n  exact ⟨_derivative_real, ({equal} ▸ _derivative_member), {existence}⟩\n))"))
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_derivative_equality(
        &self,
        fact: &EqualFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_derivative::DerivativeSelectedValueProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (selected, value, object, reversed) = match (&fact.left, &fact.right) {
            (Obj::DerivativeOperator(DerivativeOperator::AtPoint(p)), value) => {
                (&fact.left, value, p, false)
            }
            (value, Obj::DerivativeOperator(DerivativeOperator::AtPoint(p))) => {
                (&fact.right, value, p, true)
            }
            _ => return Err(invalid("SelectedObject")),
        };
        let AtomicFact::HasDerivativeAtFact(candidate) = &proof.candidate.fact else {
            return Err(invalid("EqualityCandidate"));
        };
        if candidate.function.ir() != object.function.ir()
            || candidate.point.ir() != object.point.ir()
        {
            return Err(invalid("EqualityCandidateSubject"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
            proof.candidate.searched_proof.as_ref()
        else {
            return Err(invalid("EqualityCitation"));
        };
        let h = self.compile_known_atomic(c, &proof.candidate.fact, position)?;
        let real = format!(
            "(Litex.derivativeCandidateInR {} {} {} {h})",
            self.compile_object_reference(&candidate.function, position)?,
            self.compile_object_reference(&candidate.point, position)?,
            self.compile_object_reference(&candidate.value, position)?
        );
        let obligation = EqualFact {
            fact_id: fact.fact_id,
            left: candidate.value.clone(),
            right: value.clone(),
            line_file: None,
        };
        let matched = self.compile_equality_search(&obligation, &proof.value_equality, position)?;
        let term = format!(
            "((Litex.derivativeEqCandidate {} {} {real} {h}).trans {matched})",
            self.compile_object_reference(selected, position)?,
            self.compile_object_reference(&candidate.value, position)?
        );
        Ok(if reversed {
            format!("({term}).symm")
        } else {
            term
        })
    }
}
