//! Replay finite real function-limit facts and their original domain/WD evidence.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_limit::{
    FunctionConvergenceProof, RealFunctionLimitDomainProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_function_limit::FunctionLimitEqualityProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FunctionLimitApproachRealProof, FunctionLimitPredicateDomainProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FunctionLimitApproachWellDefinedProof, FunctionLimitObjWellDefinedProof,
};
use crate::prelude::*;

pub(super) fn finite_side(
    approach: &LimitApproach,
) -> Result<(&'static str, &Obj), LeanCompileError> {
    match approach {
        LimitApproach::AtPoint(p) => Ok(("both", p)),
        LimitApproach::FromLeft(p) => Ok(("left", p)),
        LimitApproach::FromRight(p) => Ok(("right", p)),
        _ => Err(LeanCompileError::unsupported(
            "FunctionLimit/InfiniteApproach",
        )),
    }
}

pub(super) fn limit_parts(fact: &AtomicFact) -> Option<(&Obj, &LimitApproach, &Obj, bool)> {
    match fact {
        AtomicFact::HasFunctionLimitFact(f) => Some((&f.function, &f.approach, &f.value, false)),
        AtomicFact::NotHasFunctionLimitFact(f) => Some((&f.function, &f.approach, &f.value, true)),
        _ => None,
    }
}

pub(super) fn infinite_direction(
    approach: &LimitApproach,
) -> Result<&'static str, LeanCompileError> {
    match approach {
        LimitApproach::AtPositiveInfinity => Ok("positive"),
        LimitApproach::AtNegativeInfinity => Ok("negative"),
        _ => Err(LeanCompileError::unsupported(
            "FunctionLimit/FiniteApproach",
        )),
    }
}

fn real_requirement(object: &Obj, proof: &VerifyFactResult) -> Result<(), LeanCompileError> {
    if matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir() == object.ir() && f.set == Obj::StandardSet(StandardSet::R))
    {
        Ok(())
    } else {
        Err(LeanCompileError::unsupported("FunctionLimit/RealSubject"))
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_real_function_domain(
        &self,
        function: &Obj,
        proof: &RealFunctionLimitDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = &proof.source.signature;
        let params = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        let [(parameter, base)] = params.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "FunctionLimit/UnarySignature",
            ));
        };
        let correct_domain = if signature.dom_facts.is_empty() {
            proof.domain.ir() == base.ir()
        } else {
            matches!(&proof.domain, Obj::SetFormer(SetFormer::SetBuilder(b))
                if b.param_binding.id == parameter.id && b.param_set.ir() == base.ir()
                    && b.facts == signature.dom_facts)
        };
        if !correct_domain {
            return Err(LeanCompileError::unsupported(
                "FunctionLimit/EffectiveDomain",
            ));
        }
        for (set, checked) in [
            (*base, &proof.input_real),
            (signature.ret_set.as_ref(), &proof.output_real),
        ] {
            if !matches!(source_subject(checked)?, Fact::AtomicFact(AtomicFact::SubsetFact(f))
                if f.left.ir() == set.ir() && f.right == Obj::StandardSet(StandardSet::R))
            {
                return Err(LeanCompileError::unsupported(
                    "FunctionLimit/RealDomainSubject",
                ));
            }
        }
        let member = self.compile_complete_domain_member(function, &proof.source, position)?;
        let signature = self.compile_complete_domain_signature(&proof.source, position)?;
        let input = self.compile_verify(&proof.input_real, position)?.1;
        let output = self.compile_verify(&proof.output_real, position)?.1;
        let base = self.compile_object_reference(base, position)?;
        let value = self.compile_object_reference(function, position)?;
        Ok(format!("(show Litex.RealFunctionValue M (Litex.denote {value}) from by\n  let _limit_signature := {signature}\n  have _limit_function : Litex.In {value} (Litex.fnSet _limit_signature) := {member}\n  have _limit_input : Litex.Subset {base} (Litex.R (M := M)) := {input}\n  have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := {output}\n  refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩\n  intro x hx\n  exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1\n)"))
    }

    pub(super) fn compile_function_limit_predicate_domain(
        &self,
        fact: &AtomicFact,
        proof: &FunctionLimitPredicateDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (function, approach, value, _) = limit_parts(fact)
            .ok_or_else(|| LeanCompileError::unsupported("FunctionLimit/PredicateSubject"))?;
        let mut real_arguments = Vec::new();
        match (approach.point(), &proof.approach_real) {
            (Some(point), FunctionLimitApproachRealProof::Finite(real)) => {
                real_requirement(point, real)?;
                real_arguments.push(real.as_ref());
            }
            (None, FunctionLimitApproachRealProof::AtPositiveInfinity)
                if matches!(approach, LimitApproach::AtPositiveInfinity) => {}
            (None, FunctionLimitApproachRealProof::AtNegativeInfinity)
                if matches!(approach, LimitApproach::AtNegativeInfinity) => {}
            _ => return Err(LeanCompileError::unsupported("FunctionLimit/ApproachReal")),
        }
        real_requirement(value, &proof.value_real)?;
        let domain =
            self.compile_real_function_domain(function, &proof.function_domain, position)?;
        let function = self.compile_object_reference(function, position)?;
        let mut lines = vec![format!("have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote {function}) := {domain}")];
        real_arguments.push(proof.value_real.as_ref());
        for checked in real_arguments {
            let (ty, term) = self.compile_verify(checked, position)?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                source_subject(checked)?.fact_id().value()
            ));
        }
        Ok(lines)
    }

    pub(super) fn compile_function_limit_wd(
        &self,
        object: &FunctionLimit,
        proof: &FunctionLimitObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if object.approach != proof.approach {
            return Err(LeanCompileError::unsupported(
                "FunctionLimit/ApproachSubject",
            ));
        }
        if object.approach.point().is_none() {
            return self.compile_infinite_function_limit_wd(object, proof, position);
        }
        let (side, point) = finite_side(&object.approach)?;
        ensure_object(&object.function, &proof.function_wd)?;
        let FunctionLimitApproachWellDefinedProof::Finite { point_wd } = &proof.approach_wd else {
            return Err(LeanCompileError::unsupported("FunctionLimit/PointWD"));
        };
        ensure_object(point, point_wd)?;
        let FunctionLimitApproachRealProof::Finite(point_real) = &proof.approach_real else {
            return Err(LeanCompileError::unsupported("FunctionLimit/PointReal"));
        };
        real_requirement(point, point_real)?;
        let function = self.compile_wd(&proof.function_wd, position)?;
        let point_term = self.compile_wd(point_wd, position)?;
        let domain =
            self.compile_real_function_domain(&object.function, &proof.function_domain, position)?;
        let real = self.compile_verify(point_real, position)?.1;
        let convergence = match &proof.convergence {
            FunctionConvergenceProof::Candidate(p) => {
                let AtomicFact::HasFunctionLimitFact(f) = &p.fact else {
                    return Err(LeanCompileError::unsupported("FunctionLimit/Candidate"));
                };
                if f.function.ir() != object.function.ir() || f.approach != object.approach {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/CandidateSubject",
                    ));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    p.searched_proof.as_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/CandidateCitation",
                    ));
                };
                let known = self.compile_known_atomic(citation, &p.fact, position)?;
                format!("(Litex.finiteFunctionConvergentOfCandidate .{side} _function _point {} {known})", self.compile_object_reference(&f.value, position)?)
            }
            FunctionConvergenceProof::Existence { fact, proof } => {
                super::compile_function_limit_definition::validate_limit_existence(
                    &object.function,
                    &object.approach,
                    fact,
                )?;
                if source_subject(proof)? != *fact {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/ExistenceSubject",
                    ));
                }
                let (ty, term) = self.compile_verify(proof, position)?;
                format!("(Litex.finiteFunctionConvergentOfExistence .{side} _function _point (show {ty} from {term}))")
            }
        };
        Ok(format!("(let _function := {function}; let _point := {point_term}; Litex.finiteFunctionLimit .{side} _function _point {domain} {real} {convergence})"))
    }

    pub(super) fn compile_function_limit_equality(
        &self,
        fact: &EqualFact,
        proof: &FunctionLimitEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let citation = |p: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof| {
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) = p.searched_proof.as_ref() else {
                return Err(LeanCompileError::unsupported("FunctionLimit/CandidateCitation"));
            };
            self.compile_known_atomic(c, &p.fact, position)
        };
        match proof {
            FunctionLimitEqualityProof::SelectedValue(p) => {
                let (object, value, reversed) = match (&fact.left, &fact.right) {
                    (Obj::LimitOperator(LimitOperator::Function(f)), v) => (f, v, false),
                    (v, Obj::LimitOperator(LimitOperator::Function(f))) => (f, v, true),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "FunctionLimit/SelectedSubject",
                        ))
                    }
                };
                let law = if object.approach.point().is_some() {
                    finite_side(&object.approach)?;
                    "finiteFunctionLimitEqCandidate"
                } else {
                    infinite_direction(&object.approach)?;
                    "infiniteFunctionLimitEqCandidate"
                };
                let AtomicFact::HasFunctionLimitFact(candidate) = &p.candidate.fact else {
                    return Err(LeanCompileError::unsupported("FunctionLimit/Candidate"));
                };
                if candidate.function.ir() != object.function.ir()
                    || candidate.approach != object.approach
                {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/CandidateSubject",
                    ));
                }
                let comparison = EqualFact {
                    fact_id: fact.fact_id,
                    left: candidate.value.clone(),
                    right: value.clone(),
                    line_file: None,
                };
                let comparison =
                    self.compile_equality_search(&comparison, &p.value_equality, position)?;
                let selected = if reversed { &fact.right } else { &fact.left };
                let result = format!(
                    "((Litex.{law} {} {} {}).trans {comparison})",
                    self.compile_object_reference(selected, position)?,
                    self.compile_object_reference(&candidate.value, position)?,
                    citation(&p.candidate)?
                );
                Ok(if reversed {
                    format!("({result}).symm")
                } else {
                    result
                })
            }
            FunctionLimitEqualityProof::Uniqueness(p) => {
                let (
                    AtomicFact::HasFunctionLimitFact(left),
                    AtomicFact::HasFunctionLimitFact(right),
                ) = (&p.left.fact, &p.right.fact)
                else {
                    return Err(LeanCompileError::unsupported("FunctionLimit/Candidates"));
                };
                if left.function.ir() != right.function.ir()
                    || left.approach != right.approach
                    || left.value.ir() != fact.left.ir()
                    || right.value.ir() != fact.right.ir()
                {
                    return Err(LeanCompileError::unsupported(
                        "FunctionLimit/CandidateSubjects",
                    ));
                }
                let (law, approach_arguments) = if left.approach.point().is_some() {
                    let (side, point) = finite_side(&left.approach)?;
                    (
                        "finiteFunctionLimitCandidatesEqual",
                        format!(
                            ".{side} {} {}",
                            self.compile_object_reference(&left.function, position)?,
                            self.compile_object_reference(point, position)?
                        ),
                    )
                } else {
                    let direction = infinite_direction(&left.approach)?;
                    (
                        "infiniteFunctionLimitCandidatesEqual",
                        format!(
                            ".{direction} {}",
                            self.compile_object_reference(&left.function, position)?
                        ),
                    )
                };
                Ok(format!(
                    "(Litex.{law} {approach_arguments} {} {} {} {})",
                    self.compile_object_reference(&fact.left, position)?,
                    self.compile_object_reference(&fact.right, position)?,
                    citation(&p.left)?,
                    citation(&p.right)?
                ))
            }
        }
    }
}
