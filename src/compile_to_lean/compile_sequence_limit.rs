//! Replay the domain and convergence evidence owned by `lim(a)`.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::sequence_limit::{
    RealSequenceDomainProof, SequenceConvergenceProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SequenceLimitObjWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_limit::SequenceLimitEqualityProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_sequence_limit_equality(
        &self,
        fact: &EqualFact,
        proof: &SequenceLimitEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let SequenceLimitEqualityProof::Uniqueness(p) = proof {
            let (AtomicFact::HasSequenceLimitFact(left), AtomicFact::HasSequenceLimitFact(right)) =
                (&p.left.fact, &p.right.fact)
            else {
                return Err(LeanCompileError::unsupported("SequenceLimit/Candidates"));
            };
            if left.value.ir() != fact.left.ir()
                || right.value.ir() != fact.right.ir()
                || left.sequence.ir() != right.sequence.ir()
            {
                return Err(LeanCompileError::unsupported("SequenceLimit/Candidates"));
            }
            let citation = |candidate: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof| {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) = candidate.searched_proof.as_ref() else {
                    return Err(LeanCompileError::unsupported("SequenceLimit/CandidateCitation"));
                };
                self.compile_known_atomic(c, &candidate.fact, position)
            };
            let domain = self.sequence_parameter_raw_domain(&left.sequence, position)?;
            let real_left = self.compile_real_membership_certificate(&fact.left, position)?;
            let real_right = self.compile_real_membership_certificate(&fact.right, position)?;
            return Ok(format!("(Litex.sequenceLimitCandidatesEqual {} {} {} {domain} {real_left} {real_right} {} {})",
                self.compile_object_reference(&left.sequence, position)?,
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?,
                citation(&p.left)?, citation(&p.right)?));
        }
        let SequenceLimitEqualityProof::SelectedValue(proof) = proof else {
            unreachable!()
        };
        let (limit, value, reversed) = match (&fact.left, &fact.right) {
            (Obj::LimitOperator(LimitOperator::Sequence(p)), value) => (p, value, false),
            (value, Obj::LimitOperator(LimitOperator::Sequence(p))) => (p, value, true),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "SequenceLimit/SelectedSubject",
                ))
            }
        };
        let AtomicFact::HasSequenceLimitFact(candidate) = &proof.candidate.fact else {
            return Err(LeanCompileError::unsupported("SequenceLimit/Candidate"));
        };
        if candidate.sequence.ir() != limit.sequence.ir() || candidate.value.ir() != value.ir() {
            return Err(LeanCompileError::unsupported("SequenceLimit/Candidate"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            proof.candidate.searched_proof.as_ref()
        else {
            return Err(LeanCompileError::unsupported(
                "SequenceLimit/CandidateCitation",
            ));
        };
        let known = self.compile_known_atomic(citation, &proof.candidate.fact, position)?;
        let real = self.compile_real_membership_certificate(value, position)?;
        let limit_object = if reversed { &fact.right } else { &fact.left };
        let result = format!(
            "(Litex.sequenceLimitEqCandidate {} {} {real} {known})",
            self.compile_object_reference(limit_object, position)?,
            self.compile_object_reference(value, position)?
        );
        Ok(if reversed {
            format!("({result}).symm")
        } else {
            result
        })
    }

    /// Only use the original typed parameter's own membership producer; do
    /// not search the environment for an unrelated substitute domain fact.
    fn sequence_parameter_raw_domain(
        &self,
        sequence: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = sequence else {
            return Err(LeanCompileError::unsupported(
                "SequenceLimit/UniqueSequenceParameter",
            ));
        };
        let (_, Some(carrier), _, membership) = position.visible_parameter(*id, &self.runtime)?
        else {
            return Err(LeanCompileError::unsupported(
                "SequenceLimit/UniqueSequenceDomain",
            ));
        };
        let sequence = self.compile_object_reference(sequence, position)?;
        let carrier_term = self.compile_object_reference(carrier, position)?;
        let guarded = match carrier {
            Obj::SetFormer(SetFormer::SeqSet(set)) if set.set.as_ref() == &Obj::StandardSet(StandardSet::R) =>
                format!("(Litex.inOfSame {sequence} {sequence} {carrier_term} (Litex.fnSet (Litex.seqSignature {carrier_term}.val.carrier)) (Litex.sameRefl {sequence}) (Litex.seqSet_eq_fnSet {carrier_term}) {membership})"),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature))
                if matches!(signature.set_bound_parameters.groups.as_slice(), [g] if g.params.len() == 1 && g.param_type.as_ref() == &Obj::StandardSet(StandardSet::NPos))
                    && signature.dom_facts.is_empty()
                    && signature.ret_set.as_ref() == &Obj::StandardSet(StandardSet::R) => membership,
            _ => return Err(LeanCompileError::unsupported("SequenceLimit/UniqueSequenceDomain")),
        };
        Ok(format!("(Litex.unguardedFunctionDomain {sequence} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {guarded})"))
    }

    pub(super) fn compile_sequence_limit_wd(
        &self,
        object: &SequenceLimit,
        proof: &SequenceLimitObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_object(&object.sequence, &proof.sequence_wd)?;
        let sequence = self.compile_wd(&proof.sequence_wd, position)?;
        let domain = match &proof.sequence_domain {
            RealSequenceDomainProof::CompleteSignature(domain) => {
                let signature = &domain.signature;
                if !matches!(signature.set_bound_parameters.groups.as_slice(), [g] if g.params.len() == 1 && g.param_type.as_ref() == &Obj::StandardSet(StandardSet::NPos))
                    || !signature.dom_facts.is_empty()
                    || signature.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
                {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Signature"));
                }
                self.compile_complete_domain_member(&object.sequence, domain, position)?
            }
            RealSequenceDomainProof::Membership(membership) => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(membership)? else {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Domain"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Signature"));
                };
                if f.element.ir() != object.sequence.ir()
                    || !matches!(signature.set_bound_parameters.groups.as_slice(), [g] if g.params.len() == 1 && g.param_type.as_ref() == &Obj::StandardSet(StandardSet::NPos))
                    || !signature.dom_facts.is_empty()
                    || signature.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
                {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Signature"));
                }
                self.compile_verify(membership, position)?.1
            }
        };
        let convergence = match &proof.convergence {
            SequenceConvergenceProof::Candidate(candidate) => {
                let AtomicFact::HasSequenceLimitFact(f) = &candidate.fact else {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Candidate"));
                };
                if f.sequence.ir() != object.sequence.ir() {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Candidate"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    candidate.searched_proof.as_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "SequenceLimit/CandidateCitation",
                    ));
                };
                let known = self.compile_known_atomic(citation, &candidate.fact, position)?;
                let value = self.compile_object_reference(&f.value, position)?;
                let real = self.compile_real_membership_certificate(&f.value, position)?;
                format!("(Litex.sequenceConvergentOfCandidate _sequence {value} {real} {known})")
            }
            SequenceConvergenceProof::Existence { fact, proof } => {
                super::compile_sequence_epsilon::validate_limit_existence(&object.sequence, fact)?;
                if source_subject(proof)? != *fact {
                    return Err(LeanCompileError::unsupported("SequenceLimit/Existence"));
                }
                self.compile_verify(proof, position)?.1
            }
        };
        Ok(format!("(let _sequence := {sequence}; Litex.sequenceLimit _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {domain}) {convergence})"))
    }
}
