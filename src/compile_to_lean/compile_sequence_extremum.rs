//! Replay finite limsup/liminf WD and the selected original candidate/existence proof.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::sequence_limit::{
    RealSequenceDomainProof, SequenceConvergenceProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::prelude::*;

pub(super) fn extremum_parts(fact: &AtomicFact) -> Option<(&Obj, &Obj, bool, bool)> {
    Some(match fact {
        AtomicFact::HasSequenceLimsupFact(f) => (&f.sequence, &f.value, true, false),
        AtomicFact::HasSequenceLiminfFact(f) => (&f.sequence, &f.value, false, false),
        AtomicFact::NotHasSequenceLimsupFact(f) => (&f.sequence, &f.value, true, true),
        AtomicFact::NotHasSequenceLiminfFact(f) => (&f.sequence, &f.value, false, true),
        _ => return None,
    })
}
pub(super) fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceExtremum/{stage}"))
}

pub(super) fn validate_extremum_existence(
    sequence: &Obj,
    upper: bool,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(f) = fact else {
        return Err(invalid("Existence"));
    };
    let p = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if contains_parameter(sequence, p.id) {
        return Err(invalid("BinderCapture"));
    }
    let [QuantifierFreeFact::AtomicFact(candidate)] = f.facts.as_slice() else {
        return Err(invalid("ExistenceClause"));
    };
    let (a, v, kind, negative) =
        extremum_parts(candidate).ok_or_else(|| invalid("ExistenceKind"))?;
    if kind != upper
        || negative
        || a.ir() != sequence.ir()
        || v.ir() != Obj::Identifier(IdentifierObj::from_bound_name(p)).ir()
    {
        return Err(invalid("ExistenceSubject"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_sequence_extremum_wd(
        &self,
        upper: bool,
        sequence: &Obj,
        sequence_wd: &ObjWellDefinedProof,
        sequence_domain: &RealSequenceDomainProof,
        selection: &SequenceConvergenceProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_object(sequence, sequence_wd)?;
        let object = self.compile_wd(sequence_wd, position)?;
        let domain = self.compile_real_sequence_domain(sequence, sequence_domain, position)?;
        let selected = match selection {
            SequenceConvergenceProof::Candidate(candidate) => {
                let (a, v, kind, negative) =
                    extremum_parts(&candidate.fact).ok_or_else(|| invalid("CandidateKind"))?;
                if kind != upper || negative || a.ir() != sequence.ir() {
                    return Err(invalid("CandidateSubject"));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    candidate.searched_proof.as_ref()
                else {
                    return Err(invalid("CandidateCitation"));
                };
                let known = self.compile_known_atomic(citation, &candidate.fact, position)?;
                let value = self.compile_object_reference(v, position)?;
                let real = self.compile_real_membership_certificate(v, position)?;
                format!("(Litex.sequenceExtremumExistsOfCandidate {upper} _sequence {value} {real} {known})")
            }
            SequenceConvergenceProof::Existence { fact, proof } => {
                validate_extremum_existence(sequence, upper, fact)?;
                if source_subject(proof)? != *fact {
                    return Err(invalid("ExistenceProofSubject"));
                }
                self.compile_verify(proof, position)?.1
            }
        };
        Ok(format!("(let _sequence := {object}; Litex.sequenceExtremum {upper} _sequence (Litex.unguardedFunctionDomain _sequence (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {domain}) {selected})"))
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_sequence_limsup_equality(
        &self,
        fact: &EqualFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_limsup::SequenceLimsupEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_limsup::SequenceLimsupEqualityProof as P;
        match proof {
            P::SelectedValue(p) => self.compile_sequence_extremum_selected(
                fact,
                true,
                &p.candidate,
                &p.value_equality,
                position,
            ),
            P::Uniqueness(p) => {
                self.compile_sequence_extremum_unique(fact, true, &p.left, &p.right, position)
            }
        }
    }
    pub(super) fn compile_sequence_liminf_equality(
        &self,
        fact: &EqualFact,
        proof:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_liminf::SequenceLiminfEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_liminf::SequenceLiminfEqualityProof as P;
        match proof {
            P::SelectedValue(p) => self.compile_sequence_extremum_selected(
                fact,
                false,
                &p.candidate,
                &p.value_equality,
                position,
            ),
            P::Uniqueness(p) => {
                self.compile_sequence_extremum_unique(fact, false, &p.left, &p.right, position)
            }
        }
    }
    fn compile_extremum_citation(
        &self,
        upper: bool,
        candidate:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (_, _, kind, negative) =
            extremum_parts(&candidate.fact).ok_or_else(|| invalid("CandidateKind"))?;
        if kind != upper || negative {
            return Err(invalid("CandidateKind"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
            candidate.searched_proof.as_ref()
        else {
            return Err(invalid("CandidateCitation"));
        };
        self.compile_known_atomic(c, &candidate.fact, position)
    }
    fn compile_sequence_extremum_selected(
        &self,
        fact: &EqualFact,
        upper: bool,
        candidate:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
        equality: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (selected, value, sequence, reversed) = match (&fact.left, &fact.right, upper) {
            (Obj::LimitOperator(LimitOperator::SequenceLimsup(p)), value, true) => {
                (&fact.left, value, p.sequence.as_ref(), false)
            }
            (value, Obj::LimitOperator(LimitOperator::SequenceLimsup(p)), true) => {
                (&fact.right, value, p.sequence.as_ref(), true)
            }
            (Obj::LimitOperator(LimitOperator::SequenceLiminf(p)), value, false) => {
                (&fact.left, value, p.sequence.as_ref(), false)
            }
            (value, Obj::LimitOperator(LimitOperator::SequenceLiminf(p)), false) => {
                (&fact.right, value, p.sequence.as_ref(), true)
            }
            _ => return Err(invalid("SelectedSubject")),
        };
        let (a, v, kind, negative) =
            extremum_parts(&candidate.fact).ok_or_else(|| invalid("CandidateKind"))?;
        if a.ir() != sequence.ir() || kind != upper || negative {
            return Err(invalid("CandidateSubject"));
        }
        let known = self.compile_extremum_citation(upper, candidate, position)?;
        let real = self.compile_real_membership_certificate(v, position)?;
        let obligation = EqualFact {
            fact_id: fact.fact_id,
            left: v.clone(),
            right: value.clone(),
            line_file: None,
        };
        let matched = self.compile_equality_search(&obligation, equality, position)?;
        let result = format!(
            "((Litex.sequenceExtremumEqCandidate {upper} {} {} {real} {known}).trans {matched})",
            self.compile_object_reference(selected, position)?,
            self.compile_object_reference(v, position)?
        );
        Ok(if reversed {
            format!("({result}).symm")
        } else {
            result
        })
    }
    fn compile_sequence_extremum_unique(
        &self,
        fact: &EqualFact,
        upper: bool,
        left:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
        right:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (a, v, kind, negative) =
            extremum_parts(&left.fact).ok_or_else(|| invalid("CandidateKind"))?;
        let (b, w, kind2, negative2) =
            extremum_parts(&right.fact).ok_or_else(|| invalid("CandidateKind"))?;
        if kind != upper
            || kind2 != upper
            || negative
            || negative2
            || a.ir() != b.ir()
            || v.ir() != fact.left.ir()
            || w.ir() != fact.right.ir()
        {
            return Err(invalid("UniquenessSubject"));
        }
        let domain = self.sequence_parameter_raw_domain(a, position)?;
        let hv = self.compile_real_membership_certificate(v, position)?;
        let hw = self.compile_real_membership_certificate(w, position)?;
        Ok(format!(
            "(Litex.sequenceExtremumCandidatesEqual {upper} {} {} {} {domain} {hv} {hw} {} {})",
            self.compile_object_reference(a, position)?,
            self.compile_object_reference(v, position)?,
            self.compile_object_reference(w, position)?,
            self.compile_extremum_citation(upper, left, position)?,
            self.compile_extremum_citation(upper, right, position)?
        ))
    }
}
