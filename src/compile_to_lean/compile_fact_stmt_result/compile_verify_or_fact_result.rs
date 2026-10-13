use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::prelude::{
    OrFactSearchProofByBuiltinRule, OrFactSearchedProof, OrFactWellDefinedProof, VerifyOrFactResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_or_result(
        &self,
        result: &VerifyOrFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyOrFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Or/Failed"));
        };
        self.compile_or_wd(&proof.fact, &proof.well_defined_proof, position)?;
        let formed = SourcePosition {
            before: proof.fact.facts.len(),
            ..*position
        };
        let position = &formed;
        let fact = Fact::OrFact(proof.fact.clone());
        let term = match &proof.searched_proof {
            OrFactSearchedProof::ByKnownForallFact(known) => {
                return self.compile_known_application(&fact, known, position)
            }
            OrFactSearchedProof::BySelectedBranch(selected)
                if selected.assumed_negated_branches.is_empty() =>
            {
                if selected.selected_index >= proof.fact.facts.len()
                    || source_subject(&selected.selected_branch)?
                        != crate::ast::fact::and_chain_as_fact(
                            &proof.fact.facts[selected.selected_index],
                        )
                {
                    return Err(LeanCompileError::new(
                        "Or/SelectedSubject",
                        "The selected original branch differs from its proof or index.",
                    ));
                }
                let mut term = self.compile_verify(&selected.selected_branch, position)?.1;
                if selected.selected_index + 1 != proof.fact.facts.len() {
                    term = format!("(Or.inl {term})");
                }
                for _ in 0..selected.selected_index {
                    term = format!("(Or.inr {term})");
                }
                term
            }
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(selected),
            ) => {
                let [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)), AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(greater))] =
                    proof.fact.facts.as_slice()
                else {
                    return Err(LeanCompileError::unsupported("Or/IntegerTailShape"));
                };
                if equal.left.ir() != selected.subject.ir()
                    || equal.right.ir() != selected.base.ir()
                    || greater.left.ir() != selected.subject.ir()
                    || greater.right.ir() != selected.base.ir()
                {
                    return Err(LeanCompileError::new("Or/IntegerTailSubject", "The original equality and strict tail must use the recorded subject and base."));
                }
                let mut integer_memberships = Vec::new();
                for (child, operand) in [
                    (&selected.subject_in_z, &selected.subject),
                    (&selected.base_in_z, &selected.base),
                ] {
                    match source_subject(child)? {
                        Fact::AtomicFact(AtomicFact::InFact(member))
                            if member.element.ir() == operand.ir()
                                && member.set == Obj::StandardSet(StandardSet::Z) => {}
                        _ => {
                            return Err(LeanCompileError::new(
                                "Or/IntegerTailMembership",
                                "An integer child has another subject or carrier.",
                            ))
                        }
                    }
                    integer_memberships.push(self.compile_verify(child, position)?.1);
                }
                let Fact::AtomicFact(bound) = source_subject(&selected.subject_ge_base)? else {
                    return Err(LeanCompileError::unsupported("Or/IntegerTailBound"));
                };
                let (base, subject, strict) = source_order_oriented(&bound)?;
                if strict
                    || base.ir() != selected.base.ir()
                    || subject.ir() != selected.subject.ir()
                {
                    return Err(LeanCompileError::new(
                        "Or/IntegerTailBound",
                        "The weak-bound child has another subject, base or strictness.",
                    ));
                }
                let bound = self.compile_verify(&selected.subject_ge_base, position)?.1;
                let base = self.compile_object_reference(&selected.base, position)?;
                let subject = self.compile_object_reference(&selected.subject, position)?;
                format!(
                    "(Litex.integerSuccessorTail {subject} {base} {} {} {bound})",
                    integer_memberships[0], integer_memberships[1]
                )
            }
            _ => return Err(LeanCompileError::unsupported("Or/SelectedRule")),
        };
        Ok((self.fact_proposition(&fact, position)?, term))
    }

    pub(in crate::compile_to_lean) fn compile_or_wd(
        &self,
        fact: &OrFact,
        proof: &OrFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        if fact.facts.is_empty() || fact.facts.len() != proof.branches.len() {
            return Err(LeanCompileError::unsupported("Or/FormationArity"));
        }
        for (index, (branch, wd)) in fact.facts.iter().zip(&proof.branches).enumerate() {
            self.compile_fact_wd(
                wd,
                &crate::ast::fact::and_chain_as_fact(branch),
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
        }
        Ok(())
    }
}
