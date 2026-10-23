use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_membership_rule(
        &self,
        fact: &InFact,
        rule: &InFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match rule {
            InFactSearchProofByBuiltinRule::ListSetElementMembership(proof) => {
                let Obj::SetFormer(SetFormer::ListSet(set)) = &fact.set else {
                    return Err(LeanCompileError::new(
                        "ListSet/MembershipSubject",
                        "Selected enumeration evidence has another set constructor.",
                    ));
                };
                let selected = proof.selected_index;
                if selected >= set.list.len() {
                    return Err(LeanCompileError::new(
                        "ListSet/SelectedIndex",
                        "Selected element is outside the source enumeration.",
                    ));
                }
                match source_subject(&proof.equality_proof)? {
                    Fact::AtomicFact(AtomicFact::EqualFact(f))
                        if f.left.ir() == fact.element.ir()
                            && f.right.ir() == set.list[selected].ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "ListSet/SelectedEquality",
                            "Selected equality proves another member or orientation.",
                        ))
                    }
                }
                let eq = self.compile_verify(&proof.equality_proof, position)?.1;
                let element = self.compile_object_reference(&fact.element, position)?;
                let set = self.compile_object_reference(&fact.set, position)?;
                let suffix = |i: usize| format!("_set{}", ".val.tail".repeat(i));
                let mut term = format!("((Litex.inInsert_iff {element} {}.val.element {}.val.tail {}.wd).mpr (Or.inl {eq}))", suffix(selected), suffix(selected), suffix(selected));
                for i in (0..selected).rev() {
                    term = format!("((Litex.inInsert_iff {element} {}.val.element {}.val.tail {}.wd).mpr (Or.inr {term}))", suffix(i), suffix(i), suffix(i));
                }
                Ok(format!("(by\n  let _set := {set}\n  exact {term})"))
            }
            InFactSearchProofByBuiltinRule::SetBuilderMembership(proof) => self
                .compile_builder_membership(
                    fact,
                    &proof.requirement_facts,
                    &proof.proof_of_requirement_facts,
                    position,
                ),
            _ => Err(LeanCompileError::unsupported("Set/MembershipRule")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_builder_membership(
        &self,
        fact: &InFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != proofs.len() {
            return Err(LeanCompileError::unsupported("SetBuilder/MembershipArity"));
        }
        let mut witnesses = Vec::new();
        for (requirement, proof) in requirements.iter().zip(proofs) {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::new(
                    "SetBuilder/FilterProof",
                    "Predicate premise and evidence differ.",
                ));
            }
            witnesses.push(self.compile_verify(proof, position)?.1);
        }
        self.compile_builder_membership_evidence(fact, requirements, witnesses, position)
    }

    pub(in crate::compile_to_lean) fn compile_builder_membership_evidence(
        &self,
        fact: &InFact,
        requirements: &[Fact],
        mut witnesses: Vec<String>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetFormer(SetFormer::SetBuilder(set)) = &fact.set else {
            return Err(LeanCompileError::new(
                "SetBuilder/MembershipSubject",
                "Selected formation rule has another bound constructor.",
            ));
        };
        if requirements.len() != 1 + set.facts.len() || witnesses.len() != requirements.len() {
            return Err(LeanCompileError::new(
                "SetBuilder/MembershipArity",
                "Membership needs the recorded bound and every filter proof.",
            ));
        }
        let substitution = HashMap::from([(set.param_binding.id, fact.element.clone())]);
        for (i, requirement) in requirements.iter().enumerate() {
            if i == 0 {
                match requirement {
                    Fact::AtomicFact(AtomicFact::InFact(f))
                        if f.element.ir() == fact.element.ir()
                            && f.set.ir() == set.param_set.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "SetBuilder/BoundMembership",
                            "The first premise belongs to another element or bound.",
                        ))
                    }
                }
            } else if !instantiated_fact_matches(
                &crate::instantiate::quantifier_free_fact_to_fact(set.facts[i - 1].clone()),
                requirement,
                &substitution,
            ) {
                return Err(LeanCompileError::new(
                    "SetBuilder/FilterSubject",
                    "An ordered filter proves another instantiated predicate.",
                ));
            }
        }
        let predicate = if set.facts.is_empty() {
            "True.intro".into()
        } else {
            let mut tail = witnesses.pop().unwrap();
            for head in witnesses[1..].iter().rev() {
                tail = format!("(Exists.intro {head} {tail})");
            }
            tail
        };
        Ok(format!("(by\n  let _set := {}\n  exact (Litex.inSetBuilder_iff {} _set.val.bound _set.val.predicate).mpr ⟨{}, {}⟩)", self.compile_object_reference(&fact.set, position)?, self.compile_object_reference(&fact.element, position)?, witnesses[0], predicate))
    }
}
