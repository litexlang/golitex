use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_subset_rule(
        &self,
        fact: &SubsetFact,
        rule: &SubsetFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match rule {
            SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(_)
                if fact.left.ir() == fact.right.ir() =>
            {
                Ok(format!(
                    "(Litex.subsetRefl {})",
                    self.compile_object_reference(&fact.left, position)?
                ))
            }
            SubsetFactSearchProofByBuiltinRule::ListSetSubsetFromMembers(proof) => {
                self.compile_list_subset(fact, &proof.member_in_proofs, position)
            }
            SubsetFactSearchProofByBuiltinRule::SetBuilderSubsetOfParamSet(_) => {
                let Obj::SetFormer(SetFormer::SetBuilder(set)) = &fact.left else {
                    return Err(LeanCompileError::new(
                        "SetBuilder/SubsetSubject",
                        "Subset evidence has another constructor.",
                    ));
                };
                if set.param_set.ir() != fact.right.ir() {
                    return Err(LeanCompileError::new(
                        "SetBuilder/SubsetBound",
                        "Subset target is not the source bound.",
                    ));
                }
                Ok(format!("(by\n  let _set := {}\n  exact Litex.setBuilderSubset _set.val.bound _set.val.predicate)", self.compile_object_reference(&fact.left, position)?))
            }
            _ => Err(LeanCompileError::unsupported("Set/SubsetRule")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_list_subset(
        &self,
        fact: &SubsetFact,
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetFormer(SetFormer::ListSet(set)) = &fact.left else {
            return Err(LeanCompileError::new(
                "ListSet/SubsetSubject",
                "Selected subset evidence has another constructor.",
            ));
        };
        if proofs.len() != set.list.len() {
            return Err(LeanCompileError::new(
                "ListSet/SubsetArity",
                "Subset needs each recorded member proof.",
            ));
        }
        let upper = self.compile_object_reference(&fact.right, position)?;
        let mut term = format!("(Litex.emptySubset {upper})");
        for (i, (element, proof)) in set.list.iter().zip(proofs).enumerate().rev() {
            match source_subject(proof)? {
                Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == element.ir() && f.set.ir() == fact.right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ListSet/SubsetMember",
                        "The recorded child proves another element or upper bound.",
                    ))
                }
            }
            let member = self.compile_verify(proof, position)?.1;
            let suffix = format!("_set{}", ".val.tail".repeat(i));
            term = format!("(Litex.insertSubset {suffix}.val.element {suffix}.val.tail {upper} {suffix}.wd {member} {term})");
        }
        Ok(format!(
            "(by\n  let _set := {}\n  exact {term})",
            self.compile_object_reference(&fact.left, position)?
        ))
    }
}
