use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_union_subset_componentwise(
        &self,
        fact: &SubsetFact,
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::SetOperator(SetOperator::Union(left)),
            Obj::SetOperator(SetOperator::Union(right)),
        ) = (&fact.left, &fact.right)
        else {
            return Err(LeanCompileError::unsupported("UnionSubset/Constructors"));
        };
        'orientation: for swapped in [false, true] {
            let bounds = if swapped {
                [&right.right, &right.left]
            } else {
                [&right.left, &right.right]
            };
            let pairs = [(&left.left, bounds[0]), (&left.right, bounds[1])];
            // The original producer skips exactly the syntactically reflexive
            // pairs. Every remaining pair must have its recorded child in order.
            let needed = pairs.iter().filter(|(a, b)| a.ir() != b.ir()).count();
            if proofs.len() != needed {
                continue;
            }
            let mut index = 0;
            for (a, b) in pairs {
                if a.ir() == b.ir() {
                    continue;
                }
                if !matches!(source_subject(&proofs[index])?, Fact::AtomicFact(AtomicFact::SubsetFact(p))
                    if p.left.ir() == a.ir() && p.right.ir() == b.ir())
                {
                    continue 'orientation;
                }
                index += 1;
            }
            let mut children = Vec::new();
            let mut index = 0;
            for ((a, b), field) in pairs.into_iter().zip(["left", "right"]) {
                if a.ir() == b.ir() {
                    children.push(format!("(Litex.subsetRefl _subset_left.val.{field})"));
                } else {
                    children.push(
                        self.compile_verify(&proofs[index], &position.atomic_search_prior(index)?)?
                            .1,
                    );
                    index += 1;
                }
            }
            let complete = position.atomic_search_prior(proofs.len())?;
            let left = self.compile_object_reference(&fact.left, &complete)?;
            let right = self.compile_object_reference(&fact.right, &complete)?;
            let law = if swapped {
                "unionMonoSwap"
            } else {
                "unionMono"
            };
            return Ok(format!("(let _subset_left := {left}; let _subset_right := {right}; Litex.{law} _subset_left.val.left _subset_left.val.right _subset_right.val.left _subset_right.val.right {} {})",children[0],children[1]));
        }
        Err(LeanCompileError::unsupported("UnionSubset/OrderedPremises"))
    }
}
