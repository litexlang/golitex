use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_composed_structure::AbsProductFromFactorsProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Compose the original input-left/input-right absolute-value equalities.
    /// Goal orientation and output permutation do not reorder child execution.
    pub(super) fn compile_abs_product_strategy(
        &self,
        goal: &EqualFact,
        proof: &AbsProductFromFactorsProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let children = &proof.proof_of_requirement_facts;
        if proof.requirement_facts.len() != 2 || children.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "AbsProductStrategy/Requirements",
            ));
        }
        let mut requirements = Vec::with_capacity(2);
        for (requirement, child) in proof.requirement_facts.iter().zip(children) {
            if source_subject(child)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "AbsProductStrategy/RequirementSubject",
                ));
            }
            let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = requirement else {
                return Err(LeanCompileError::unsupported(
                    "AbsProductStrategy/RequirementSubject",
                ));
            };
            requirements.push(equal);
        }
        for (absolute, product, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = absolute else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(input)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(output)),
            ) = (abs.arg.as_ref(), product)
            else {
                continue;
            };
            if !requirements
                .iter()
                .zip([&input.left, &input.right])
                .all(|(equal, input)| {
                    matches!(&equal.left, Obj::ArithmeticOperator(ArithmeticOperator::Abs(a))
                    if a.arg.ir() == input.ir())
                })
            {
                return Err(LeanCompileError::unsupported(
                    "AbsProductStrategy/RequirementSubject",
                ));
            }
            let swapped = if requirements[0].right.ir() == output.left.ir()
                && requirements[1].right.ir() == output.right.ir()
            {
                false
            } else if requirements[0].right.ir() == output.right.ir()
                && requirements[1].right.ir() == output.left.ir()
            {
                true
            } else {
                return Err(LeanCompileError::unsupported(
                    "AbsProductStrategy/RequirementSubject",
                ));
            };
            let mut absolutes = Vec::with_capacity(2);
            let mut equalities = Vec::with_capacity(2);
            for (index, (equal, child)) in requirements.iter().zip(children).enumerate() {
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let compiled = self.compile_verify(child, &prior)?;
                let checked = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
                absolutes.push(self.compile_object_reference(&equal.left, &checked)?);
                equalities.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(&equal.left, &checked)?,
                    self.compile_normalization_value(&equal.right, &checked)?,
                    compiled.1
                ));
            }
            self.compile_object_reference(&goal.left, position)?;
            self.compile_object_reference(&goal.right, position)?;
            let (first, second) = if swapped { (1, 0) } else { (0, 1) };
            let symmetry = if reversed { ".symm" } else { "" };
            return Ok(format!("(show {} = {} from ((Litex.absProduct {} {} {swapped}).trans (congrArg₂ M.mulValue {} {})){symmetry})",
                self.compile_normalization_value(&goal.left, position)?,
                self.compile_normalization_value(&goal.right, position)?,
                absolutes[first], absolutes[second], equalities[first], equalities[second]));
        }
        Err(LeanCompileError::unsupported("AbsProductStrategy/Subject"))
    }
}
