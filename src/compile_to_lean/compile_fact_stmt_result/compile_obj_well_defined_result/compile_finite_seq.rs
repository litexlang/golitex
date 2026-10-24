use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSeqSetObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_finite_seq_signature(
        sequence: &FiniteSeqSet,
        signature: &FnSet,
    ) -> Result<(), LeanCompileError> {
        let [group] = signature.set_bound_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("FiniteSeq/Signature"));
        };
        if group.params.len() != 1
            || !signature.dom_facts.is_empty()
            || signature.ret_set.ir() != sequence.set.ir()
            || !matches!(group.param_type.as_ref(), Obj::SetFormer(SetFormer::ClosedRange(range))
                if matches!(range.start.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
                    && range.end.ir() == sequence.n.ir())
        {
            return Err(LeanCompileError::unsupported("FiniteSeq/Signature"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_finite_seq_wd(
        &self,
        sequence: &FiniteSeqSet,
        proof: &FiniteSeqSetObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.child_obj_well_defined.len() != 2 || proof.requirement_fact_verified.len() != 2 {
            return Err(LeanCompileError::unsupported("FiniteSeq/Stages"));
        }
        let mut terms = Vec::new();
        for (index, object) in [&sequence.set, &sequence.n].iter().enumerate() {
            let child = &proof.child_obj_well_defined[index];
            ensure_object(object, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let [sethood, natural] = proof.requirement_fact_verified.as_slice() else {
            unreachable!()
        };
        if !matches!(source_subject(sethood)?, Fact::AtomicFact(AtomicFact::IsSetFact(f))
            if f.set.ir() == sequence.set.ir())
            || !matches!(source_subject(natural)?, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == sequence.n.ir() && f.set == Obj::StandardSet(StandardSet::N))
        {
            return Err(LeanCompileError::unsupported("FiniteSeq/Requirements"));
        }
        let sethood = self.compile_wd_requirement(
            sethood,
            &SourcePosition {
                before: 2,
                ..*position
            },
        )?;
        let natural = self.compile_wd_requirement(
            natural,
            &SourcePosition {
                before: 3,
                ..*position
            },
        )?;
        Ok(format!(
            "(Litex.finiteSeq {} {} {sethood} {natural})",
            terms[0], terms[1]
        ))
    }
}
