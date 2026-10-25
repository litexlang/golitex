use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SeqSetObjWellDefinedProof;
use crate::prelude::*;
impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_seq_signature(
        sequence: &SeqSet,
        signature: &FnSet,
    ) -> Result<(), LeanCompileError> {
        let [group] = signature.set_bound_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Seq/Signature"));
        };
        if group.params.len() != 1
            || group.param_type.as_ref() != &Obj::StandardSet(StandardSet::NPos)
            || !signature.dom_facts.is_empty()
            || signature.ret_set.ir() != sequence.set.ir()
        {
            return Err(LeanCompileError::unsupported("Seq/Signature"));
        }
        Ok(())
    }
    pub(in crate::compile_to_lean) fn compile_seq_wd(
        &self,
        sequence: &SeqSet,
        proof: &SeqSetObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [child] = proof.child_obj_well_defined.as_slice() else {
            return Err(LeanCompileError::unsupported("Seq/WDStages"));
        };
        let [sethood] = proof.requirement_fact_verified.as_slice() else {
            return Err(LeanCompileError::unsupported("Seq/WDStages"));
        };
        ensure_object(&sequence.set, child)?;
        if !matches!(source_subject(sethood)?,Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==sequence.set.ir())
        {
            return Err(LeanCompileError::unsupported("Seq/CarrierSet"));
        }
        let carrier = self.compile_wd(
            child,
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let sethood = self.compile_wd_requirement(
            sethood,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        Ok(format!("(Litex.seqSet {carrier} {sethood})"))
    }
}
