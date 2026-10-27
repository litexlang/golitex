//! Calls through a matrix or finite-sequence result retain the original WD stages.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_returned_array_call(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        receiver: &str,
        output: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj, String), LeanCompileError> {
        let (dimensions, carrier, signature_name) = match output {
            Obj::SetFormer(SetFormer::MatrixSet(m)) => (
                vec![m.rows.as_ref(), m.cols.as_ref()],
                m.set.as_ref(),
                "matrixSignature",
            ),
            Obj::SetFormer(SetFormer::FiniteSeqSet(s)) => {
                (vec![s.n.as_ref()], s.set.as_ref(), "finiteSeqSignature")
            }
            _ => return Err(LeanCompileError::unsupported("ReturnedArray/Carrier")),
        };
        if application.body.len() != 2 || application.body[1].len() != dimensions.len() {
            return Err(LeanCompileError::unsupported("ReturnedArray/CallShape"));
        }
        let count = dimensions.len();
        let child_offset = proof
            .child_obj_well_defined
            .len()
            .checked_sub(count)
            .ok_or_else(|| LeanCompileError::unsupported("ReturnedArray/ChildStages"))?;
        let requirement_offset = proof
            .requirement_fact_verified
            .len()
            .checked_sub(count)
            .ok_or_else(|| LeanCompileError::unsupported("ReturnedArray/RequirementStages"))?;
        let mut terms = Vec::new();
        let mut checks = Vec::new();
        for (index, (argument, dimension)) in
            application.body[1].iter().zip(&dimensions).enumerate()
        {
            let wd = &proof.child_obj_well_defined[child_offset + index];
            ensure_object(argument, wd)?;
            terms.push(self.compile_wd(
                wd,
                &SourcePosition {
                    before: child_offset + index,
                    ..*position
                },
            )?);
            let requirement = &proof.requirement_fact_verified[requirement_offset + index];
            if !matches!(source_subject(requirement)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==argument.ir() && matches!(&f.set, Obj::SetFormer(SetFormer::ClosedRange(r)) if closed_integer(&r.start)==Some(1) && r.end.ir()==dimension.ir()))
            {
                return Err(LeanCompileError::unsupported(
                    "ReturnedArray/IndexMembership",
                ));
            }
            checks.push(
                self.compile_verify(
                    requirement,
                    &SourcePosition {
                        before: proof.child_obj_well_defined.len() + requirement_offset + index,
                        ..*position
                    },
                )?
                .1,
            );
        }
        let formed = SourcePosition {
            before: usize::MAX,
            ..*position
        };
        let array = self.compile_object_reference(output, &formed)?;
        let packed = if count == 2 {
            format!("(Litex.callArguments2 {} {})", terms[0], terms[1])
        } else {
            terms[0].clone()
        };
        let base = if count == 2 {
            format!(
                "(Litex.callArguments2_mem_cart {} {} {} {})",
                terms[0], terms[1], checks[0], checks[1]
            )
        } else {
            checks[0].clone()
        };
        let call = format!(
            "(by\n  let _returned_receiver := {receiver}\n  let _returned_array := {array}\n  let _returned_signature := Litex.{signature_name} _returned_array\n  let _returned_argument := {packed}\n  have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver\n  have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨{base}, True.intro⟩\n  exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)"
        );
        let member = format!("(Litex.callOnInOutput {call})");
        Ok((call, carrier.clone(), member))
    }
}
