//! Calls through a matrix or sequence result retain the original WD stages.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

pub(super) fn array_parts(
    output: &Obj,
) -> Result<(Vec<Option<&Obj>>, &Obj, &'static str), LeanCompileError> {
    match output {
        Obj::SetFormer(SetFormer::MatrixSet(m)) => Ok((
            vec![Some(m.rows.as_ref()), Some(m.cols.as_ref())],
            m.set.as_ref(),
            "matrixSignature",
        )),
        Obj::SetFormer(SetFormer::FiniteSeqSet(s)) => Ok((
            vec![Some(s.n.as_ref())],
            s.set.as_ref(),
            "finiteSeqSignature",
        )),
        Obj::SetFormer(SetFormer::SeqSet(s)) => Ok((vec![None], s.set.as_ref(), "seqSignature")),
        _ => Err(LeanCompileError::unsupported("ReturnedArray/Carrier")),
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_returned_array_step(
        &self,
        arguments: &[Box<Obj>],
        proof: &FnObjObjWellDefinedProof,
        receiver: &str,
        output: &Obj,
        receiver_member: &str,
        child_offset: usize,
        requirement_offset: usize,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj), LeanCompileError> {
        let (dimensions, carrier, signature_name) = array_parts(output)?;
        let count = dimensions.len();
        if arguments.len() != count
            || child_offset + count > proof.child_obj_well_defined.len()
            || requirement_offset + count > proof.requirement_fact_verified.len()
        {
            return Err(LeanCompileError::unsupported("ReturnedArray/StageArity"));
        }
        let mut terms = Vec::new();
        let mut checks = Vec::new();
        for (index, (argument, dimension)) in arguments.iter().zip(&dimensions).enumerate() {
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
            let valid_index = match source_subject(requirement)? {
                Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == argument.ir() => {
                    match dimension {
                        Some(dimension) => {
                            matches!(&f.set, Obj::SetFormer(SetFormer::ClosedRange(r))
                            if closed_integer(&r.start) == Some(1) && r.end.ir() == dimension.ir())
                        }
                        None => f.set == Obj::StandardSet(StandardSet::NPos),
                    }
                }
                _ => false,
            };
            if !valid_index {
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
            before: proof.child_obj_well_defined.len() + requirement_offset + count,
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
        let signature_argument = if matches!(output, Obj::SetFormer(SetFormer::SeqSet(_))) {
            "_returned_array.val.carrier"
        } else {
            "_returned_array"
        };
        let call = format!(
            "(by\n  let _returned_receiver := {receiver}\n  let _returned_array := {array}\n  let _returned_signature := Litex.{signature_name} {signature_argument}\n  let _returned_argument := {packed}\n  have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature)  := {receiver_member}\n  have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨{base}, True.intro⟩\n  exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)"
        );
        Ok((call, carrier.clone()))
    }
}
