use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_arcsine_from_known_sine(
        &self,
        fact: &EqualFact,
        evidence: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::ArcsinFromKnownSineProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if evidence.principal_bounds.len() != 2 {
            return Err(LeanCompileError::unsupported("Trig/KnownSineRequirements"));
        }
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some(("Arcsin", argument)) = trig_argument(object) else {
                continue;
            };
            let sine = Obj::TrigOperator(TrigOperator::Sin(Sin {
                arg: Box::new(other.clone()),
            }));
            // Fixed view of the original equality lookup, with no new source
            // fact, WD proof, store, publication or equality search.
            let view = EqualFact {
                fact_id: fact.fact_id,
                left: argument.clone(),
                right: sine.clone(),
                line_file: fact.line_file.clone(),
            };
            let equality =
                self.compile_equality_search(&view, &evidence.sine_equality, position)?;
            let mut bounds = Vec::new();
            for (i, child) in evidence.principal_bounds.iter().enumerate() {
                let Fact::AtomicFact(source) = source_subject(child)? else {
                    return Err(LeanCompileError::unsupported("Trig/KnownSineBoundFamily"));
                };
                let proof = self.compile_verify(child, position)?.1;
                let formed =
                    SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
                bounds.push(self.compile_principal_trig_bound(
                    &source,
                    &proof,
                    other,
                    true,
                    i == 0,
                    false,
                    &formed,
                )?);
            }
            let proof = format!(
                "(Litex.arcsineFromKnownSineValue {} {} {} {} {equality})",
                self.compile_object_reference(object, position)?,
                self.compile_object_reference(&sine, position)?,
                bounds[0],
                bounds[1]
            );
            return Ok(if reversed {
                format!("{proof}.symm")
            } else {
                proof
            });
        }
        Err(LeanCompileError::unsupported("Trig/KnownSineSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_trig_principal_inverse(
        &self,
        fact: &EqualFact,
        outer: &str,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (inner, half_pi, strict, law) = match outer {
            "Arcsin" => ("Sin", true, false, "arcsineSinePrincipalValue"),
            "Arccos" => ("Cos", false, false, "arccosineCosinePrincipalValue"),
            "Arctan" => ("Tan", true, true, "arctangentTangentPrincipalValue"),
            "Arccot" => ("Cot", false, true, "arccotangentCotangentPrincipalValue"),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Trig/PrincipalInverseOperation",
                ))
            }
        };
        if requirements.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "Trig/PrincipalInverseRequirements",
            ));
        }
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((op, nested)) = trig_argument(object) else {
                continue;
            };
            let Some((inner_op, arg)) = trig_argument(nested) else {
                continue;
            };
            if op != outer || inner_op != inner || arg.ir() != other.ir() {
                continue;
            }
            let mut bounds = Vec::new();
            for (i, child) in requirements.iter().enumerate() {
                let Fact::AtomicFact(source) = source_subject(child)? else {
                    return Err(LeanCompileError::unsupported(
                        "Trig/PrincipalInverseBoundFamily",
                    ));
                };
                let proof = self.compile_verify(child, position)?.1;
                let formed =
                    SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
                bounds.push(self.compile_principal_trig_bound(
                    &source,
                    &proof,
                    arg,
                    half_pi,
                    i == 0,
                    strict,
                    &formed,
                )?);
            }
            let term = self.compile_object_reference(object, position)?;
            let proof = format!("(Litex.{law} {term} {} {})", bounds[0], bounds[1]);
            return Ok(if reversed {
                format!("{proof}.symm")
            } else {
                proof
            });
        }
        Err(LeanCompileError::unsupported(
            "Trig/PrincipalInverseSubject",
        ))
    }
}
