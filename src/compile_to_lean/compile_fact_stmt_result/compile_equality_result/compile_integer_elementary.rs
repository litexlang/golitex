use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_gcd_lcm::gcd_lcm_arguments;
use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_gcd_argument_identity(
        &self,
        fact: &EqualFact,
        negation: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (changed, base, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Some((changed_arg, b)), Some((a, d))) = (
                gcd_lcm_arguments(changed, false),
                gcd_lcm_arguments(base, false),
            ) else {
                continue;
            };
            if b.ir() != d.ir() {
                continue;
            }
            let reverse_args = match (changed_arg, negation) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)), true)
                    if p.arg.ir() == a.ir() =>
                {
                    false
                }
                (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), false)
                    if p.left.ir() == a.ir() && p.right.ir() == b.ir() =>
                {
                    false
                }
                (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), false)
                    if p.right.ir() == a.ir() && p.left.ir() == b.ir() =>
                {
                    true
                }
                _ => continue,
            };
            let base = self.compile_object_reference(base, position)?;
            let law = if negation {
                "gcdNegationValue"
            } else {
                "gcdAddArgumentValue"
            };
            let order = if negation {
                String::new()
            } else {
                format!(" {reverse_args}")
            };
            return Ok(format!("(let _gcd := {base}; (Litex.{law} (Litex.denote _gcd.val.left) (Litex.denote _gcd.val.right) _gcd.wd.1 _gcd.wd.2.1{order}){})",if reversed {".symm"} else {""}));
        }
        Err(invalid("GcdArgumentSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_gcd_positive_scale(
        &self,
        fact: &EqualFact,
        children: [&VerifyFactResult; 3],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (changed, scaled, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Some((ka, kb)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(product))) =
                (gcd_lcm_arguments(changed, false), scaled)
            else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(first)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(second)),
                Some((a, b)),
            ) = (ka, kb, gcd_lcm_arguments(&product.right, false))
            else {
                continue;
            };
            let k = product.left.as_ref();
            if first.left.ir() != k.ir()
                || second.left.ir() != k.ir()
                || first.right.ir() != a.ir()
                || second.right.ir() != b.ir()
            {
                continue;
            }
            let mut proofs = Vec::new();
            for (child, object) in children.iter().zip([a, b, k]) {
                if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir()==object.ir() && f.set==Obj::StandardSet(StandardSet::NPos))
                {
                    return Err(invalid("GcdScalePositiveSubject"));
                }
                proofs.push(self.compile_verify(child, position)?.1);
            }
            let scaled = self.compile_object_reference(scaled, position)?;
            return Ok(format!("(let _scaled := {scaled}; (Litex.gcdPositiveScaleValue (Litex.denote _scaled.val.right.val.left) (Litex.denote _scaled.val.right.val.right) (Litex.denote _scaled.val.left) {} {} {}){})",proofs[0],proofs[1],proofs[2],if reversed {".symm"} else {""}));
        }
        Err(invalid("GcdScaleSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_remainder_integer_shift(
        &self,
        fact: &EqualFact,
        integer: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (changed, base, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::IntegerOperator(IntegerOperator::Mod(left)),
                Obj::IntegerOperator(IntegerOperator::Mod(right)),
            ) = (changed, base)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = left.left.as_ref() else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = sum.right.as_ref()
            else {
                continue;
            };
            if left.right.ir() != right.right.ir()
                || sum.left.ir() != right.left.ir()
                || product.right.ir() != right.right.ir()
            {
                continue;
            }
            if !matches!(source_subject(integer)?,Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir()==product.left.ir() && f.set==Obj::StandardSet(StandardSet::Z))
            {
                return Err(invalid("RemainderMultiplierSubject"));
            }
            let proof = self.compile_verify(integer, position)?.1;
            let k = self.compile_object_reference(&product.left, position)?;
            let base = self.compile_object_reference(base, position)?;
            return Ok(format!("(let _mod := {base}; (Litex.remainderIntegerShiftValue (Litex.denote _mod.val.left) (Litex.denote {k}) (Litex.denote _mod.val.right) _mod.wd.1 {proof} _mod.wd.2.1){})",if reversed {".symm"} else {""}));
        }
        Err(invalid("RemainderShiftSubject"))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ElementaryInteger/{stage}"))
}
