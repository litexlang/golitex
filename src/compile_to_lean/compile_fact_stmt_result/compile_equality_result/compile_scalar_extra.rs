use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::ScalarExtraEqualityProof as Rule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_scalar_extra(
        &self,
        goal: &EqualFact,
        proof: &Rule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Rule::ArcsinFromKnownSine(p) = proof {
            return self.compile_arcsine_from_known_sine(goal, p, position);
        }
        if let Rule::NestedRemainderUnit(_) = proof {
            return self.compile_nested_remainder_unit(goal, position);
        }
        let (argument_equality, quotient) = match proof {
            Rule::SqrtProductFromKnownArgument(p) => (p.argument_equality.as_ref(), false),
            Rule::SqrtQuotientFromKnownArgument(p) => (p.argument_equality.as_ref(), true),
            _ => return Err(invalid("Variant")),
        };
        for (root, other, reverse) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root_arg)) = root else {
                continue;
            };
            let (a, b) = match (other, quotient) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)), false) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Div(p)), true) => (&p.left, &p.right),
                _ => continue,
            };
            let (
                Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)),
                Obj::ExpLogOperator(ExpLogOperator::Sqrt(b)),
            ) = (a.as_ref(), b.as_ref())
            else {
                continue;
            };
            let argument = if quotient {
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: a.arg.clone(),
                    right: b.arg.clone(),
                }))
            } else {
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: a.arg.clone(),
                    right: b.arg.clone(),
                }))
            };
            // This is the producer's exact fixed search obligation. It owns
            // no new FactId producer, WD result, store or equality search.
            let view = EqualFact {
                fact_id: goal.fact_id,
                left: root_arg.arg.as_ref().clone(),
                right: argument,
                line_file: goal.line_file.clone(),
            };
            let equality = self.compile_equality_search(&view, argument_equality, position)?;
            let law = if quotient {
                "sqrtQuotientFromArgumentEquality"
            } else {
                "sqrtProductFromArgumentEquality"
            };
            return Ok(format!(
                "(Litex.{law} {} {} {equality}){}",
                self.compile_object_reference(root, position)?,
                self.compile_object_reference(other, position)?,
                if reverse { ".symm" } else { "" }
            ));
        }
        Err(invalid("KnownRootEndpoints"))
    }

    fn compile_nested_remainder_unit(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let (
                Obj::IntegerOperator(IntegerOperator::Mod(outer)),
                Obj::IntegerOperator(IntegerOperator::Mod(other)),
            ) = (left, right)
            else {
                continue;
            };
            let Obj::IntegerOperator(IntegerOperator::Mod(inner)) = outer.left.as_ref() else {
                continue;
            };
            if inner.left.ir() != other.left.ir() {
                continue;
            }
            let mut proofs = Vec::new();
            for (object, modulus) in [(left, &outer.right), (right, &other.right)] {
                if EvalRational::from_obj(modulus) != EvalRational::new(1, 1) {
                    return Err(invalid("RemainderUnitModulus"));
                }
                let term = self.compile_object_reference(object, position)?;
                let modulus_term = self.compile_object_reference(modulus, position)?;
                let observed = self.compile_numeric_observation(modulus, position)?;
                let unit = format!("(show Litex.denote {modulus_term} = M.number (1 : ℂ) from (({}).trans (congrArg M.number (by norm_num))))", observed.1);
                proofs.push(format!("(Litex.remainderUnitValue {term} {unit})"));
            }
            let proof = format!("({}.trans {}.symm)", proofs[0], proofs[1]);
            return Ok(if reversed {
                format!("{proof}.symm")
            } else {
                proof
            });
        }
        Err(invalid("NestedRemainderUnitEndpoints"))
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ScalarExtra/{part}"))
}
