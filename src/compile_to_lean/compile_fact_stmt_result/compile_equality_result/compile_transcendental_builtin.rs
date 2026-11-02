use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_exp_sum(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::ExpLogOperator(ExpLogOperator::Exp(exp)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
            ) = (left, right)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = exp.arg.as_ref() else {
                continue;
            };
            let (
                Obj::ExpLogOperator(ExpLogOperator::Exp(a)),
                Obj::ExpLogOperator(ExpLogOperator::Exp(b)),
            ) = (product.left.as_ref(), product.right.as_ref())
            else {
                continue;
            };
            let reverse_args = if sum.left.ir() == a.arg.ir() && sum.right.ir() == b.arg.ir() {
                false
            } else if sum.left.ir() == b.arg.ir() && sum.right.ir() == a.arg.ir() {
                true
            } else {
                continue;
            };
            let product = self.compile_object_reference(right, position)?;
            return Ok(format!("(let _exp_product := {product}; (Litex.exponentialSumValue _exp_product.val.left _exp_product.val.right {reverse_args}){})", if reversed { ".symm" } else { "" }));
        }
        Err(LeanCompileError::unsupported("ExpSum/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_trig_sum(
        &self,
        fact: &EqualFact,
        sine: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((kind, Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)))) =
                trig_argument(left)
            else {
                continue;
            };
            if kind != if sine { "Sin" } else { "Cos" } {
                continue;
            }
            let (p, q) = match (right, sine) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), true) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)), false) => (&p.left, &p.right),
                _ => continue,
            };
            let pair = |o: &Obj, lk: &str, la: &Obj, rk: &str, ra: &Obj| {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = o else {
                    return false;
                };
                matches!(trig_argument(&p.left),Some((k,a)) if k==lk && a.ir()==la.ir())
                    && matches!(trig_argument(&p.right),Some((k,a)) if k==rk && a.ir()==ra.ir())
            };
            let valid = if sine {
                let sin_cos = |p: &Obj, q: &Obj| {
                    pair(p, "Sin", &sum.left, "Cos", &sum.right)
                        && (pair(q, "Cos", &sum.left, "Sin", &sum.right)
                            || pair(q, "Sin", &sum.right, "Cos", &sum.left))
                };
                sin_cos(p, q) || sin_cos(q, p)
            } else {
                (pair(p, "Cos", &sum.left, "Cos", &sum.right)
                    || pair(p, "Cos", &sum.right, "Cos", &sum.left))
                    && pair(q, "Sin", &sum.left, "Sin", &sum.right)
            };
            if !valid {
                continue;
            }
            let a = self.compile_numeric_observation(&sum.left, position)?.0;
            let b = self.compile_numeric_observation(&sum.right, position)?.0;
            let law = if sine {
                "sineAdditionComplex"
            } else {
                "cosineAdditionComplex"
            };
            return self.compile_trig_native_identity(fact,
                &format!("{}simpa only [Complex.add_re, add_comm, mul_comm] using (Litex.{law} ({a}).re ({b}).re)", if reversed { "symm; " } else { "" }),
                position);
        }
        Err(LeanCompileError::unsupported("TrigSum/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_absolute_square(
        &self,
        fact: &EqualFact,
        real: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(q)),
            ) = (abs.arg.as_ref(), right)
            else {
                continue;
            };
            if p.base.ir() != q.base.ir()
                || !matches!(p.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value=="2")
                || !matches!(q.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value=="2")
                || !matches!(source_subject(real)?, Fact::AtomicFact(AtomicFact::InFact(ref f)) if f.element.ir()==p.base.ir() && f.set==Obj::StandardSet(StandardSet::R))
            {
                continue;
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(std::slice::from_ref(real)),
                0,
            );
            let proof = self.compile_verify(real, &child)?.1;
            let base = self.compile_object_reference(&p.base, position)?;
            return Ok(format!(
                "(Litex.absoluteSquareValue {base} {proof}){}",
                if reversed { ".symm" } else { "" }
            ));
        }
        Err(LeanCompileError::unsupported(
            "AbsoluteSquare/EndpointsOrRealPremise",
        ))
    }
}
