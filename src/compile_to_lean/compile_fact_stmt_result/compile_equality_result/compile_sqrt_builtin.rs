use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sqrt_known_square(
        &self,
        goal: &EqualFact,
        premise: &EqualFactSearchedProof,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "SqrtKnownSquare/Requirements",
            ));
        }
        for (root, target, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(p)) = root else {
                continue;
            };
            if !matches!(source_subject(&requirements[0])?, Fact::AtomicFact(AtomicFact::InFact(ref f))
                if f.element.ir() == target.ir() && f.set == Obj::StandardSet(StandardSet::R))
            {
                continue;
            }
            let mut definitions = Vec::new();
            for (index, requirement) in requirements.iter().enumerate() {
                let child = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    index,
                );
                let compiled = self.compile_verify(requirement, &child)?;
                definitions.push(self.emit_internal_fact(
                    &source_subject(requirement)?,
                    &compiled,
                    &child,
                )?);
            }
            let complete = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                requirements.len(),
            );
            let real = self.compile_verify(&requirements[0], &complete)?.1;
            let nonnegative =
                self.compile_sqrt_bound(&requirements[1], target, false, &complete)?;
            // The producer fixes this original obligation. Resolve its existing
            // WD/citation; never register a synthetic constructor or new proof.
            let exponent = Obj::Literal(Literal::Number(Number::new("2".into())));
            let square = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                base: Box::new(target.clone()),
                exponent: Box::new(exponent.clone()),
            }));
            let obligation = EqualFact {
                fact_id: goal.fact_id,
                left: p.arg.as_ref().clone(),
                right: square.clone(),
                line_file: goal.line_file.clone(),
            };
            let equality = self.compile_equality_search(&obligation, premise, &complete)?;
            let square = self.compile_object_reference(&square, &complete)?;
            let exponent = self.compile_literal_natural_identity(&exponent, 2, &complete)?;
            let root = self.compile_object_reference(root, position)?;
            let target = self.compile_object_reference(target, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  {}\n  let _root := {root}\n  let _square := {square}\n  have _eq : Litex.denote _root.val.arg = M.powValue (Litex.denote {target}) (Litex.denote _square.val.exponent) := {equality}\n  have _exp : Litex.denote _square.val.exponent = M.number ((2 : ℕ) : ℂ) := {exponent}\n  rw [_exp] at _eq\n  exact ((congrArg (Litex.sqrtValue (M := M)) _eq).trans (Litex.sqrtOfNonnegativeSquare {target} {real} {nonnegative})){symmetric}\n)",definitions.join("\n").replace('\n', "\n  ")));
        }
        Err(LeanCompileError::unsupported("SqrtKnownSquare/Subject"))
    }

    pub(in crate::compile_to_lean) fn compile_sqrt_of_square(
        &self,
        goal: &EqualFact,
        absolute: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != usize::from(!absolute) {
            return Err(LeanCompileError::unsupported("SqrtOfSquare/Requirements"));
        }
        for (root, target, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root_arg)) = root else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = root_arg.arg.as_ref()
            else {
                continue;
            };
            if !matches!(power.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "2")
            {
                continue;
            }
            let argument = if absolute {
                let Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) = target else {
                    continue;
                };
                p.arg.as_ref()
            } else {
                target
            };
            if power.base.ir() != argument.ir() {
                continue;
            }
            let exponent = self.compile_literal_natural_identity(&power.exponent, 2, position)?;
            let target_term = self.compile_object_reference(target, position)?;
            let application = if absolute {
                format!("Litex.sqrtOfSquareAbsolute {target_term}")
            } else {
                let proof = self.compile_sqrt_bound(&requirements[0], argument, false, position)?;
                let real = self.compile_real_membership_certificate(argument, position)?;
                format!("Litex.sqrtOfNonnegativeSquare {target_term} {real} {proof}")
            };
            let symmetric = if reversed { ".symm" } else { "" };
            let root = self.compile_object_reference(root, position)?;
            return Ok(format!("(by\n  let _root := {root}\n  have _exp : Litex.denote _root.val.arg.val.exponent = M.number ((2 : ℕ) : ℂ) := {exponent}\n  have _identity : Litex.sqrtValue (M.powValue (Litex.denote _root.val.arg.val.base) (Litex.denote _root.val.arg.val.exponent)) = Litex.denote {target_term} := by\n    rw [_exp]\n    exact {application}\n  exact _identity{symmetric}\n)"));
        }
        Err(LeanCompileError::unsupported("SqrtOfSquare/Endpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_sqrt_product_quotient(
        &self,
        goal: &EqualFact,
        quotient: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 2 {
            return Err(LeanCompileError::unsupported("SqrtBinary/Requirements"));
        }
        for (root, target, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root_arg)) = root else {
                continue;
            };
            let (a, b, first, second) = match (root_arg.arg.as_ref(), target, quotient) {
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
                    false,
                ) => (&a.left, &a.right, &b.left, &b.right),
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(a)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(b)),
                    true,
                ) => (&a.left, &a.right, &b.left, &b.right),
                _ => continue,
            };
            let (
                Obj::ExpLogOperator(ExpLogOperator::Sqrt(first_arg)),
                Obj::ExpLogOperator(ExpLogOperator::Sqrt(second_arg)),
            ) = (first.as_ref(), second.as_ref())
            else {
                continue;
            };
            let reverse_args = if a.ir() == first_arg.arg.ir() && b.ir() == second_arg.arg.ir() {
                false
            } else if !quotient && b.ir() == first_arg.arg.ir() && a.ir() == second_arg.arg.ir() {
                true
            } else {
                continue;
            };
            // Both producers record the original input operand order. The
            // output product may commute its two square-root factors.
            let mut definitions = Vec::new();
            for (index, argument) in [a, b].into_iter().enumerate() {
                let child = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    index,
                );
                let bound = self.compile_sqrt_bound(
                    &requirements[index],
                    argument,
                    quotient && index == 1,
                    &child,
                )?;
                let fact = source_subject(&requirements[index])?;
                let compiled = self.compile_verify(&requirements[index], &child)?;
                definitions.push(self.emit_internal_fact(&fact, &compiled, &child)?);
                definitions.push(format!(
                    "have _bound_{index} : Litex.{} (Litex.number (M := M) 0) {} := {bound}",
                    if quotient && index == 1 { "Lt" } else { "Le" },
                    self.compile_object_reference(argument, position)?
                ));
            }
            let first = self.compile_object_reference(first, position)?;
            let second = self.compile_object_reference(second, position)?;
            let application = if quotient {
                format!("Litex.sqrtQuotient {first} {second} _bound_0 _bound_1")
            } else if reverse_args {
                format!("Litex.sqrtProduct {first} {second} true _bound_1 _bound_0")
            } else {
                format!("Litex.sqrtProduct {first} {second} false _bound_0 _bound_1")
            };
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(by\n  {}\n  exact ({application}){symmetric}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            ));
        }
        Err(LeanCompileError::unsupported("SqrtBinary/Endpoints"))
    }

    fn compile_sqrt_bound(
        &self,
        result: &VerifyFactResult,
        argument: &Obj,
        positive: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(subject) = source_subject(result)? else {
            return Err(LeanCompileError::unsupported("SqrtBuiltin/BoundFamily"));
        };
        let (zero, value, strict) = source_order_oriented(&subject)?;
        if !is_exact_zero(zero) || value.ir() != argument.ir() || (positive && !strict) {
            return Err(LeanCompileError::unsupported("SqrtBuiltin/BoundSubject"));
        }
        let proof = self.compile_verify(result, position)?.1;
        Ok(if strict && !positive {
            format!(
                "(Litex.ltToLe (Litex.number (M := M) 0) {} {proof})",
                self.compile_object_reference(argument, position)?
            )
        } else {
            proof
        })
    }
}
