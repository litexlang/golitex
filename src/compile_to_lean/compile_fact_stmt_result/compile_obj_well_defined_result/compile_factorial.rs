use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn factorial_argument(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::IntegerOperator(IntegerOperator::Factorial(p)) => Some(&p.arg),
        _ => None,
    }
}

fn plus_one(object: &Obj) -> Option<&Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) = object else {
        return None;
    };
    let one = |o: &Obj| matches!(o, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1");
    if one(&p.right) {
        Some(&p.left)
    } else if one(&p.left) {
        Some(&p.right)
    } else {
        None
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_factorial_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([child], [requirement]) = (children, requirements) else {
            return Err(LeanCompileError::unsupported("WD/FactorialStages"));
        };
        ensure_object(argument, child)?;
        if membership_subject(&source_subject(requirement)?, argument)? != StandardSet::N {
            return Err(LeanCompileError::unsupported("WD/FactorialNaturalDomain"));
        }
        let term = self.compile_wd(
            child,
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let member = self.compile_wd_requirement(
            requirement,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        Ok(format!("(Litex.factorial {term} {member})"))
    }

    pub(in crate::compile_to_lean) fn numeric_factorial_wd(
        &self,
        wd: &ObjWellDefinedProof,
        children: &[Box<ObjWellDefinedProof>],
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let term = self.compile_wd(wd, position)?;
        let setup = format!("let _factorial := {term};\nlet _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);");
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let [child] = children else {
                return Err(LeanCompileError::unsupported("Factorial/ObservationChild"));
            };
            let observation = self.numeric_wd(
                child,
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?;
            let n = observation
                .3
                .as_ref()
                .and_then(EvalRational::to_i128_if_integer)
                .filter(|n| *n >= 0)
                .ok_or_else(|| LeanCompileError::unsupported("Factorial/ClosedNatural"))?;
            let denotation = format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = (({n} : ℕ) : ℂ))))",
                observation.1, observation.0
            );
            let exact = exact_rational_literal(&value, "ℂ")?;
            return Ok((exact, format!("({setup}\n(Litex.factorialDenoteNat _factorial {n} {denotation}).trans (congrArg M.number (by norm_num)))"), format!("({setup}\n_member)"), Some(value)));
        }
        Ok((
            format!("({setup}\nLitex.NativeBridge.asComplex _factorial _member)"),
            format!("({setup}\nLitex.NativeBridge.asComplex_spec _factorial _member)"),
            format!("({setup}\n_member)"),
            None,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_factorial_step(
        &self,
        goal: &EqualFact,
        predecessor: bool,
        requirements: &[&VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [requirement] = requirements else {
            return Err(LeanCompileError::unsupported("Factorial/StepRequirement"));
        };
        for (upper, product, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Some(upper_arg) = factorial_argument(upper) else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = product else {
                continue;
            };
            for (coefficient, lower, first) in [
                (&product.left, &product.right, true),
                (&product.right, &product.left, false),
            ] {
                let Some(lower_arg) = factorial_argument(lower) else {
                    continue;
                };
                let required = if predecessor {
                    if coefficient.ir() != upper_arg.ir() {
                        continue;
                    }
                    let expected = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                        left: Box::new(upper_arg.clone()),
                        right: Box::new(Obj::Literal(Literal::Number(Number::new("1".into())))),
                    }));
                    if !crate::rational_expression::objs_equal_by_rational_expression_evaluation(
                        lower_arg, &expected,
                    ) {
                        continue;
                    }
                    upper_arg
                } else {
                    if !plus_one(upper_arg).is_some_and(|n| n.ir() == lower_arg.ir())
                        || !plus_one(coefficient).is_some_and(|n| n.ir() == lower_arg.ir())
                    {
                        continue;
                    }
                    lower_arg
                };
                if membership_subject(&source_subject(requirement)?, required)?
                    != if predecessor {
                        StandardSet::NPos
                    } else {
                        StandardSet::N
                    }
                {
                    return Err(LeanCompileError::unsupported("Factorial/StepDomain"));
                }
                // This rule's producer normalizes the predecessor argument but
                // records no separate denominator guards. Keep the fixed
                // polynomial adapter; do not reconstruct missing guard proofs.
                if !normalization_nonzero_subjects(upper_arg, lower_arg)?.is_empty()
                    || !normalization_nonzero_subjects(coefficient, upper_arg)?.is_empty()
                {
                    return Err(LeanCompileError::unsupported(
                        "Factorial/GuardedArgumentNormalization",
                    ));
                }
                let domain = self.compile_verify(requirement, position)?;
                let upper_term = self.compile_object_reference(upper, position)?;
                let lower_term = self.compile_object_reference(lower, position)?;
                let coefficient_term = self.compile_object_reference(coefficient, position)?;
                let upper_value = self.compile_numeric_observation(upper_arg, position)?;
                let lower_value = self.compile_numeric_observation(lower_arg, position)?;
                let coefficient_value = self.compile_numeric_observation(coefficient, position)?;
                let symmetric = if reversed { ".symm" } else { "" };
                let target = if first {
                    format!("M.mulValue (Litex.denote {coefficient_term}) (Litex.denote _lower)")
                } else {
                    format!("M.mulValue (Litex.denote _lower) (Litex.denote {coefficient_term})")
                };
                return Ok(format!("(by\n  let _upper := {upper_term}\n  let _lower := {lower_term}\n  have _source_domain : {} := {}\n  let _u_native : ℂ := {}\n  have _u : Litex.denote _upper.val.arg = M.number _u_native := {}\n  let _l_native : ℂ := {}\n  have _l : Litex.denote _lower.val.arg = M.number _l_native := {}\n  let _c_native : ℂ := {}\n  have _c : Litex.denote {coefficient_term} = M.number _c_native := {}\n  have _step : Litex.denote _upper.val.arg = M.addValue (Litex.denote _lower.val.arg) (M.number 1) := by\n    exact _u.trans ((congrArg M.number (by ring! : _u_native = _l_native + 1)).trans (((congrArg (fun _value => M.addValue _value (M.number 1)) _l).trans (M.add_numbers _l_native 1)).symm))\n  have _coefficient : Litex.denote {coefficient_term} = Litex.denote _upper.val.arg := by\n    exact _c.trans ((congrArg M.number (by ring! : _c_native = _u_native)).trans _u.symm)\n  have _result : Litex.denote _upper = {target} := by\n    rw [_coefficient]\n    exact Litex.factorialStep _upper _lower _step {first}\n  exact _result{symmetric}\n)", domain.0, domain.1, upper_value.0, upper_value.1, lower_value.0, lower_value.1, coefficient_value.0, coefficient_value.1));
            }
        }
        Err(LeanCompileError::unsupported("Factorial/StepSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_factorial_nonzero(
        &self,
        goal: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(goal) = goal else {
            return Err(LeanCompileError::unsupported("Factorial/NonzeroSubject"));
        };
        let (object, reverse) =
            if factorial_argument(&goal.left).is_some() && is_exact_zero(&goal.right) {
                (&goal.left, false)
            } else if factorial_argument(&goal.right).is_some() && is_exact_zero(&goal.left) {
                (&goal.right, true)
            } else {
                return Err(LeanCompileError::unsupported("Factorial/NonzeroSubject"));
            };
        let proof = format!(
            "(Litex.factorialNonzero {})",
            self.compile_object_reference(object, position)?
        );
        Ok(if reverse {
            format!("(fun _h => {proof} _h.symm)")
        } else {
            proof
        })
    }

    pub(in crate::compile_to_lean) fn compile_factorial_monotone(
        &self,
        goal: &AtomicFact,
        positive: Option<&VerifyFactResult>,
        argument_order: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (Some(left), Some(right)) = (factorial_argument(low), factorial_argument(high)) else {
            return Err(LeanCompileError::unsupported("Factorial/OrderConstructor"));
        };
        let Fact::AtomicFact(subject) = source_subject(argument_order)? else {
            return Err(LeanCompileError::unsupported("Factorial/OrderPremise"));
        };
        let (a, b, premise_strict) = source_order_oriented(&subject)?;
        if strict != positive.is_some()
            || strict != premise_strict
            || a.ir() != left.ir()
            || b.ir() != right.ir()
        {
            return Err(LeanCompileError::unsupported("Factorial/OrderPremise"));
        }
        let positive_proof = if let Some(positive) = positive {
            if membership_subject(&source_subject(positive)?, left)? != StandardSet::NPos {
                return Err(LeanCompileError::unsupported("Factorial/PositiveSmaller"));
            }
            Some(
                self.compile_verify(positive, &position.atomic_search_prior(0)?)?
                    .1,
            )
        } else {
            None
        };
        let order = self
            .compile_verify(
                argument_order,
                &position.atomic_search_prior(usize::from(strict))?,
            )?
            .1;
        let complete = position.atomic_search_prior(usize::from(strict) + 1)?;
        let p = self.compile_object_reference(low, &complete)?;
        let q = self.compile_object_reference(high, &complete)?;
        Ok(if let Some(positive) = positive_proof {
            format!("(Litex.factorialStrictMonotone {p} {q} {positive} {order})")
        } else {
            format!("(Litex.factorialMonotone {p} {q} {order})")
        })
    }
}
