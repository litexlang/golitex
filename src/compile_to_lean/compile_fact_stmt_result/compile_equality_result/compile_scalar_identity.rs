use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_min_max::min_max_arguments;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof as Rule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_scalar_identity(
        &self,
        fact: &EqualFact,
        rule: &Rule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match rule {
            Rule::SignZeroReflection(p) => self.compile_scalar_zero_reflection(
                fact,
                false,
                &p.real_proof,
                &p.premise_proof,
                position,
            ),
            Rule::AbsZeroArgument(p) => self.compile_scalar_zero_reflection(
                fact,
                true,
                &p.real_proof,
                &p.premise_proof,
                position,
            ),
            Rule::AbsDifferenceSymmetry(_) => self.compile_abs_difference_symmetry(fact, position),
            Rule::FloorNegation(_) => self.compile_rounding_negation(fact, false, position),
            Rule::CeilNegation(_) => self.compile_rounding_negation(fact, true, position),
            Rule::FloorIntegerTranslation(p) => {
                self.compile_rounding_integer_translation(fact, false, &p.integer_proof, position)
            }
            Rule::CeilIntegerTranslation(p) => {
                self.compile_rounding_integer_translation(fact, true, &p.integer_proof, position)
            }
            Rule::MinMaxAbsorption(_) => self.compile_min_max_absorption(fact, false, position),
            Rule::MaxMinAbsorption(_) => self.compile_min_max_absorption(fact, true, position),
            Rule::LcmZero(_) => self.compile_lcm_zero(fact, position),
            _ => Err(invalid("Variant")),
        }
    }

    fn compile_scalar_zero_reflection(
        &self,
        fact: &EqualFact,
        absolute: bool,
        real: &VerifyFactResult,
        premise: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (value, zero, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if !is_exact_zero(zero) {
                continue;
            }
            if membership_subject(&source_subject(real)?, value)? != StandardSet::R {
                return Err(invalid("ZeroReflectionRealSubject"));
            }
            let children = std::slice::from_ref(real);
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                0,
            );
            let real_proof = self.compile_verify(real, &prior)?.1;
            let complete = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                1,
            );
            let property = if absolute {
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
                    arg: Box::new(value.clone()),
                }))
            } else {
                Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
                    arg: Box::new(value.clone()),
                }))
            };
            // AbsZeroArgument searches the fixed literal-zero property. Sign
            // reflection searches the original goal's zero endpoint instead.
            // This borrowed obligation introduces no WD result, store or search.
            let property_zero = if absolute {
                Obj::Literal(Literal::Number(Number::new("0".into())))
            } else {
                zero.clone()
            };
            let view = EqualFact {
                fact_id: fact.fact_id,
                left: property,
                right: property_zero.clone(),
                line_file: fact.line_file.clone(),
            };
            let property_proof = self.compile_equality_search(&view, premise, &complete)?;
            let property_zero = self.compile_scalar_identity_zero(&property_zero, &complete)?;
            let value = self.compile_object_reference(value, position)?;
            let goal_zero = self.compile_scalar_identity_zero(zero, position)?;
            let law = if absolute {
                "absoluteZeroReflectionValue"
            } else {
                "signZeroReflectionValue"
            };
            return Ok(format!("((Litex.{law} {value} {real_proof} (({property_proof}).trans {property_zero})).trans ({goal_zero}).symm){}", if reverse { ".symm" } else { "" }));
        }
        Err(invalid("ZeroReflectionEndpoints"))
    }

    fn compile_abs_difference_symmetry(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(b)),
        ) = (&fact.left, &fact.right)
        else {
            return Err(invalid("AbsoluteShape"));
        };
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(b)),
        ) = (a.arg.as_ref(), b.arg.as_ref())
        else {
            return Err(invalid("DifferenceShape"));
        };
        if a.left.ir() != b.right.ir() || a.right.ir() != b.left.ir() {
            return Err(invalid("DifferenceEndpoints"));
        }
        Ok(format!(
            "(Litex.absDifferenceSymmetryValue {}).symm",
            self.compile_object_reference(&fact.left, position)?
        ))
    }

    fn compile_rounding_negation(
        &self,
        fact: &EqualFact,
        ceiling: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (rounded, negative, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some(input) = rounding_arg(rounded, ceiling) else {
                continue;
            };
            let (Some(x), Some(opposite)) = (negative_arg(input), negative_arg(negative)) else {
                continue;
            };
            if !rounding_arg(opposite, !ceiling).is_some_and(|y| y.ir() == x.ir()) {
                continue;
            }
            let term = self.compile_object_reference(opposite, position)?;
            let input_eq = self.compile_negated_value(
                input,
                "_round.val.arg",
                "(Litex.realToComplex _round.val.arg _round.wd)",
                position,
            )?;
            let output_eq = self.compile_negated_value(
                negative,
                "_round",
                "(Litex.integerToComplex _round (Litex.roundingInZ _round))",
                position,
            )?;
            return Ok(format!("(by\n  let _round := {term}\n  exact (((congrArg (Litex.roundingValue (M := M) {ceiling}) {input_eq}).trans (Litex.roundingNegationValue {ceiling} (Litex.denote _round.val.arg) _round.wd)).trans ({output_eq}).symm){}\n)", if reverse { ".symm" } else { "" }));
        }
        Err(invalid("RoundingNegationEndpoints"))
    }

    fn compile_rounding_integer_translation(
        &self,
        fact: &EqualFact,
        ceiling: bool,
        integer: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (rounded, translated, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some(Obj::ArithmeticOperator(ArithmeticOperator::Add(input))) =
                rounding_arg(rounded, ceiling)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(output)) = translated else {
                continue;
            };
            for (round, n, reverse_output) in [
                (&output.left, &output.right, false),
                (&output.right, &output.left, true),
            ] {
                let Some(x) = rounding_arg(round, ceiling) else {
                    continue;
                };
                let reverse_input = if input.left.ir() == x.ir() && input.right.ir() == n.ir() {
                    false
                } else if input.right.ir() == x.ir() && input.left.ir() == n.ir() {
                    true
                } else {
                    continue;
                };
                if !matches!(source_subject(integer)?, Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==n.ir() && p.set==Obj::StandardSet(StandardSet::Z))
                {
                    return Err(invalid("TranslationIntegerSubject"));
                }
                let scope = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(std::slice::from_ref(integer)),
                    0,
                );
                let integer_proof = self.compile_verify(integer, &scope)?.1;
                let round = self.compile_object_reference(round, position)?;
                let n = self.compile_object_reference(n, position)?;
                return Ok(format!("(by\n  let _round := {round}\n  exact (Litex.roundingIntegerTranslationValue {ceiling} (Litex.denote _round.val.arg) (Litex.denote {n}) _round.wd {integer_proof} {reverse_input} {reverse_output}){}\n)",if reverse { ".symm" } else { "" }));
            }
        }
        Err(invalid("TranslationEndpoints"))
    }

    fn compile_min_max_absorption(
        &self,
        fact: &EqualFact,
        maximum: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (outer, plain, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((left, right)) = min_max_arguments(outer, maximum) else {
                continue;
            };
            for (arg, nested, reverse_outer) in [(left, right, false), (right, left, true)] {
                if arg.ir() != plain.ir() {
                    continue;
                }
                let Some((a, b)) = min_max_arguments(nested, !maximum) else {
                    continue;
                };
                let reverse_inner = if a.ir() == plain.ir() {
                    false
                } else if b.ir() == plain.ir() {
                    true
                } else {
                    continue;
                };
                let (a, b, ha, hb) = if reverse_inner {
                    (
                        "_nested.val.right",
                        "_nested.val.left",
                        "_nested.wd.2",
                        "_nested.wd.1",
                    )
                } else {
                    (
                        "_nested.val.left",
                        "_nested.val.right",
                        "_nested.wd.1",
                        "_nested.wd.2",
                    )
                };
                let nested = self.compile_object_reference(nested, position)?;
                return Ok(format!("(by\n  let _nested := {nested}\n  exact (Litex.minMaxAbsorptionValue {maximum} (Litex.denote {a}) (Litex.denote {b}) {ha} {hb} {reverse_outer} {reverse_inner}){}\n)",if reverse { ".symm" } else { "" }));
            }
        }
        Err(invalid("AbsorptionEndpoints"))
    }

    fn compile_lcm_zero(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (lcm, zero, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::IntegerOperator(IntegerOperator::Lcm(p)) = lcm else {
                continue;
            };
            if !is_exact_zero(zero) {
                continue;
            }
            let (arg, constructor) = if is_exact_zero(&p.left) {
                (p.left.as_ref(), "Or.inl")
            } else if is_exact_zero(&p.right) {
                (p.right.as_ref(), "Or.inr")
            } else {
                continue;
            };
            let arg_zero = self.compile_scalar_identity_zero(arg, position)?;
            let result_zero = self.compile_scalar_identity_zero(zero, position)?;
            let lcm = self.compile_object_reference(lcm, position)?;
            return Ok(format!("(by\n  let _lcm := {lcm}\n  exact ((Litex.lcmZeroValue (Litex.denote _lcm.val.left) (Litex.denote _lcm.val.right) _lcm.wd.1 _lcm.wd.2 ({constructor} {arg_zero})).trans ({result_zero}).symm){}\n)",if reverse { ".symm" } else { "" }));
        }
        Err(invalid("LcmZeroEndpoints"))
    }

    fn compile_scalar_identity_zero(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !is_exact_zero(object) {
            return Err(invalid("ZeroValue"));
        }
        let term = self.compile_object_reference(object, position)?;
        let observed = self.compile_numeric_observation(object, position)?;
        Ok(format!("(show Litex.denote {term} = M.number (0 : ℂ) from (({}).trans (congrArg M.number (by norm_num : {} = (0 : ℂ)))))", observed.1, observed.0))
    }
}

fn rounding_arg(object: &Obj, ceiling: bool) -> Option<&Obj> {
    match (object, ceiling) {
        (Obj::ArithmeticOperator(ArithmeticOperator::Floor(p)), false) => Some(&p.arg),
        (Obj::ArithmeticOperator(ArithmeticOperator::Ceil(p)), true) => Some(&p.arg),
        _ => None,
    }
}
fn negative_arg(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => Some(&p.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if is_exact_zero(&p.left) => {
            Some(&p.right)
        }
        _ => None,
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ScalarIdentity/{part}"))
}
