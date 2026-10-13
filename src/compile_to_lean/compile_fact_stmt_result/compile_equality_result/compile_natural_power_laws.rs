use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_natural_power_product(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (product_object, combined_object, product, combined, reversed) =
            match (&goal.left, &goal.right) {
                (
                    left @ Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
                    right @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(combined)),
                ) => (left, right, product, combined, false),
                (
                    left @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(combined)),
                    right @ Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
                ) => (right, left, product, combined, true),
                _ => return Err(LeanCompileError::new(
                    "NaturalPowerProduct/Constructor",
                    "The selected rule must compare its original product with its combined power.",
                )),
            };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = combined.exponent.as_ref()
        else {
            return Err(LeanCompileError::new(
                "NaturalPowerProduct/Sum",
                "The combined exponent must retain its original sum.",
            ));
        };
        let (base, first, second, header) =
            self.natural_power_law_requirements(requirements, position)?;
        if base.ir() != combined.base.ir() {
            return Err(LeanCompileError::new(
                "NaturalPowerProduct/Base",
                "The actual base-membership child belongs to another common base.",
            ));
        }
        let indices = ordered_exponent_indices(&sum.left, &sum.right, &first, &second)?;
        let combined_value =
            self.natural_exponent_operation_value(&combined.exponent, "add", indices, position)?;
        let left = self.natural_factor_value(&product.left, &base, &first, &second, position)?;
        let right = self.natural_factor_value(&product.right, &base, &first, &second, position)?;
        if first.ir() != second.ir() && left.0 == right.0 {
            return Err(LeanCompileError::new(
                "NaturalPowerProduct/OrderedFactors",
                "The two original factors must consume both recorded exponent subjects.",
            ));
        }
        let combined_term = self.compile_object_reference(combined_object, position)?;
        let product_term = self.compile_object_reference(product_object, position)?;
        let proof = format!("(by\n{header}\n  let _litex_product := {product_term}\n  let _litex_combined := {combined_term}\n  have _litex_combined_exponent : Litex.Same _litex_combined.val.exponent (Litex.number (M := M) (((_litex_n1 + _litex_n2 : ℕ) : ℂ))) := {combined_value}\n  have _litex_factor_left : Litex.denote _litex_product.val.left = M.number (_litex_base_value ^ {}) := {}\n  have _litex_factor_right : Litex.denote _litex_product.val.right = M.number (_litex_base_value ^ {}) := {}\n  exact Litex.NativeBridge.sameOfDenoteNumber _litex_product _litex_combined ((_litex_base_value ^ {}) * (_litex_base_value ^ {})) (_litex_base_value ^ (_litex_n1 + _litex_n2)) (Litex.NativeBridge.denoteMul _litex_product.val.left _litex_product.val.right _litex_product.wd.1 _litex_product.wd.2 _ _ _litex_factor_left _litex_factor_right) (Litex.NativeBridge.denotePowStructuralNat _litex_combined (_litex_n1 + _litex_n2) _litex_combined_exponent _litex_base_value _litex_base_denote) (by rw [pow_add]; ring)\n)", left.0, left.1, right.0, right.1, left.0, right.0);
        Ok(if reversed {
            format!("(Eq.symm {proof})")
        } else {
            proof
        })
    }

    pub(in crate::compile_to_lean) fn compile_natural_power_of_power(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (nested_object, combined_object, nested, combined, reversed) =
            match (&goal.left, &goal.right) {
                (
                    left @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(nested)),
                    right @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(combined)),
                ) if matches!(
                    nested.base.as_ref(),
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(_))
                ) =>
                {
                    (left, right, nested, combined, false)
                }
                (
                    left @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(combined)),
                    right @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(nested)),
                ) if matches!(
                    nested.base.as_ref(),
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(_))
                ) =>
                {
                    (right, left, nested, combined, true)
                }
                _ => {
                    return Err(LeanCompileError::new(
                        "NaturalPowerOfPower/Constructor",
                        "The selected rule must retain its nested and combined source powers.",
                    ))
                }
            };
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(inner)) = nested.base.as_ref() else {
            unreachable!()
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = combined.exponent.as_ref()
        else {
            return Err(LeanCompileError::new(
                "NaturalPowerOfPower/Product",
                "The combined exponent must retain its original product.",
            ));
        };
        let (base, first, second, header) =
            self.natural_power_law_requirements(requirements, position)?;
        if base.ir() != inner.base.ir()
            || base.ir() != combined.base.ir()
            || first.ir() != inner.exponent.ir()
            || second.ir() != nested.exponent.ir()
        {
            return Err(LeanCompileError::new("NaturalPowerOfPower/Children", "The original ordered requirements must name this exact base, inner exponent and outer exponent."));
        }
        let indices = ordered_exponent_indices(&product.left, &product.right, &first, &second)?;
        let combined_value =
            self.natural_exponent_operation_value(&combined.exponent, "mul", indices, position)?;
        let proof = format!("(by\n{header}\n  let _litex_nested := {}\n  let _litex_combined := {}\n  have _litex_combined_exponent : Litex.Same _litex_combined.val.exponent (Litex.number (M := M) (((_litex_n1 * _litex_n2 : ℕ) : ℂ))) := {combined_value}\n  have _litex_inner_denote : Litex.denote _litex_nested.val.base = M.number (_litex_base_value ^ _litex_n1) := Litex.NativeBridge.denotePowStructuralNat _litex_nested.val.base _litex_n1 _litex_exp1 _litex_base_value _litex_base_denote\n  exact Litex.NativeBridge.sameOfDenoteNumber _litex_nested _litex_combined ((_litex_base_value ^ _litex_n1) ^ _litex_n2) (_litex_base_value ^ (_litex_n1 * _litex_n2)) (Litex.NativeBridge.denotePowStructuralNat _litex_nested _litex_n2 _litex_exp2 (_litex_base_value ^ _litex_n1) _litex_inner_denote) (Litex.NativeBridge.denotePowStructuralNat _litex_combined (_litex_n1 * _litex_n2) _litex_combined_exponent _litex_base_value _litex_base_denote) (pow_mul _litex_base_value _litex_n1 _litex_n2).symm\n)", self.compile_object_reference(nested_object, position)?, self.compile_object_reference(combined_object, position)?);
        Ok(if reversed {
            format!("(Eq.symm {proof})")
        } else {
            proof
        })
    }

    fn natural_power_law_requirements(
        &self,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<(Obj, Obj, Obj, String), LeanCompileError> {
        if requirements.len() != 3 {
            return Err(LeanCompileError::new("NaturalPowerLaw/Requirements", "The selected power law needs its original base and two ordered natural-exponent results."));
        }
        let mut objects = Vec::new();
        let mut proofs = Vec::new();
        for (requirement, set) in
            requirements
                .iter()
                .zip([StandardSet::C, StandardSet::N, StandardSet::N])
        {
            let Fact::AtomicFact(AtomicFact::InFact(member)) = source_subject(requirement)? else {
                return Err(LeanCompileError::new(
                    "NaturalPowerLaw/RequirementFamily",
                    "An original power-law child is not an atomic membership.",
                ));
            };
            if member.set != Obj::StandardSet(set) {
                return Err(LeanCompileError::new(
                    "NaturalPowerLaw/RequirementCarrier",
                    "The original ordered power-law memberships have changed their carriers.",
                ));
            }
            objects.push(member.element);
            proofs.push(self.compile_verify(requirement, position)?.1);
        }
        let base = self.compile_object_reference(&objects[0], position)?;
        let first = self.compile_object_reference(&objects[1], position)?;
        let second = self.compile_object_reference(&objects[2], position)?;
        let header = format!("  have _litex_base_complex : Litex.In {base} (Litex.C (M := M)) := {}\n  have _litex_first_natural : Litex.In {first} (Litex.N (M := M)) := {}\n  have _litex_second_natural : Litex.In {second} (Litex.N (M := M)) := {}\n  let _litex_base_value : ℂ := Litex.NativeBridge.asComplex {base} _litex_base_complex\n  have _litex_base_denote : Litex.denote {base} = M.number _litex_base_value := Litex.NativeBridge.asComplex_spec {base} _litex_base_complex\n  let _litex_n1 : ℕ := Litex.NativeBridge.asNat {first} _litex_first_natural\n  let _litex_n2 : ℕ := Litex.NativeBridge.asNat {second} _litex_second_natural\n  have _litex_exp1 : Litex.Same {first} (Litex.number (M := M) (_litex_n1 : ℂ)) := Litex.NativeBridge.asNat_spec {first} _litex_first_natural\n  have _litex_exp2 : Litex.Same {second} (Litex.number (M := M) (_litex_n2 : ℂ)) := Litex.NativeBridge.asNat_spec {second} _litex_second_natural", proofs[0], proofs[1], proofs[2]);
        Ok((
            objects.remove(0),
            objects.remove(0),
            objects.remove(0),
            header,
        ))
    }

    fn natural_exponent_operation_value(
        &self,
        object: &Obj,
        operation: &str,
        indices: (usize, usize),
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let term = self.compile_object_reference(object, position)?;
        Ok(format!("(by\n    let _litex_exponent := {term}\n    change M.{operation}Value (Litex.denote _litex_exponent.val.left) (Litex.denote _litex_exponent.val.right) = _\n    have _litex_first_value := _litex_exp{}\n    have _litex_second_value := _litex_exp{}\n    change Litex.denote _litex_exponent.val.left = M.number (_litex_n{} : ℂ) at _litex_first_value\n    change Litex.denote _litex_exponent.val.right = M.number (_litex_n{} : ℂ) at _litex_second_value\n    rw [_litex_first_value, _litex_second_value, M.{operation}_numbers]\n    congr 1\n    push_cast\n    ring)", indices.0, indices.1, indices.0, indices.1))
    }

    fn natural_factor_value(
        &self,
        object: &Obj,
        base: &Obj,
        first: &Obj,
        second: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = object {
            if power.base.ir() != base.ir() {
                return Err(LeanCompileError::new(
                    "NaturalPowerProduct/FactorBase",
                    "The original factor has another common base.",
                ));
            }
            let index = if power.exponent.ir() == first.ir() {
                1
            } else if power.exponent.ir() == second.ir() {
                2
            } else {
                return Err(LeanCompileError::new(
                    "NaturalPowerProduct/FactorExponent",
                    "The original factor has another recorded exponent.",
                ));
            };
            return Ok((format!("_litex_n{index}"), format!("(Litex.NativeBridge.denotePowStructuralNat {} _litex_n{index} _litex_exp{index} _litex_base_value _litex_base_denote)", self.compile_object_reference(object, position)?)));
        }
        if object.ir() != base.ir() {
            return Err(LeanCompileError::new(
                "NaturalPowerProduct/BareFactor",
                "The original bare factor must be the exact recorded common base.",
            ));
        }
        let index = if matches!(first, Obj::Literal(Literal::Number(_)))
            && closed_integer(first) == Some(1)
        {
            1
        } else if matches!(second, Obj::Literal(Literal::Number(_)))
            && closed_integer(second) == Some(1)
        {
            2
        } else {
            return Err(LeanCompileError::new(
                "NaturalPowerProduct/BareExponent",
                "The original bare factor needs its recorded exact literal exponent one.",
            ));
        };
        let exponent = if index == 1 { first } else { second };
        let one = self.compile_literal_natural_identity(exponent, 1, position)?;
        Ok((format!("_litex_n{index}"), format!("(by\n    have _litex_one : _litex_n{index} = 1 := Litex.NativeBridge.asNat_ofDenote {} _litex_{}_natural 1 {one}\n    simpa only [_litex_one, pow_one] using _litex_base_denote)", self.compile_object_reference(exponent, position)?, if index == 1 { "first" } else { "second" })))
    }
}

fn ordered_exponent_indices(
    left: &Obj,
    right: &Obj,
    first: &Obj,
    second: &Obj,
) -> Result<(usize, usize), LeanCompileError> {
    if left.ir() == first.ir() && right.ir() == second.ir() {
        Ok((1, 2))
    } else if left.ir() == second.ir() && right.ir() == first.ir() {
        Ok((2, 1))
    } else {
        Err(LeanCompileError::new(
            "NaturalPowerLaw/ExponentOperation",
            "The original combined operation changes its two recorded natural exponents.",
        ))
    }
}
