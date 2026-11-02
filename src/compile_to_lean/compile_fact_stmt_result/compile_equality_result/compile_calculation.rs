use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

enum NumericNormalization {
    Polynomial,
    GuardedRational,
    GuardedComplex,
}

fn validate_closed_rational_pair(
    values: &ClosedValuePair,
    left: &EvalRational,
    right: &EvalRational,
) -> Result<(), LeanCompileError> {
    let matching = match values {
        ClosedValuePair::Decimal { left: a, right: b } => {
            scalar_decimal(a)? == *left && scalar_decimal(b)? == *right
        }
        ClosedValuePair::Rational { left: a, right: b } => a == left && b == right,
        ClosedValuePair::Complex {
            left_real: a,
            left_imaginary: ai,
            right_real: b,
            right_imaginary: bi,
        } => a == left && b == right && ai.is_zero() && bi.is_zero(),
        ClosedValuePair::Radical { .. } => {
            return Err(LeanCompileError::unsupported("ClosedEquality/Radical"))
        }
    };
    if !matching || left != right {
        return Err(LeanCompileError::new(
            "ClosedEquality/Values",
            "Closed equality values differ from their exact source endpoints or from each other.",
        ));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    /// Normalize a selected arithmetic alignment using only the guards of its
    /// original constructors. A cached object still resolves to that constructor;
    /// this does not search for a new nonzero proof in the final environment.
    pub(in crate::compile_to_lean) fn compile_formation_normalization(
        &self,
        objects: &[&Obj],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        fn collect<'a>(object: &'a Obj, guards: &mut Vec<(&'a Obj, &'a Obj)>) {
            if EvalRational::from_obj(object).is_some() {
                // The numeric observer checks the original closed certificate.
                // Its native value has no symbolic denominator to discharge.
                return;
            }
            let guard = match object {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
                    collect(&p.left, guards);
                    collect(&p.right, guards);
                    None
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
                    collect(&p.left, guards);
                    collect(&p.right, guards);
                    None
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                    collect(&p.left, guards);
                    collect(&p.right, guards);
                    None
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
                    collect(&p.left, guards);
                    collect(&p.right, guards);
                    Some(p.right.as_ref())
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => {
                    collect(&p.arg, guards);
                    None
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
                    collect(&p.base, guards);
                    closed_integer(&p.exponent)
                        .filter(|n| *n < 0)
                        .map(|_| p.base.as_ref())
                }
                _ => None,
            };
            if let Some(subject) = guard {
                if !guards
                    .iter()
                    .any(|(_, previous)| previous.ir() == subject.ir())
                {
                    guards.push((object, subject));
                }
            }
        }
        let mut guards = Vec::new();
        for object in objects {
            collect(object, &mut guards);
        }
        if guards.is_empty() {
            return Ok("by ring!".into());
        }
        let mut declarations = Vec::new();
        let mut names = Vec::new();
        for (index, (owner, subject)) in guards.into_iter().enumerate() {
            let proof = position
                .with_visible_wd(owner, &mut |wd, producer| {
                    ensure_object(owner, wd)?;
                    // Validate every child and domain stage before projecting the
                    // exact requirement. Merely finding a similarly shaped WD is
                    // not enough to justify its nonzero conclusion.
                    self.compile_wd(wd, producer)?;
                    let (requirements, slot) = match wd.detailed_ref() {
                        DetailedObjWellDefinedProof::ByDef {
                            proof:
                                ObjWellDefinedProofByDef::ArithmeticOperator(
                                    ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                                ),
                            ..
                        } => (&p.requirement_fact_verified, 0),
                        DetailedObjWellDefinedProof::ByDef {
                            proof:
                                ObjWellDefinedProofByDef::ArithmeticOperator(
                                    ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                                ),
                            ..
                        } => (&p.requirement_fact_verified, 2),
                        _ => {
                            return Err(LeanCompileError::unsupported(
                                "Normalization/GuardConstructor",
                            ))
                        }
                    };
                    let guard = requirements.get(slot).ok_or_else(|| {
                        LeanCompileError::unsupported("Normalization/OriginalGuard")
                    })?;
                    ensure_nonzero_subject(&source_subject(guard)?, subject)?;
                    let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 2 + slot);
                    self.compile_wd_requirement(guard, &scope)
                })?
                .ok_or_else(|| LeanCompileError::unsupported("Normalization/GuardWD"))?;
            let term = self.compile_object_reference(subject, position)?;
            let native = self.compile_numeric_observation(subject, position)?;
            let name = format!("_litex_nz_{index}");
            declarations.push(format!("have {name} : ({} : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote {term} {} {} {proof}", native.0, native.0, native.1));
            let mut factors = vec![(subject, name)];
            while let Some((factor, name)) = factors.pop() {
                names.push(name.clone());
                let (left, right, law) = match factor {
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                        (&p.left, &p.right, "mul_ne_zero_iff")
                    }
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
                        (&p.left, &p.right, "div_ne_zero_iff")
                    }
                    _ => continue,
                };
                for (part, field, child) in [(left, "1", "left"), (right, "2", "right")] {
                    let child_name = format!("{name}_{child}");
                    declarations.push(format!("have {child_name} := ({law}.mp {name}).{field}"));
                    factors.push((part, child_name));
                }
            }
        }
        let exact = names
            .iter()
            .map(|name| format!("exact {name}"))
            .collect::<Vec<_>>()
            .join(" | ");
        Ok(format!("(by\n  {}\n  litex_normalize_rational (disch := repeat' first | {exact} | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)\n)", declarations.join("\n  ")))
    }

    /// A checked beta endpoint has a raw semantic value but is not a new WD
    /// producer. Replay its closed arithmetic certificate at that value.
    pub(super) fn compile_parent_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &ClosedEqualityCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, left_proof) = self.compile_eval_closed_value(&fact.left, position)?;
        let (right, right_proof) = self.compile_eval_closed_value(&fact.right, position)?;
        validate_closed_rational_pair(&proof.values, &left, &right)?;
        Ok(format!("(({left_proof}).trans ({right_proof}).symm)"))
    }

    pub(in crate::compile_to_lean) fn compile_builtin_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &EqualitySearchProofByCalculation,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let values = match proof {
            EqualitySearchProofByCalculation::ClosedDecimal {
                left_normal,
                right_normal,
            } => ClosedValuePair::Decimal {
                left: left_normal.clone(),
                right: right_normal.clone(),
            },
            EqualitySearchProofByCalculation::ClosedRational {
                left_normal,
                right_normal,
            } => {
                let left = self
                    .compile_numeric_observation(&fact.left, position)?
                    .3
                    .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
                let right = self
                    .compile_numeric_observation(&fact.right, position)?
                    .3
                    .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
                if left.to_obj().readable_string() != *left_normal
                    || right.to_obj().readable_string() != *right_normal
                {
                    return Err(LeanCompileError::unsupported("ClosedEquality/NormalForms"));
                }
                ClosedValuePair::Rational { left, right }
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "ClosedEquality/BuiltinFamily",
                ))
            }
        };
        self.compile_closed_equality(fact, &ClosedEqualityCalculationProof { values }, position)
    }

    pub(in crate::compile_to_lean) fn compile_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &ClosedEqualityCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if matches!(proof.values, ClosedValuePair::Complex { .. }) {
            return self.compile_closed_complex_relation(
                &fact.left,
                &fact.right,
                &proof.values,
                true,
                position,
            );
        }
        let left = self
            .compile_numeric_observation(&fact.left, position)?
            .3
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let right = self
            .compile_numeric_observation(&fact.right, position)?
            .3
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        validate_closed_rational_pair(&proof.values, &left, &right)?;
        let x = self.compile_numeric_observation(&fact.left, position)?;
        let y = self.compile_numeric_observation(&fact.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }

    pub(in crate::compile_to_lean) fn compile_scalar_division_relation(
        &self,
        fact: &EqualFact,
        proof: &ScalarDivisionRelationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (child, product_from_division) = match proof {
            ScalarDivisionRelationProof::ProductFromDivision(p) => (&p.division_equation, true),
            ScalarDivisionRelationProof::DivisionFromProduct(p) => (&p.product_equation, false),
        };
        let compiled = self.compile_verify(child, position)?;
        let source_equation = source_subject(child)?;
        let equation = match &source_equation {
            Fact::AtomicFact(AtomicFact::EqualFact(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ScalarDivisionRelation/Child",
                    "The source equation is not an equality.",
                ))
            }
        };
        let (_numerator, _denominator, _factor, quotient, reversed, commuted) =
            if product_from_division {
                let quotient = match &equation.left {
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "ScalarDivisionRelation/DivisionSubject",
                            "ProductFromDivision must cite a quotient equation.",
                        ))
                    }
                };
                let mut matched = None;
                for (other, product, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = product {
                        if other.ir() != quotient.left.ir() {
                            continue;
                        }
                        if p.left.ir() == equation.right.ir() && p.right.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, false));
                            break;
                        }
                        if p.right.ir() == equation.right.ir() && p.left.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, true));
                            break;
                        }
                    }
                }
                let (reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source quotient equation does not describe the parent product endpoints."))?;
                (
                    quotient.left.as_ref(),
                    quotient.right.as_ref(),
                    &equation.right,
                    &equation.left,
                    reversed,
                    commuted,
                )
            } else {
                let mut matched = None;
                for (quotient_obj, factor, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(q)) = quotient_obj {
                        if equation.left.ir() != q.left.ir() {
                            continue;
                        }
                        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = &equation.right
                        {
                            if p.left.ir() == factor.ir() && p.right.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, false));
                                break;
                            }
                            if p.right.ir() == factor.ir() && p.left.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, true));
                                break;
                            }
                        }
                    }
                }
                let (q, factor, quotient_obj, reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source product equation does not describe the parent quotient endpoints."))?;
                (
                    q.left.as_ref(),
                    q.right.as_ref(),
                    factor,
                    quotient_obj,
                    reversed,
                    commuted,
                )
            };
        // The checked child has now formed its exact endpoints. Its WD is
        // available to the conversion, without publishing its equality truth.
        let checked_child =
            SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let position = &checked_child;
        let product = if product_from_division {
            if reversed {
                &fact.left
            } else {
                &fact.right
            }
        } else {
            &equation.right
        };
        let quotient = self.compile_object_reference(quotient, position)?;
        let product = self.compile_object_reference(product, position)?;
        let factor_field = if commuted { "right" } else { "left" };
        let member_field = if commuted { "2" } else { "1" };
        let commute = if commuted {
            "(Litex.sameMulComm _product.val.left _product.val.right _product.wd.1 _product.wd.2)"
        } else {
            ""
        };
        let converted = if product_from_division {
            if commuted {
                format!("((_conversion.mp _child).trans {commute}.symm)")
            } else {
                "(_conversion.mp _child)".to_string()
            }
        } else if commuted {
            format!("(_conversion.mpr (_child.trans {commute}))")
        } else {
            "(_conversion.mpr _child)".to_string()
        };
        let converted = if reversed {
            format!("({converted}.symm)")
        } else {
            converted
        };
        Ok(format!("(by\n  let _quotient := {}\n  let _product := {}\n  have _child : {} := {}\n  have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.{factor_field} _quotient.wd.1 _quotient.wd.2.1 _product.wd.{member_field} _quotient.wd.2.2\n  exact {converted})",
            quotient.replace('\n', "\n  "), product.replace('\n', "\n  "), compiled.0.replace('\n', "\n  "), compiled.1.replace('\n', "\n  ")))
    }

    pub(in crate::compile_to_lean) fn compile_rational(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        guarded: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_numeric_normalization(
            fact,
            requirements,
            proofs,
            if guarded {
                NumericNormalization::GuardedRational
            } else {
                NumericNormalization::Polynomial
            },
            position,
        )
    }

    pub(super) fn compile_guarded_complex(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !crate::rational_expression::contains_imaginary_unit(&fact.left)
            && !crate::rational_expression::contains_imaginary_unit(&fact.right)
        {
            return Err(LeanCompileError::unsupported(
                "ComplexNormalization/Subject",
            ));
        }
        self.compile_numeric_normalization(
            fact,
            requirements,
            proofs,
            NumericNormalization::GuardedComplex,
            position,
        )
    }

    fn compile_numeric_normalization(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        mode: NumericNormalization,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let guarded = !matches!(mode, NumericNormalization::Polynomial);
        let complex = matches!(mode, NumericNormalization::GuardedComplex);
        let route = if complex {
            "ComplexNormalization"
        } else {
            "Rational"
        };
        validate_arithmetic_expression(&fact.left)?;
        validate_arithmetic_expression(&fact.right)?;
        let expected = if complex {
            crate::rational_expression::algebraic_normalization_nonzero_requirements(
                &fact.left,
                &fact.right,
            )
        } else {
            normalization_nonzero_subjects(&fact.left, &fact.right)?
        };
        if requirements.len() != expected.len()
            || proofs.len() != expected.len()
            || guarded != !expected.is_empty()
        {
            return Err(LeanCompileError::new(&format!("{route}/Requirements"), "The selected normalization family or ordered guard arity differs from the source expression."));
        }
        let mut native_guards = Vec::new();
        let mut guard_names = Vec::new();
        for (index, ((requirement, proof), object)) in
            requirements.iter().zip(proofs).zip(expected).enumerate()
        {
            ensure_nonzero_subject(requirement, &object)?;
            let proved = self.compile_verify(proof, position)?;
            if &source_subject(proof)? != requirement {
                return Err(LeanCompileError::new(
                    &format!("{route}/RequirementSubject"),
                    "A guard's verify result differs from its exact ordered requirement.",
                ));
            }
            let term = self.compile_object_reference(&object, position)?;
            let native = self.compile_numeric_observation(&object, position)?;
            // A tactic-valued observation needs its expected scalar type before
            // elaborating the zero in this standalone nonzero proposition.
            native_guards.push(format!("have _litex_nz_{index} : ({} : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote {term} {} {} {}", native.0, native.0, native.1, proved.1));
            let mut factors = vec![(&object, format!("_litex_nz_{index}"))];
            while let Some((object, name)) = factors.pop() {
                if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = object {
                    if complex {
                        let left = format!("{name}_left");
                        let right = format!("{name}_right");
                        native_guards.push(format!("have {left} := (mul_ne_zero_iff.mp {name}).1"));
                        native_guards
                            .push(format!("have {right} := (mul_ne_zero_iff.mp {name}).2"));
                        factors.push((&product.right, right));
                        factors.push((&product.left, left));
                        continue;
                    }
                }
                guard_names.push(name);
            }
        }
        let x = self.compile_numeric_observation(&fact.left, position)?;
        let y = self.compile_numeric_observation(&fact.right, position)?;
        // The empty Rational tag contains no monomial trace. The Lean kernel
        // checks the fixed normalization proof, including forged false tags.
        let normalization = if guarded {
            let exact_guards = guard_names
                .iter()
                .map(|n| format!("exact {n}"))
                .collect::<Vec<_>>()
                .join(" | ");
            let discharger = format!("(disch := repeat' first | {exact_guards} | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)");
            if complex {
                format!(
                    "(by\n  {}\n  litex_normalize_guarded_complex {discharger}\n)",
                    native_guards.join("\n  ")
                )
            } else {
                format!(
                    "(by\n  {}\n  litex_normalize_rational {discharger}\n)",
                    native_guards.join("\n  ")
                )
            }
        } else {
            // The same source atom can occur through different projections of
            // certified objects. Compare those definitions at default transparency.
            "(by ring!)".to_string()
        };
        Ok(format!(
            // Endpoint WD was checked by the equality dispatcher. The exact
            // denotation certificates determine these same two objects.
            "(Litex.NativeBridge.sameOfDenoteNumber _ _ {} {} {} {} {normalization})",
            x.0, y.0, x.1, y.1
        ))
    }
}
