use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::prelude::{
    OrFactSearchProofByBuiltinRule, OrFactSearchedProof, OrFactWellDefinedProof, VerifyOrFactResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_or_result(
        &self,
        result: &VerifyOrFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyOrFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Or/Failed"));
        };
        self.compile_or_wd(&proof.fact, &proof.well_defined_proof, position)?;
        let formed = SourcePosition {
            before: proof.fact.facts.len(),
            ..*position
        };
        let position = &formed;
        let fact = Fact::OrFact(proof.fact.clone());
        let term = match &proof.searched_proof {
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::ClosedIntegerRangeEqualityCover(p),
            ) => self.compile_integer_range_cover(
                &proof.fact,
                &p.subject,
                &p.interval,
                &p.membership,
                &p.carrier_equal,
                &p.branch_indices,
                true,
                position,
            )?,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::HalfOpenIntegerRangeEqualityCover(p),
            ) => self.compile_integer_range_cover(
                &proof.fact,
                &p.subject,
                &p.interval,
                &p.membership,
                &p.carrier_equal,
                &p.branch_indices,
                false,
                position,
            )?,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::ComplementaryAtomic(selected),
            ) => {
                let [AndChainAtomicFact::AtomicFact(left), AndChainAtomicFact::AtomicFact(right)] =
                    proof.fact.facts.as_slice()
                else {
                    return Err(LeanCompileError::unsupported("Or/ComplementaryShape"));
                };
                if left != &selected.left || right != &selected.right {
                    return Err(LeanCompileError::new(
                        "Or/ComplementarySubject",
                        "The complementary certificate differs from the original ordered branches.",
                    ));
                }
                let negative = crate::compile_to_lean::compile_by_stmt_result::compile_by_contra_stmt_result::validate_atomic_negation(
                    &Fact::AtomicFact(left.clone()), &Fact::AtomicFact(right.clone()))?;
                if negative {
                    format!(
                        "(Or.symm (Classical.em ({})))",
                        self.atomic_proposition(right, position)?
                    )
                } else {
                    format!(
                        "(Classical.em ({}))",
                        self.atomic_proposition(left, position)?
                    )
                }
            }
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::LessOrGreaterEqual(p),
            ) => self.compile_real_order_split(
                &proof.fact,
                &p.left,
                &p.right,
                &p.left_in_r,
                &p.right_in_r,
                false,
                position,
            )?,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::GreaterOrLessEqual(p),
            ) => self.compile_real_order_split(
                &proof.fact,
                &p.left,
                &p.right,
                &p.left_in_r,
                &p.right_in_r,
                true,
                position,
            )?,
            OrFactSearchedProof::ByKnownOrFact(known) => {
                return self.compile_known_or_fact(&proof.fact, known, position)
            }
            OrFactSearchedProof::ByKnownForallFact(known) => {
                return self.compile_known_application(&fact, known, position)
            }
            OrFactSearchedProof::BySelectedBranch(selected)
                if !selected.assumed_negated_branches.is_empty() =>
            {
                use crate::compile_to_lean::compile_by_stmt_result::compile_by_contra_stmt_result::validate_atomic_negation;
                if selected.selected_index >= proof.fact.facts.len()
                    || selected.assumed_negated_branches.len() + 1 != proof.fact.facts.len()
                    || source_subject(&selected.selected_branch)?
                        != crate::ast::fact::and_chain_as_fact(
                            &proof.fact.facts[selected.selected_index],
                        )
                {
                    return Err(LeanCompileError::unsupported("Or/SelectedCoverage"));
                }
                let introduce = |mut term: String, index: usize| {
                    if index + 1 != proof.fact.facts.len() {
                        term = format!("(Or.inl {term})");
                    }
                    for _ in 0..index {
                        term = format!("(Or.inr {term})");
                    }
                    term
                };
                let scope =
                    SourcePosition::new(Some(position), SourceOwner::OrSelected(selected), 0);
                let mut lines = vec![
                    "classical".to_string(),
                    "apply Classical.byContradiction".to_string(),
                    "intro _negative_disjunction".to_string(),
                ];
                let mut indices =
                    (0..proof.fact.facts.len()).filter(|i| *i != selected.selected_index);
                for (i, assumption) in selected.assumed_negated_branches.iter().enumerate() {
                    let expected = indices.next().unwrap();
                    if assumption.branch_index != expected {
                        return Err(LeanCompileError::unsupported("Or/SelectedAssumptionOrder"));
                    }
                    let original = crate::ast::fact::and_chain_as_fact(&proof.fact.facts[expected]);
                    let negative = validate_atomic_negation(&original, &assumption.negated_fact)?;
                    let prior = SourcePosition {
                        before: 2 * i,
                        ..scope
                    };
                    self.compile_fact_wd(
                        &assumption.well_defined,
                        &assumption.negated_fact,
                        &prior,
                    )?;
                    self.validate_store(
                        &assumption.store_and_infer.store,
                        &assumption.negated_fact,
                    )?;
                    let formed = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::FactWD(&assumption.well_defined),
                        usize::MAX,
                    );
                    let proposition = self.fact_proposition(&assumption.negated_fact, &formed)?;
                    let not_branch = format!(
                        "(fun _branch => _negative_disjunction {})",
                        introduce("_branch".into(), expected)
                    );
                    let term = if negative {
                        format!("(Classical.byContradiction {not_branch})")
                    } else {
                        not_branch
                    };
                    lines.push(self.emit_internal_fact(
                        &assumption.negated_fact,
                        &(proposition.clone(), term),
                        &formed,
                    )?);
                    lines.extend(self.compile_stored_inferences(
                        &assumption.store_and_infer,
                        &assumption.negated_fact,
                        &(
                            proposition,
                            format!("h_{}", assumption.negated_fact.fact_id().value()),
                        ),
                        &SourcePosition {
                            before: 2 * i + 2,
                            ..scope
                        },
                    )?);
                }
                let checked = self.compile_verify(
                    &selected.selected_branch,
                    &SourcePosition {
                        before: 2 * selected.assumed_negated_branches.len(),
                        ..scope
                    },
                )?;
                lines.push(format!(
                    "exact _negative_disjunction {}",
                    introduce(checked.1, selected.selected_index)
                ));
                format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  "))
            }
            OrFactSearchedProof::BySelectedBranch(selected)
                if selected.assumed_negated_branches.is_empty() =>
            {
                if selected.selected_index >= proof.fact.facts.len()
                    || source_subject(&selected.selected_branch)?
                        != crate::ast::fact::and_chain_as_fact(
                            &proof.fact.facts[selected.selected_index],
                        )
                {
                    return Err(LeanCompileError::new(
                        "Or/SelectedSubject",
                        "The selected original branch differs from its proof or index.",
                    ));
                }
                let mut term = self.compile_verify(&selected.selected_branch, position)?.1;
                if selected.selected_index + 1 != proof.fact.facts.len() {
                    term = format!("(Or.inl {term})");
                }
                for _ in 0..selected.selected_index {
                    term = format!("(Or.inr {term})");
                }
                term
            }
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::ZeroProductSplit(selected),
            ) => {
                let [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(left)), AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(right))] =
                    proof.fact.facts.as_slice()
                else {
                    return Err(LeanCompileError::unsupported("Or/ZeroProductShape"));
                };
                let orientation = |equal: &EqualFact, object: &Obj| {
                    if equal.left.ir() == object.ir() && is_exact_zero(&equal.right) {
                        Ok(false)
                    } else if equal.right.ir() == object.ir() && is_exact_zero(&equal.left) {
                        Ok(true)
                    } else {
                        Err(LeanCompileError::unsupported("Or/ZeroProductBranch"))
                    }
                };
                let left_reversed = orientation(left, &selected.left)?;
                let right_reversed = orientation(right, &selected.right)?;
                let mut lines = vec!["classical".to_string()];
                for (i, (child, object)) in [
                    (&selected.left_in_r, &selected.left),
                    (&selected.right_in_r, &selected.right),
                ]
                .into_iter()
                .enumerate()
                {
                    if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == object.ir() && f.set == Obj::StandardSet(StandardSet::R))
                    {
                        return Err(LeanCompileError::unsupported("Or/ZeroProductMember"));
                    }
                    let checked = self.compile_verify(
                        child,
                        &SourcePosition {
                            before: position.before + i,
                            ..*position
                        },
                    )?;
                    lines.push(format!(
                        "have _factor_real_{i} : {} := {}",
                        checked.0, checked.1
                    ));
                }
                let source = source_subject(&selected.product_zero)?;
                let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &source else {
                    return Err(LeanCompileError::unsupported("Or/ZeroProductPremise"));
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = &equal.left else {
                    return Err(LeanCompileError::unsupported("Or/ZeroProductPremise"));
                };
                if !is_exact_zero(&equal.right) {
                    return Err(LeanCompileError::unsupported("Or/ZeroProductPremise"));
                }
                let swapped = if product.left.ir() == selected.left.ir()
                    && product.right.ir() == selected.right.ir()
                {
                    false
                } else if product.left.ir() == selected.right.ir()
                    && product.right.ir() == selected.left.ir()
                {
                    true
                } else {
                    return Err(LeanCompileError::unsupported("Or/ZeroProductFactors"));
                };
                let checked = self.compile_verify(
                    &selected.product_zero,
                    &SourcePosition {
                        before: position.before + 2,
                        ..*position
                    },
                )?;
                let complete = SourcePosition {
                    before: position.before + 3,
                    ..*position
                };
                let term = self.compile_object_reference(&equal.left, &complete)?;
                lines.push(format!("let _product := {term}"));
                lines.push(format!(
                    "have _product_zero : Litex.Same _product (Litex.number 0) := {}",
                    checked.1
                ));
                lines.push(format!(
                    "by_cases _left : {}",
                    self.atomic_proposition(&AtomicFact::EqualFact(left.clone()), position)?
                ));
                lines.push("· exact Or.inl _left".into());
                let left_nonzero = if left_reversed {
                    "(fun h => _left h.symm)"
                } else {
                    "_left"
                };
                let right_nonzero = if right_reversed {
                    "(fun h => _right h.symm)"
                } else {
                    "_right"
                };
                let (first, second) = if swapped {
                    (right_nonzero, left_nonzero)
                } else {
                    (left_nonzero, right_nonzero)
                };
                lines.push(format!("· apply Or.inr
  apply Classical.byContradiction
  intro _right
  exact (Litex.mulNonzero _product.val.left _product.val.right _product.wd.1 _product.wd.2 {first} {second}) _product_zero"));
                format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  "))
            }
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(selected),
            ) => self.compile_or_square_sum_nonzero(
                &proof.fact,
                &selected.left,
                &selected.right,
                &selected.square_sum_nonzero,
                position,
            )?,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(selected),
            ) => {
                let [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)), AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(greater))] =
                    proof.fact.facts.as_slice()
                else {
                    return Err(LeanCompileError::unsupported("Or/IntegerTailShape"));
                };
                if equal.left.ir() != selected.subject.ir()
                    || equal.right.ir() != selected.base.ir()
                    || greater.left.ir() != selected.subject.ir()
                    || greater.right.ir() != selected.base.ir()
                {
                    return Err(LeanCompileError::new("Or/IntegerTailSubject", "The original equality and strict tail must use the recorded subject and base."));
                }
                let mut integer_memberships = Vec::new();
                for (child, operand) in [
                    (&selected.subject_in_z, &selected.subject),
                    (&selected.base_in_z, &selected.base),
                ] {
                    match source_subject(child)? {
                        Fact::AtomicFact(AtomicFact::InFact(member))
                            if member.element.ir() == operand.ir()
                                && member.set == Obj::StandardSet(StandardSet::Z) => {}
                        _ => {
                            return Err(LeanCompileError::new(
                                "Or/IntegerTailMembership",
                                "An integer child has another subject or carrier.",
                            ))
                        }
                    }
                    integer_memberships.push(self.compile_verify(child, position)?.1);
                }
                let Fact::AtomicFact(bound) = source_subject(&selected.subject_ge_base)? else {
                    return Err(LeanCompileError::unsupported("Or/IntegerTailBound"));
                };
                let (base, subject, strict) = source_order_oriented(&bound)?;
                if strict
                    || base.ir() != selected.base.ir()
                    || subject.ir() != selected.subject.ir()
                {
                    return Err(LeanCompileError::new(
                        "Or/IntegerTailBound",
                        "The weak-bound child has another subject, base or strictness.",
                    ));
                }
                let bound = self.compile_verify(&selected.subject_ge_base, position)?.1;
                let base = self.compile_object_reference(&selected.base, position)?;
                let subject = self.compile_object_reference(&selected.subject, position)?;
                format!(
                    "(Litex.integerSuccessorTail {subject} {base} {} {} {bound})",
                    integer_memberships[0], integer_memberships[1]
                )
            }
            _ => return Err(LeanCompileError::unsupported("Or/SelectedRule")),
        };
        Ok((self.fact_proposition(&fact, position)?, term))
    }

    fn compile_real_order_split(
        &self,
        fact: &OrFact,
        left: &Obj,
        right: &Obj,
        left_real: &VerifyFactResult,
        right_real: &VerifyFactResult,
        reverse: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [AndChainAtomicFact::AtomicFact(first), AndChainAtomicFact::AtomicFact(second)] =
            fact.facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Or/RealSplitShape"));
        };
        let (a, b) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let (x, y, first_strict) = source_order_oriented(first)?;
        let (z, t, second_strict) = source_order_oriented(second)?;
        let valid = if first_strict {
            x == a && y == b && z == b && t == a && !second_strict
        } else {
            x == b && y == a && z == a && t == b && second_strict
        };
        if !valid {
            return Err(LeanCompileError::unsupported("Or/RealSplitSubject"));
        }
        let mut lines = Vec::new();
        for (i, (proof, object)) in [(left_real, left), (right_real, right)]
            .into_iter()
            .enumerate()
        {
            if membership_subject(&source_subject(proof)?, object)? != StandardSet::R {
                return Err(LeanCompileError::unsupported("Or/RealSplitCarrier"));
            }
            let checked = self.compile_verify(
                proof,
                &SourcePosition {
                    before: position.before + i,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have _split_member_{i} : {} := {}",
                checked.0, checked.1
            ));
        }
        let completed = SourcePosition {
            before: position.before + 2,
            ..*position
        };
        let a = self.compile_object_reference(a, &completed)?;
        let b = self.compile_object_reference(b, &completed)?;
        let (ha, hb) = if reverse {
            ("_split_member_1", "_split_member_0")
        } else {
            ("_split_member_0", "_split_member_1")
        };
        lines.push(format!("rcases lt_or_ge (Litex.NativeBridge.asReal {a} {ha}) (Litex.NativeBridge.asReal {b} {hb}) with _lt | _ge"));
        let (strict, weak) = if first_strict {
            ("inl", "inr")
        } else {
            ("inr", "inl")
        };
        lines.push(format!(
            "· exact Or.{strict} ((Litex.NativeBridge.lt_iff_asReal {a} {b} {ha} {hb}).mpr _lt)"
        ));
        lines.push(format!(
            "· exact Or.{weak} ((Litex.NativeBridge.le_iff_asReal {b} {a} {hb} {ha}).mpr _ge)"
        ));
        Ok(format!(
            "(by\n  {})",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    fn compile_or_square_sum_nonzero(
        &self,
        fact: &OrFact,
        left: &Obj,
        right: &Obj,
        nonzero: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(first)), AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(second))] =
            fact.facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Or/SquareSumSubject"));
        };
        let orientation = |fact: &NotEqualFact, operand: &Obj| {
            if &fact.left == operand && is_zero(&fact.right) {
                Ok(false)
            } else if is_zero(&fact.left) && &fact.right == operand {
                Ok(true)
            } else {
                Err(LeanCompileError::new(
                    "Or/SquareSumSubject",
                    "The ordered nonzero branches differ from the recorded components.",
                ))
            }
        };
        let left_reversed = orientation(first, left)?;
        let right_reversed = orientation(second, right)?;
        let Fact::AtomicFact(AtomicFact::NotEqualFact(premise)) = source_subject(nonzero)? else {
            return Err(LeanCompileError::unsupported("Or/SquareSumPremise"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &premise.left else {
            return Err(LeanCompileError::unsupported("Or/SquareSumPremise"));
        };
        // The producer tries precisely two powers or two self-products, in
        // either component order. Do not accept other equivalent polynomials.
        let components = match (sum.left.as_ref(), sum.right.as_ref()) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
            ) if matches!(a.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "2")
                && matches!(b.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "2") =>
            {
                Some((
                    a.base.as_ref(),
                    b.base.as_ref(),
                    "fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)",
                ))
            }
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
            ) if a.left == a.right && b.left == b.right => Some((
                a.left.as_ref(),
                b.left.as_ref(),
                "fun (x y : ℂ) => x * x + y * y",
            )),
            _ => None,
        };
        let Some((a, b, square_sum)) = components else {
            return Err(LeanCompileError::unsupported("Or/SquareSumPremise"));
        };
        if !is_zero(&premise.right) || !((a == left && b == right) || (a == right && b == left)) {
            return Err(LeanCompileError::new(
                "Or/SquareSumPremise",
                "The original nonzero child is not one of the recorded components' square sums.",
            ));
        }
        let checked = self.compile_verify(nonzero, position)?;
        let complete =
            SourcePosition::new(Some(position), SourceOwner::Verify(nonzero), usize::MAX);
        let left_object = self.compile_object_reference(left, &complete)?;
        let right_object = self.compile_object_reference(right, &complete)?;
        let sum_object = self.compile_object_reference(&premise.left, &complete)?;
        let left_native = self.compile_numeric_observation(left, &complete)?;
        let right_native = self.compile_numeric_observation(right, &complete)?;
        let sum_native = self.compile_numeric_observation(&premise.left, &complete)?;
        let zero = "(Litex.number (M := M) (0 : ℂ))";
        let zero_denote = "(Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))";
        let left_same = if left_reversed {
            format!("Litex.Same {zero} {left_object}")
        } else {
            format!("Litex.Same {left_object} {zero}")
        };
        let left_equal = if left_reversed {
            "_litex_left.symm"
        } else {
            "_litex_left"
        };
        let right_equal = if right_reversed {
            "_litex_right.symm"
        } else {
            "_litex_right"
        };
        let (first_equal, second_equal) = if a == left && b == right {
            ("_litex_x_zero", "_litex_y_zero")
        } else {
            ("_litex_y_zero", "_litex_x_zero")
        };
        Ok(format!(
            "(by\n  classical\n  have _litex_sum_nonzero : {} := {}\n  by_cases _litex_left : {left_same}\n  · apply Or.inr\n    intro _litex_right\n    have _litex_x_zero : {} = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber {left_object} {zero} {} (0 : ℂ) {} {zero_denote} ({left_equal})\n    have _litex_y_zero : {} = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber {right_object} {zero} {} (0 : ℂ) {} {zero_denote} ({right_equal})\n    apply _litex_sum_nonzero\n    exact Litex.NativeBridge.sameOfDenoteNumber {sum_object} {zero} {} (0 : ℂ) {} {zero_denote} ((congrArg₂ ({square_sum}) {first_equal} {second_equal}).trans (by norm_num))\n  · exact Or.inl _litex_left\n)",
            checked.0, checked.1,
            left_native.0, left_native.0, left_native.1,
            right_native.0, right_native.0, right_native.1,
            sum_native.0, sum_native.1,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_or_wd(
        &self,
        fact: &OrFact,
        proof: &OrFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        if fact.facts.is_empty() || fact.facts.len() != proof.detailed_ref().branches.len() {
            return Err(LeanCompileError::unsupported("Or/FormationArity"));
        }
        for (index, (branch, wd)) in fact
            .facts
            .iter()
            .zip(&proof.detailed_ref().branches)
            .enumerate()
        {
            self.compile_fact_wd(
                wd,
                &crate::ast::fact::and_chain_as_fact(branch),
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
        }
        Ok(())
    }
}
