use super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: compile the exact selected-equality child and inject its right
    /// endpoint into the retained list-set position. The selected index is
    /// verifier-owned evidence; neither the diagnostic label nor a search of
    /// the current environment participates.
    pub(super) fn construct_lean_list_set_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &ListSetMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [equality_result] = subgoals else {
            return Err("list-set membership requires exactly one equality child Result".into());
        };
        let equality_result = equality_result
            .factual_success()
            .ok_or_else(|| "list-set membership child Result is not factual".to_string())?;
        if !equality_result.store.infers.is_empty() {
            return Err("list-set membership equality child published effects".into());
        }

        let (element, set) = membership_parts(target)?;
        let Obj::ListSet(list_set) = set else {
            return Err("list-set membership evidence targets another set constructor".into());
        };
        let selected = list_set
            .list
            .get(evidence.selected_index)
            .ok_or_else(|| "list-set membership evidence has an out-of-range index".to_string())?;
        let equality_fact = equality_result.fact();
        if equality_result.store.fact.to_string() != equality_fact.to_string() {
            return Err("list-set membership equality child changed its stored fact".into());
        }
        let (equality_left, equality_right) = equality_parts(&equality_fact)?;
        if obj_equality_key(equality_left) != obj_equality_key(element)
            || obj_equality_key(equality_right) != obj_equality_key(selected.as_ref())
        {
            return Err("list-set membership equality changed its selected source element".into());
        }
        let Some(equality_proof) =
            self.construct_lean_proof_from_direct_fact_result(equality_result)?
        else {
            return Ok(None);
        };
        let selected_term = render_obj(selected.as_ref(), &self.environment_stack)?;
        render_obj(set, &self.environment_stack)?;
        let (witness, representation) =
            render_list_set_representation_bridge(&selected_term, evidence.selected_index);
        Ok(Some(format!(
            "⟨{witness}, Litex.Same.trans ({equality_proof}) ({representation})⟩"
        )))
    }

    /// `Combine`: construct one exact nonzero numeric carrier from the
    /// verifier-owned base-membership and nonzero child Results.
    pub(super) fn construct_lean_refined_numeric_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &RefinedNumericMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("refined numeric membership evidence changed its target".into());
        }
        if subgoals.len() != evidence.expected_premises.len() {
            return Err("refined numeric membership lost an ordered child Result".into());
        }
        let [base_result, nonzero_result] = subgoals else {
            return Err("refined numeric membership requires exactly two child Results".into());
        };
        let [expected_base, expected_nonzero] = evidence.expected_premises.as_slice() else {
            return Err("refined numeric membership evidence changed its premise arity".into());
        };
        let base_result = base_result
            .factual_success()
            .ok_or_else(|| "refined numeric base child is not factual".to_string())?;
        let nonzero_result = nonzero_result
            .factual_success()
            .ok_or_else(|| "refined numeric nonzero child is not factual".to_string())?;
        for (name, result, expected) in [
            ("base", base_result, expected_base),
            ("nonzero", nonzero_result, expected_nonzero),
        ] {
            if result.fact().to_string() != expected.to_string()
                || result.store.fact.to_string() != expected.to_string()
                || !result.store.infers.is_empty()
            {
                return Err(format!(
                    "refined numeric {name} child changed its fact or published effects"
                ));
            }
        }

        let (target_element, target_set) = membership_parts(target)?;
        let (base_element, base_set) = membership_parts(expected_base)?;
        let (nonzero_left, nonzero_right) = not_equal_parts(expected_nonzero)?;
        if obj_equality_key(target_element) != obj_equality_key(base_element)
            || obj_equality_key(target_element) != obj_equality_key(nonzero_left)
            || !matches!(nonzero_right, Obj::Number(number) if number.normalized_value == "0")
        {
            return Err("refined numeric membership changed its source element".into());
        }
        let theorem = match (target_set, base_set) {
            (Obj::StandardSet(StandardSet::ZStar), Obj::StandardSet(StandardSet::Z)) => {
                "inZStarOfInZNotSameZero"
            }
            (Obj::StandardSet(StandardSet::QStar), Obj::StandardSet(StandardSet::Q)) => {
                "inQStarOfInQNotSameZero"
            }
            (Obj::StandardSet(StandardSet::RStar), Obj::StandardSet(StandardSet::R)) => {
                "inRStarOfInRNotSameZero"
            }
            (Obj::StandardSet(StandardSet::CStar), Obj::StandardSet(StandardSet::C)) => {
                "inCStarOfInCNotSameZero"
            }
            _ => return Ok(None),
        };
        let Some(base_proof) = self.construct_lean_proof_from_direct_fact_result(base_result)?
        else {
            return Ok(None);
        };
        let Some(nonzero_proof) =
            self.construct_lean_proof_from_direct_fact_result(nonzero_result)?
        else {
            return Ok(None);
        };
        Ok(Some(format!(
            "Litex.Rules.{theorem} ({base_proof}) ({nonzero_proof})"
        )))
    }

    /// `Leaf`: the currently reviewed closed nonmembership fragment is zero
    /// excluded from one of the exact nonzero numeric carriers. The recursive
    /// evaluation Result proves that the source expression normalized to zero.
    pub(super) fn construct_lean_closed_numeric_nonmembership_from_result(
        &self,
        target: &Fact,
        evidence: &ClosedNumericNonmembershipBuiltinRuleEvidence,
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("closed numeric nonmembership evidence changed its target".into());
        }
        validate_success_evaluate_obj_result(&evidence.evaluation)?;
        let (element, set) = nonmembership_parts(target)?;
        let Obj::StandardSet(target_set) = set else {
            return Err("closed numeric nonmembership targets a nonstandard set".into());
        };
        if *target_set != evidence.target_set
            || obj_equality_key(element) != obj_equality_key(&evidence.evaluation.expression)
        {
            return Err(
                "closed numeric nonmembership changed its expression or target carrier".into(),
            );
        }
        if evidence.evaluation.value.normalized_value != "0" {
            return Ok(None);
        }
        let theorem = match target_set {
            StandardSet::ZStar => "notSameZeroOfInZStar",
            StandardSet::QStar => "notSameZeroOfInQStar",
            StandardSet::RStar => "notSameZeroOfInRStar",
            StandardSet::CStar => "notSameZeroOfInCStar",
            _ => return Ok(None),
        };
        let source = render_obj(element, &self.environment_stack)?;
        Ok(Some(format!(
            "(fun __membership => (Litex.Rules.{theorem} (__membership)) (Litex.Same.refl {source}))"
        )))
    }

    /// `Leaf`: replay a verifier-owned canonical witness for one base standard
    /// set. The evidence fixes both the proposition and the carrier.
    pub(super) fn construct_lean_standard_set_nonempty_from_result(
        &self,
        target: &Fact,
        evidence: &StandardSetNonemptyBuiltinRuleEvidence,
    ) -> Result<String, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("standard-set nonempty evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = target else {
            return Err("standard-set nonempty evidence targets another fact family".into());
        };
        let Obj::StandardSet(target_set) = &nonempty.set else {
            return Err("standard-set nonempty evidence targets a nonstandard carrier".into());
        };
        if *target_set != evidence.target_set {
            return Err("standard-set nonempty evidence changed its carrier".into());
        }
        render_fact(target, &self.environment_stack)?;
        let theorem = match target_set {
            StandardSet::N => "naturalNonempty",
            StandardSet::Z => "integerNonempty",
            StandardSet::Q => "rationalNonempty",
            StandardSet::R => "realNonempty",
            StandardSet::C => "complexNonempty",
            unsupported => {
                return Err(format!(
                    "unsupported direct standard-set nonempty carrier `{unsupported}`"
                ));
            }
        };
        Ok(format!("Litex.Rules.{theorem}"))
    }

    /// `Leaf`: map the exact native constant/carrier pair to its reviewed Lean
    /// theorem. There are no premises and no diagnostic-label dispatch.
    pub(super) fn construct_lean_native_constant_membership_from_result(
        &self,
        target: &Fact,
        rule: NativeConstantMembershipBuiltinRule,
    ) -> Result<String, String> {
        let (element, set) = membership_parts(target)?;
        render_fact(target, &self.environment_stack)?;
        let theorem = match (rule, element, set) {
            (
                NativeConstantMembershipBuiltinRule::ImaginaryUnitInComplex,
                Obj::ImaginaryUnit(_),
                Obj::StandardSet(StandardSet::C),
            ) => "imaginaryUnitInC",
            (
                NativeConstantMembershipBuiltinRule::EulerNumberInReal,
                Obj::EulerNumber(_),
                Obj::StandardSet(StandardSet::R),
            ) => "eInR",
            (
                NativeConstantMembershipBuiltinRule::PiInReal,
                Obj::Pi(_),
                Obj::StandardSet(StandardSet::R),
            ) => "piInR",
            (
                NativeConstantMembershipBuiltinRule::EulerNumberInPositiveReal,
                Obj::EulerNumber(_),
                Obj::StandardSet(StandardSet::RPos),
            ) => "eInRPos",
            (
                NativeConstantMembershipBuiltinRule::PiInPositiveReal,
                Obj::Pi(_),
                Obj::StandardSet(StandardSet::RPos),
            ) => "piInRPos",
            (
                NativeConstantMembershipBuiltinRule::EulerNumberInComplex,
                Obj::EulerNumber(_),
                Obj::StandardSet(StandardSet::C),
            ) => "inCOfInR (Litex.Rules.eInR)",
            (
                NativeConstantMembershipBuiltinRule::PiInComplex,
                Obj::Pi(_),
                Obj::StandardSet(StandardSet::C),
            ) => "inCOfInR (Litex.Rules.piInR)",
            _ => return Err("native constant membership changed its constant or carrier".into()),
        };
        Ok(format!("Litex.Rules.{theorem}"))
    }

    /// `Wrap`: compile the sole reversed disequality child and apply symmetry.
    pub(super) fn construct_lean_not_equal_symmetry_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [source_result] = subgoals else {
            return Err("not-equality symmetry requires exactly one child Result".into());
        };
        let source_result = source_result
            .factual_success()
            .ok_or_else(|| "not-equality symmetry child is not factual".to_string())?;
        if !source_result.store.infers.is_empty() {
            return Err("not-equality symmetry child published effects".into());
        }
        let source = source_result.fact();
        let (target_left, target_right) = not_equal_parts(target)?;
        let (source_left, source_right) = not_equal_parts(&source)?;
        if obj_equality_key(source_left) != obj_equality_key(target_right)
            || obj_equality_key(source_right) != obj_equality_key(target_left)
        {
            return Err("not-equality symmetry child does not reverse the target objects".into());
        }
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        Ok(Some(format!("Litex.Rules.notSameSymm ({source_proof})")))
    }

    /// `Leaf`: construct a subset function from the fixed standard-set
    /// inclusion chain encoded by the target endpoints.
    pub(super) fn construct_lean_standard_set_subset_from_result(
        &self,
        target: &Fact,
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = target else {
            return Err("standard-set subset evidence targets another fact family".into());
        };
        let (Obj::StandardSet(source), Obj::StandardSet(destination)) =
            (&subset.left, &subset.right)
        else {
            return Err("standard-set subset evidence retained a nonstandard endpoint".into());
        };
        render_fact(target, &self.environment_stack)?;
        if source == destination {
            return Ok("(fun _x hx => hx)".into());
        }
        let mut proof = "hx".to_string();
        for theorem in standard_set_membership_projection_theorem_chain(*source, *destination)? {
            proof = format!("Litex.Rules.{theorem} ({proof})");
        }
        Ok(format!("(fun _x hx => {proof})"))
    }

    /// `Leaf`: replay closed prime/coprime reflection after validating the
    /// exact predicate, arity, and natural-literal boundary.
    pub(super) fn construct_lean_number_theory_reflection_from_result(
        &self,
        target: &Fact,
        is_prime_rule: bool,
    ) -> Result<String, String> {
        let (predicate, arguments, negated) = match target {
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(value)) => {
                (value.predicate.to_string(), value.body.as_slice(), false)
            }
            Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(value)) => {
                (value.predicate.to_string(), value.body.as_slice(), true)
            }
            _ => return Err("number-theory reflection retained a non-predicate target".into()),
        };
        let (expected_predicate, expected_arity) = if is_prime_rule {
            (PRIME, 1)
        } else {
            (COPRIME, 2)
        };
        if predicate != expected_predicate || arguments.len() != expected_arity {
            return Err("number-theory reflection changed its predicate or arity".into());
        }
        let mut values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let Obj::Number(number) = argument else {
                return Err("number-theory reflection changed a closed numeric argument".into());
            };
            if number.normalized_value.starts_with('-')
                || number.normalized_value.contains('.')
                || (is_prime_rule && number.normalized_value.parse::<u64>().is_err())
            {
                return Err("number-theory reflection retained a non-natural argument".into());
            }
            values.push(number.normalized_value.as_str());
        }
        render_fact(target, &self.environment_stack)?;
        if is_prime_rule {
            let theorem = if negated {
                "notPrimeOfNat"
            } else {
                "primeOfNat"
            };
            Ok(format!(
                "(by simpa using (Litex.{theorem} {} (by norm_num)))",
                values[0]
            ))
        } else {
            let theorem = if negated {
                "notCoprimeOfNat"
            } else {
                "coprimeOfNat"
            };
            Ok(format!(
                "(by simpa using (Litex.{theorem} {} {} (by norm_num)))",
                values[0], values[1]
            ))
        }
    }

    /// `Leaf`: construct finiteness from the exact set constructor retained by
    /// the target proposition.
    pub(super) fn construct_lean_finite_set_from_result(
        &self,
        target: &Fact,
        rule: FiniteSetBuiltinRule,
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(finite)) = target else {
            return Err("finite-set evidence targets a non-finiteness fact".into());
        };
        render_fact(target, &self.environment_stack)?;
        match (rule, &finite.set) {
            (FiniteSetBuiltinRule::Range, Obj::Range(_)) => {
                Ok("(by unfold Litex.Set.Finite Litex.range; infer_instance)".into())
            }
            (FiniteSetBuiltinRule::ClosedRange, Obj::ClosedRange(_)) => {
                Ok("(by unfold Litex.Set.Finite Litex.closedRange; infer_instance)".into())
            }
            (FiniteSetBuiltinRule::ListSet, Obj::ListSet(list_set)) => render_list_set_finiteness(
                &list_set
                    .list
                    .iter()
                    .map(|item| LeanTargetObjectRepresentation::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
                &self.environment_stack,
            ),
            _ => Err("finite-set evidence changed its exact constructor family".into()),
        }
    }

    /// `Leaf`: complex arithmetic is closed without operand premises because
    /// every target-selected operand representation has the universal complex
    /// view. A binder may select `In.rep` instead of the heterogeneous source
    /// symbol, so this must render the numeric view used by the target.
    pub(super) fn construct_lean_complex_membership_closure_from_result(
        &self,
        target: &Fact,
        rule: ComplexArithmeticMembershipClosureBuiltinRule,
    ) -> Result<String, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::C)) {
            return Err("complex arithmetic membership target is not C".into());
        }
        let (left, right, theorem) = match (rule, target_element) {
            (ComplexArithmeticMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInC",
            ),
            (ComplexArithmeticMembershipClosureBuiltinRule::Sub, Obj::Sub(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexSubInC",
            ),
            (ComplexArithmeticMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInC",
            ),
            (ComplexArithmeticMembershipClosureBuiltinRule::Div, Obj::Div(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexDivInC",
            ),
            _ => return Err("complex arithmetic membership changed its operator".into()),
        };
        let rendered_left = render_numeric_obj(left, &self.environment_stack)?;
        let rendered_right = render_numeric_obj(right, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_target = format!(
            "Litex.In ({rendered_left} {} {rendered_right}) Litex.C",
            match rule {
                ComplexArithmeticMembershipClosureBuiltinRule::Add => "+",
                ComplexArithmeticMembershipClosureBuiltinRule::Sub => "-",
                ComplexArithmeticMembershipClosureBuiltinRule::Mul => "*",
                ComplexArithmeticMembershipClosureBuiltinRule::Div => "/",
            }
        );
        if rendered_target != expected_target {
            return Err("complex arithmetic rendering changed its verified target".into());
        }
        Ok(format!(
            "Litex.Rules.{theorem} {rendered_left} {rendered_right}"
        ))
    }

    /// `Leaf`: tuple syntax itself fixes the reflected tuple-shape instance.
    /// The verifier attaches this certificate only after checking the literal
    /// has the tuple arity accepted by the source language.
    pub(super) fn construct_lean_tuple_literal_shape_from_result(
        &self,
        target: &Fact,
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::IsTupleFact(tuple_fact)) = target else {
            return Err("tuple-literal shape evidence targets another fact family".into());
        };
        let Obj::Tuple(tuple) = &tuple_fact.set else {
            return Err("tuple-literal shape evidence changed its exact object".into());
        };
        if tuple.args.len() < 2 {
            return Err("tuple-literal shape evidence retained fewer than two items".into());
        }
        render_fact(target, &self.environment_stack)?;
        Ok("⟨inferInstance⟩".into())
    }

    /// `Wrap`: the integer closure certificate owns one exact conjunction
    /// child whose ordered components prove the two operand memberships.
    pub(super) fn construct_lean_integer_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: IntegerMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::Z)) {
            return Err("integer arithmetic membership target is not Z".into());
        }
        let theorem = match rule {
            IntegerMembershipClosureBuiltinRule::Add if matches!(target_element, Obj::Add(_)) => {
                "complexAddInZ"
            }
            IntegerMembershipClosureBuiltinRule::Sub if matches!(target_element, Obj::Sub(_)) => {
                "complexSubInZ"
            }
            IntegerMembershipClosureBuiltinRule::Mul if matches!(target_element, Obj::Mul(_)) => {
                "complexMulInZ"
            }
            IntegerMembershipClosureBuiltinRule::Mod if matches!(target_element, Obj::Mod(_)) => {
                return self
                    .construct_lean_integer_remainder_membership_from_result(target, subgoals);
            }
            _ => return Err("integer arithmetic closure changed its target operator".into()),
        };
        self.construct_lean_binary_membership_from_conjunction_result(
            target,
            StandardSet::Z,
            theorem,
            subgoals,
        )
    }

    /// `Wrap`: `%` owns one conjunction child proving both operands are in
    /// `Z`. The compiler validates that recursive proof, then applies the
    /// integer remainder operation to the exact representatives retained in
    /// the active compiler environment.
    pub(super) fn construct_lean_integer_remainder_membership_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::Z)) {
            return Err("integer remainder membership target is not Z".into());
        }
        let Obj::Mod(remainder) = target_element else {
            return Err("integer remainder certificate changed its target operator".into());
        };
        let [conjunction_result] = subgoals else {
            return Err("integer remainder requires one conjunction child Result".into());
        };
        let conjunction_result = conjunction_result
            .factual_success()
            .ok_or_else(|| "integer remainder conjunction child is not factual".to_string())?;
        if !conjunction_result.store.infers.is_empty() {
            return Err("integer remainder conjunction child published effects".into());
        }
        let components = conjunction_components(&conjunction_result.fact())?;
        let [left_component, right_component] = components.as_slice() else {
            return Err("integer remainder conjunction changed its component arity".into());
        };
        for (index, (component, expected_operand)) in [left_component, right_component]
            .into_iter()
            .zip([remainder.left.as_ref(), remainder.right.as_ref()])
            .enumerate()
        {
            let (operand, set) = membership_parts(component)?;
            if !matches!(set, Obj::StandardSet(StandardSet::Z))
                || obj_equality_key(operand) != obj_equality_key(expected_operand)
            {
                return Err(format!(
                    "integer remainder conjunction component {index} changed its operand"
                ));
            }
        }
        if self
            .construct_lean_proof_from_direct_fact_result(conjunction_result)?
            .is_none()
        {
            return Ok(None);
        }

        let left = render_integer_obj(remainder.left.as_ref(), &self.environment_stack)?;
        let right = render_integer_obj(remainder.right.as_ref(), &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let rendered_remainder = format!("(({left} % {right} : ℤ) : ℂ)");
        let expected_target = format!("Litex.In {rendered_remainder} Litex.Z");
        if rendered_target != expected_target {
            return Err("integer remainder rendering changed its verified target".into());
        }
        Ok(Some(format!(
            "Litex.Rules.complexIntInZ ({left} % {right})"
        )))
    }

    /// `Combine`: natural closure retains the two operand-membership Results
    /// directly and in source order.
    pub(super) fn construct_lean_natural_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: NaturalMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::N)) {
            return Err("natural arithmetic membership target is not N".into());
        }
        let (left, right, theorem) = match (rule, target_element) {
            (NaturalMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInN",
            ),
            (NaturalMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInN",
            ),
            _ => return Err("natural arithmetic membership changed its operator".into()),
        };
        let [left_result, right_result] = subgoals else {
            return Err("natural closure requires two ordered child Results".into());
        };
        let mut proofs = Vec::with_capacity(2);
        for (index, (child, expected_element)) in [left_result, right_result]
            .into_iter()
            .zip([left, right])
            .enumerate()
        {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("natural closure child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("natural closure child {index} published effects"));
            }
            let child_fact = child.fact();
            let (element, set) = membership_parts(&child_fact)?;
            if !matches!(set, Obj::StandardSet(StandardSet::N))
                || obj_equality_key(element) != obj_equality_key(expected_element)
            {
                return Err(format!(
                    "natural closure child {index} changed its ordered operand"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            proofs.push(render_numeric_operand_membership(
                expected_element,
                &proof,
                &self.environment_stack,
            ));
        }
        Ok(Some(format!(
            "Litex.Rules.{theorem} ({}) ({})",
            proofs[0], proofs[1]
        )))
    }

    /// `Wrap`: rational closure shares the conjunction-child shape with the
    /// integer carrier. Integer power additionally switches to the exact
    /// `ℚ`/`ℤ` representatives selected in the active compiler environment.
    pub(super) fn construct_lean_rational_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: RationalMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, _) = membership_parts(target)?;
        let theorem = match rule {
            RationalMembershipClosureBuiltinRule::Add if matches!(target_element, Obj::Add(_)) => {
                "complexAddInQ"
            }
            RationalMembershipClosureBuiltinRule::Sub if matches!(target_element, Obj::Sub(_)) => {
                "complexSubInQ"
            }
            RationalMembershipClosureBuiltinRule::Mul if matches!(target_element, Obj::Mul(_)) => {
                "complexMulInQ"
            }
            RationalMembershipClosureBuiltinRule::Div if matches!(target_element, Obj::Div(_)) => {
                "complexDivInQ"
            }
            RationalMembershipClosureBuiltinRule::Pow if matches!(target_element, Obj::Pow(_)) => {
                return self.construct_lean_rational_power_membership_from_result(target, subgoals);
            }
            _ => return Err("rational arithmetic closure changed its target operator".into()),
        };
        self.construct_lean_binary_membership_from_conjunction_result(
            target,
            StandardSet::Q,
            theorem,
            subgoals,
        )
    }

    /// `Wrap`: the recursive conjunction proves `base ∈ Q` and `exponent ∈ Z`
    /// in that order. The Result supplies truth; the compiler environment only
    /// supplies the corresponding target representatives while this binder
    /// layer is active.
    pub(super) fn construct_lean_rational_power_membership_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::Q)) {
            return Err("rational power membership target is not Q".into());
        }
        let Obj::Pow(power) = target_element else {
            return Err("rational power certificate changed its target operator".into());
        };
        let [conjunction_result] = subgoals else {
            return Err("rational power requires one conjunction child Result".into());
        };
        let conjunction_result = conjunction_result
            .factual_success()
            .ok_or_else(|| "rational power conjunction child is not factual".to_string())?;
        if !conjunction_result.store.infers.is_empty() {
            return Err("rational power conjunction child published effects".into());
        }
        let components = conjunction_components(&conjunction_result.fact())?;
        let [base_component, exponent_component] = components.as_slice() else {
            return Err("rational power conjunction changed its component arity".into());
        };
        for (index, (component, expected_operand, expected_set)) in
            [base_component, exponent_component]
                .into_iter()
                .zip([
                    (power.base.as_ref(), StandardSet::Q),
                    (power.exponent.as_ref(), StandardSet::Z),
                ])
                .map(|(component, (operand, set))| (component, operand, set))
                .enumerate()
        {
            let (operand, set) = membership_parts(component)?;
            if !matches!(set, Obj::StandardSet(set) if *set == expected_set)
                || obj_equality_key(operand) != obj_equality_key(expected_operand)
            {
                return Err(format!(
                    "rational power conjunction component {index} changed its operand or carrier"
                ));
            }
        }
        if self
            .construct_lean_proof_from_direct_fact_result(conjunction_result)?
            .is_none()
        {
            return Ok(None);
        }

        let base = render_rational_obj(power.base.as_ref(), &self.environment_stack)?;
        let exponent = render_integer_obj(power.exponent.as_ref(), &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let rendered_power = format!("(({base} ^ {exponent} : ℚ) : ℂ)");
        let expected_target = format!("Litex.In {rendered_power} Litex.Q");
        if rendered_target != expected_target {
            return Err("rational power rendering changed its verified target".into());
        }
        Ok(Some(format!(
            "Litex.Rules.complexRatInQ ({base} ^ {exponent})"
        )))
    }

    pub(super) fn construct_lean_binary_membership_from_conjunction_result(
        &mut self,
        target: &Fact,
        expected_set: StandardSet,
        theorem: &str,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(set) if *set == expected_set) {
            return Err(format!(
                "binary arithmetic membership target is not {expected_set}"
            ));
        }
        let (left, right) = match target_element {
            Obj::Add(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            Obj::Sub(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            Obj::Mul(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            Obj::Div(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            _ => return Err("binary arithmetic membership changed its operator".into()),
        };
        let [conjunction_result] = subgoals else {
            return Err(
                "binary arithmetic membership requires one conjunction child Result".into(),
            );
        };
        let conjunction_result = conjunction_result
            .factual_success()
            .ok_or_else(|| "binary arithmetic conjunction child is not factual".to_string())?;
        if !conjunction_result.store.infers.is_empty() {
            return Err("binary arithmetic conjunction child published effects".into());
        }
        let components = conjunction_components(&conjunction_result.fact())?;
        let [left_component, right_component] = components.as_slice() else {
            return Err("binary arithmetic conjunction changed its component arity".into());
        };
        for (index, (component, expected_element)) in [left_component, right_component]
            .into_iter()
            .zip([left, right])
            .enumerate()
        {
            let (element, set) = membership_parts(component)?;
            if !matches!(set, Obj::StandardSet(actual) if *actual == expected_set)
                || obj_equality_key(element) != obj_equality_key(expected_element)
            {
                return Err(format!(
                    "binary arithmetic conjunction component {index} changed its operand"
                ));
            }
        }
        let Some(pair_proof) =
            self.construct_lean_proof_from_direct_fact_result(conjunction_result)?
        else {
            return Ok(None);
        };
        let pair_type = render_fact(&conjunction_result.fact(), &self.environment_stack)?;
        let left_proof =
            render_numeric_operand_membership(left, "__components.1", &self.environment_stack);
        let right_proof =
            render_numeric_operand_membership(right, "__components.2", &self.environment_stack);
        Ok(Some(format!(
            "(by\n  have __components : {pair_type} := {pair_proof}\n  exact Litex.Rules.{theorem} ({left_proof}) ({right_proof}))"
        )))
    }

    /// `Wrap` / `Combine`: replay the common sign and additive-order rules
    /// from their exact ordered child Results. Other arithmetic certificates
    /// remain fail-closed until their target representation and adapter have
    /// been reviewed.
    pub(super) fn construct_lean_arithmetic_builtin_from_result(
        &mut self,
        target: &Fact,
        rule: ArithmeticBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let sign_rule = match rule {
            ArithmeticBuiltinRule::AddNonnegative => {
                Some(LeanArithmeticBuiltinCompilationKind::AddNonnegative)
            }
            ArithmeticBuiltinRule::AddPositive => {
                Some(LeanArithmeticBuiltinCompilationKind::AddPositive)
            }
            ArithmeticBuiltinRule::AddPositiveLeftStrict => {
                Some(LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict)
            }
            ArithmeticBuiltinRule::AddPositiveRightStrict => {
                Some(LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict)
            }
            ArithmeticBuiltinRule::MulNonnegative => {
                Some(LeanArithmeticBuiltinCompilationKind::MulNonnegative)
            }
            ArithmeticBuiltinRule::MulPositive => {
                Some(LeanArithmeticBuiltinCompilationKind::MulPositive)
            }
            ArithmeticBuiltinRule::DivNonnegative => {
                Some(LeanArithmeticBuiltinCompilationKind::DivNonnegative)
            }
            ArithmeticBuiltinRule::DivPositive => {
                Some(LeanArithmeticBuiltinCompilationKind::DivPositive)
            }
            _ => None,
        };
        let expected_child_count = match rule {
            _ if sign_rule.is_some() => 2,
            ArithmeticBuiltinRule::LessEqualFromStrictOrder
            | ArithmeticBuiltinRule::GreaterEqualFromStrictOrder
            | ArithmeticBuiltinRule::AddCommonLeftLessEqual
            | ArithmeticBuiltinRule::AddCommonLeftLess => 1,
            ArithmeticBuiltinRule::AddComponentwiseLessEqual
            | ArithmeticBuiltinRule::AddComponentwiseLess
            | ArithmeticBuiltinRule::AddComponentwiseLessLessEqual
            | ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => 2,
            ArithmeticBuiltinRule::OrderTransitivity => {
                if subgoals.len() < 3 {
                    return Err(
                        "order transitivity lost its carrier evidence or ordered premises".into(),
                    );
                }
                subgoals.len()
            }
            _ => return Ok(None),
        };
        if subgoals.len() != expected_child_count {
            return Err(format!(
                "arithmetic rule {rule:?} changed its ordered child arity"
            ));
        }
        let mut children = Vec::with_capacity(subgoals.len());
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("arithmetic child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("arithmetic child {index} published effects"));
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(child)?
            else {
                return Ok(None);
            };
            children.push(CompiledFactProofBody {
                fact: child.fact(),
                proposition: String::new(),
                proof_expression,
            });
        }
        if let Some(sign_rule) = sign_rule {
            return Ok(Some(render_additive_sign_rule_from_compiled_children(
                target,
                sign_rule,
                &children,
                &self.environment_stack,
            )?));
        }

        if matches!(
            rule,
            ArithmeticBuiltinRule::AddCommonLeftLessEqual
                | ArithmeticBuiltinRule::AddCommonLeftLess
                | ArithmeticBuiltinRule::AddComponentwiseLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLess
                | ArithmeticBuiltinRule::AddComponentwiseLessLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLessEqualLess
        ) {
            return Ok(Some(
                self.construct_lean_additive_order_rule_from_compiled_children(
                    target, rule, &children,
                )?,
            ));
        }

        if rule == ArithmeticBuiltinRule::OrderTransitivity {
            return Ok(Some(
                self.construct_lean_order_transitivity_from_compiled_children(target, &children)?,
            ));
        }

        let [source] = children.as_slice() else {
            unreachable!("strict-to-weak order rule retained one child")
        };
        let (target_left, target_right, target_is_strict) = order_relation_parts(target)?;
        let (source_left, source_right, source_is_strict) = order_relation_parts(&source.fact)?;
        if target_is_strict
            || !source_is_strict
            || obj_equality_key(target_left) != obj_equality_key(source_left)
            || obj_equality_key(target_right) != obj_equality_key(source_right)
        {
            return Err("strict-to-weak order rule changed its endpoints or orientation".into());
        }
        render_fact(target, &self.environment_stack)?;
        Ok(Some(if target_left.to_string() == "0" {
            format!("Litex.Positive.toNonnegative ({})", source.proof_expression)
        } else {
            format!("Litex.Lt.toLe ({})", source.proof_expression)
        }))
    }

    pub(super) fn construct_lean_additive_order_rule_from_compiled_children(
        &self,
        target: &Fact,
        rule: ArithmeticBuiltinRule,
        children: &[CompiledFactProofBody],
    ) -> Result<String, String> {
        let (target_left, target_right, target_is_strict) = order_relation_parts(target)?;
        let (target_left_common, target_left_addend) = addition_parts(target_left)?;
        let (target_right_common, target_right_addend) = addition_parts(target_right)?;

        let (expected_strictness, theorem): (Vec<bool>, &str) = match rule {
            ArithmeticBuiltinRule::AddCommonLeftLessEqual => {
                (vec![false], "complexAddPreservesLessEqualWithCommonLeft")
            }
            ArithmeticBuiltinRule::AddCommonLeftLess => {
                (vec![true], "complexAddPreservesLessWithCommonLeft")
            }
            ArithmeticBuiltinRule::AddComponentwiseLessEqual => (
                vec![false, false],
                "complexAddPreservesLessEqualComponentwise",
            ),
            ArithmeticBuiltinRule::AddComponentwiseLess => {
                (vec![true, true], "complexAddPreservesLessComponentwise")
            }
            ArithmeticBuiltinRule::AddComponentwiseLessLessEqual => (
                vec![true, false],
                "complexAddPreservesLessOfLessAndLessEqual",
            ),
            ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => (
                vec![false, true],
                "complexAddPreservesLessOfLessEqualAndLess",
            ),
            _ => return Err(format!("unsupported additive order rule {rule:?}")),
        };
        let expected_target_strictness = expected_strictness.iter().any(|strict| *strict);
        if target_is_strict != expected_target_strictness
            || children.len() != expected_strictness.len()
        {
            return Err("additive order rule changed its target or premise arity".into());
        }

        if children.len() == 1 {
            if obj_equality_key(target_left_common) != obj_equality_key(target_right_common) {
                return Err("common-left additive order rule changed its common term".into());
            }
            let (premise_left, premise_right, premise_is_strict) =
                order_relation_parts(&children[0].fact)?;
            if premise_is_strict != expected_strictness[0]
                || obj_equality_key(premise_left) != obj_equality_key(target_left_addend)
                || obj_equality_key(premise_right) != obj_equality_key(target_right_addend)
            {
                return Err("common-left additive order rule changed its ordered premise".into());
            }
        } else {
            for (index, ((child, expected_is_strict), (expected_left, expected_right))) in children
                .iter()
                .zip(expected_strictness.iter())
                .zip([
                    (target_left_common, target_right_common),
                    (target_left_addend, target_right_addend),
                ])
                .enumerate()
            {
                let (premise_left, premise_right, premise_is_strict) =
                    order_relation_parts(&child.fact)?;
                if premise_is_strict != *expected_is_strict
                    || obj_equality_key(premise_left) != obj_equality_key(expected_left)
                    || obj_equality_key(premise_right) != obj_equality_key(expected_right)
                {
                    return Err(format!(
                        "componentwise additive order premise {index} changed its endpoints or strictness"
                    ));
                }
            }
        }

        render_fact(target, &self.environment_stack)?;
        let arguments = children
            .iter()
            .map(|child| format!("({})", child.proof_expression))
            .collect::<Vec<_>>()
            .join(" ");
        Ok(format!("Litex.Rules.{theorem} {arguments}"))
    }

    pub(super) fn construct_lean_order_transitivity_from_compiled_children(
        &self,
        target: &Fact,
        children: &[CompiledFactProofBody],
    ) -> Result<String, String> {
        if children.len() < 3 {
            return Err(
                "order transitivity requires carrier evidence followed by two premises".into(),
            );
        }
        let (carrier_evidence, ordered_premises) = children.split_at(children.len() - 2);
        let [first, second] = ordered_premises else {
            unreachable!("order transitivity retained two ordered premises")
        };
        for evidence in carrier_evidence {
            let components = match &evidence.fact {
                Fact::AndFact(_) | Fact::ChainFact(_) => conjunction_components(&evidence.fact)?,
                _ => vec![evidence.fact.clone()],
            };
            for component in components {
                let (_object, set) = membership_parts(&component)?;
                if !matches!(set, Obj::StandardSet(StandardSet::R | StandardSet::Z)) {
                    return Err(
                        "order transitivity carrier evidence changed from the verified R/Z fragment"
                            .into(),
                    );
                }
            }
        }

        let (target_left, target_right, target_strict) = order_relation_parts(target)?;
        let (first_left, middle, first_strict) = order_relation_parts(&first.fact)?;
        let (second_left, second_right, second_strict) = order_relation_parts(&second.fact)?;
        if obj_equality_key(target_left) != obj_equality_key(first_left)
            || obj_equality_key(middle) != obj_equality_key(second_left)
            || obj_equality_key(target_right) != obj_equality_key(second_right)
            || (target_strict && !first_strict && !second_strict)
        {
            return Err("order transitivity changed its ordered path".into());
        }
        if target_left.to_string() == "0"
            || first_left.to_string() == "0"
            || second_left.to_string() == "0"
        {
            return Err("mixed zero-ended order transitivity has no reviewed Lean adapter".into());
        }

        render_fact(target, &self.environment_stack)?;
        let first_proof = &first.proof_expression;
        let second_proof = &second.proof_expression;
        if target_strict {
            return Ok(match (first_strict, second_strict) {
                (true, true) => format!("Litex.Lt.trans ({first_proof}) ({second_proof})"),
                (true, false) => {
                    format!("Litex.Lt.transLe ({first_proof}) ({second_proof})")
                }
                (false, true) => {
                    format!("Litex.Le.transLt ({first_proof}) ({second_proof})")
                }
                (false, false) => unreachable!("strict target requires one strict premise"),
            });
        }
        let first_le = if first_strict {
            format!("Litex.Lt.toLe ({first_proof})")
        } else {
            format!("({first_proof})")
        };
        let second_le = if second_strict {
            format!("Litex.Lt.toLe ({second_proof})")
        } else {
            format!("({second_proof})")
        };
        Ok(format!("Litex.Le.trans {first_le} {second_le}"))
    }

    /// `Combine`: validate one registry-owned certificate directly from its
    /// stable rule identity, semantic fingerprint, matched bindings, and
    /// ordered child Results. This first direct tranche covers the complete
    /// registered set catalog; unsupported registered families remain on the
    /// compatibility path until their target renderers are migrated.
    pub(super) fn construct_lean_registered_local_builtin_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        self.validate_registered_local_builtin_target_and_child_arity(target, evidence, subgoals)?;
        let Some((set_rule, expected_binding_count, expected_semantic_premise_count)) =
            registered_set_rule(&evidence.rule_id, &evidence.semantic_fingerprint)
        else {
            return self
                .construct_lean_registered_arithmetic_rule_from_result(target, evidence, subgoals);
        };
        if evidence.bindings.len() != expected_binding_count
            || evidence.parameter_requirement_count != expected_binding_count
        {
            return Err(format!(
                "registered set rule `{}` changed its binding or parameter-requirement arity",
                evidence.rule_id.as_str()
            ));
        }

        let mut semantic_premises = Vec::new();
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("registered set child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("registered set child {index} published effects"));
            }
            let fact = child.fact();
            let is_semantic_premise = if index >= evidence.parameter_requirement_count {
                true
            } else {
                let binding = &evidence.bindings[index];
                let (retained_binding, is_semantic_premise) = match &fact {
                    Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) => (&sethood.set, false),
                    Fact::AtomicFact(AtomicFact::InFact(membership)) => (&membership.element, true),
                    _ => {
                        return Err(format!(
                            "registered set parameter child {index} is neither sethood nor membership evidence"
                        ));
                    }
                };
                if !canonical_objs_equal(retained_binding, binding, MatchLimits::default())
                    .map_err(|error| error.message)?
                {
                    return Err(format!(
                        "registered set parameter child {index} changed its exact binding"
                    ));
                }
                is_semantic_premise
            };
            // A source `A set` parameter check is represented by the Lean
            // binder `A : Litex.Set`; it is a validated compiler input, not a
            // proposition that needs a separate Lean proof term.
            if !is_semantic_premise {
                continue;
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(child)?
            else {
                return Ok(None);
            };
            semantic_premises.push(CompiledFactProofBody {
                proposition: String::new(),
                fact,
                proof_expression,
            });
        }
        if semantic_premises.len() != expected_semantic_premise_count {
            return Err(format!(
                "registered set rule `{}` changed its semantic premise count",
                evidence.rule_id.as_str()
            ));
        }

        let proof = match set_rule {
            LeanSetBuiltinCompilationKind::UnionCommutative
            | LeanSetBuiltinCompilationKind::UnionAssociative
            | LeanSetBuiltinCompilationKind::UnionIdempotent
            | LeanSetBuiltinCompilationKind::UnionEmptyIdentity
            | LeanSetBuiltinCompilationKind::IntersectCommutative
            | LeanSetBuiltinCompilationKind::IntersectAssociative => {
                if !semantic_premises.is_empty() {
                    return Err(
                        "registered structural set equality retained semantic premises".into(),
                    );
                }
                render_structural_set_equality(target, set_rule, &self.environment_stack)?
            }
            LeanSetBuiltinCompilationKind::UnionMembershipLeft
            | LeanSetBuiltinCompilationKind::UnionMembershipRight
            | LeanSetBuiltinCompilationKind::IntersectMembershipBoth
            | LeanSetBuiltinCompilationKind::SetMinusMembership => {
                let direct_rule = match set_rule {
                    LeanSetBuiltinCompilationKind::UnionMembershipLeft => {
                        SetBuiltinRule::UnionMembershipLeft
                    }
                    LeanSetBuiltinCompilationKind::UnionMembershipRight => {
                        SetBuiltinRule::UnionMembershipRight
                    }
                    LeanSetBuiltinCompilationKind::IntersectMembershipBoth => {
                        SetBuiltinRule::IntersectMembershipBoth
                    }
                    LeanSetBuiltinCompilationKind::SetMinusMembership => {
                        SetBuiltinRule::SetMinusMembership
                    }
                    _ => unreachable!("matched registered base set rule"),
                };
                let children = semantic_premises
                    .iter()
                    .map(|premise| (premise.fact.clone(), premise.proof_expression.clone()))
                    .collect::<Vec<_>>();
                render_base_set_builtin_rule_from_compiled_children(
                    target,
                    direct_rule,
                    &children,
                    &self.environment_stack,
                )?
            }
            _ => render_extended_set_rule(
                target,
                set_rule,
                &semantic_premises,
                &self.environment_stack,
            )?,
        };
        Ok(Some(proof))
    }

    /// `Combine`: registered arithmetic certificates retain real-parameter
    /// checks followed by the semantic premises in schema order. The stable
    /// RuleId selects one reviewed adapter only after the current registry
    /// fingerprint and every child shape have been validated.
    pub(super) fn construct_lean_registered_arithmetic_rule_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        #[derive(Clone, Copy)]
        enum RegisteredArithmeticRule {
            WeakOrderFromStrictOrder,
            SubtractionSign { strict: bool },
            Sign(LeanArithmeticBuiltinCompilationKind),
            AdditiveOrder(ArithmeticBuiltinRule),
        }

        let fingerprint = evidence.semantic_fingerprint.as_hex();
        let rule = match evidence.rule_id.as_str() {
            LESS_EQUAL_OF_LESS_RULE_ID if fingerprint == LESS_EQUAL_OF_LESS_FINGERPRINT => {
                RegisteredArithmeticRule::WeakOrderFromStrictOrder
            }
            "order.greater_equal_of_greater" => RegisteredArithmeticRule::WeakOrderFromStrictOrder,
            "order.sub_nonnegative_of_less_equal" => {
                RegisteredArithmeticRule::SubtractionSign { strict: false }
            }
            "order.sub_positive_of_less" => {
                RegisteredArithmeticRule::SubtractionSign { strict: true }
            }
            ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID
                if fingerprint == ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT =>
            {
                RegisteredArithmeticRule::Sign(
                    LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict,
                )
            }
            ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID
                if fingerprint == ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT =>
            {
                RegisteredArithmeticRule::Sign(
                    LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict,
                )
            }
            ADD_NONNEGATIVE_RULE_ID if fingerprint == ADD_NONNEGATIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::AddNonnegative)
            }
            ADD_POSITIVE_RULE_ID if fingerprint == ADD_POSITIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::AddPositive)
            }
            MUL_NONNEGATIVE_RULE_ID if fingerprint == MUL_NONNEGATIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::MulNonnegative)
            }
            MUL_POSITIVE_RULE_ID if fingerprint == MUL_POSITIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::MulPositive)
            }
            DIV_NONNEGATIVE_RULE_ID if fingerprint == DIV_NONNEGATIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::DivNonnegative)
            }
            DIV_POSITIVE_RULE_ID if fingerprint == DIV_POSITIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::DivPositive)
            }
            "order.add_le_add_left" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddCommonLeftLessEqual,
            ),
            "order.add_le_add" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessEqual,
            ),
            "order.add_lt_add_left" => {
                RegisteredArithmeticRule::AdditiveOrder(ArithmeticBuiltinRule::AddCommonLeftLess)
            }
            "order.add_lt_add" => {
                RegisteredArithmeticRule::AdditiveOrder(ArithmeticBuiltinRule::AddComponentwiseLess)
            }
            "order.add_lt_add_of_lt_of_le" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessLessEqual,
            ),
            "order.add_lt_add_of_le_of_lt" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessEqualLess,
            ),
            _ => return Ok(None),
        };
        let (expected_binding_count, expected_semantic_premise_count) = match rule {
            RegisteredArithmeticRule::WeakOrderFromStrictOrder
            | RegisteredArithmeticRule::SubtractionSign { .. } => (2, 1),
            RegisteredArithmeticRule::Sign(_) => (2, 2),
            RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddCommonLeftLessEqual
                | ArithmeticBuiltinRule::AddCommonLeftLess,
            ) => (3, 1),
            RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLess
                | ArithmeticBuiltinRule::AddComponentwiseLessLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLessEqualLess,
            ) => (4, 2),
            RegisteredArithmeticRule::AdditiveOrder(_) => {
                return Err("registered additive order rule has no reviewed arity".into());
            }
        };
        if evidence.bindings.len() != expected_binding_count
            || evidence.parameter_requirement_count != expected_binding_count
            || subgoals.len() != expected_binding_count + expected_semantic_premise_count
        {
            return Err(format!(
                "registered arithmetic rule `{}` changed its certificate arity",
                evidence.rule_id.as_str()
            ));
        }

        let mut semantic_premises = Vec::with_capacity(expected_semantic_premise_count);
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("registered arithmetic child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!(
                    "registered arithmetic child {index} published effects"
                ));
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(child)?
            else {
                return Ok(None);
            };
            let fact = child.fact();
            if index < evidence.parameter_requirement_count {
                let (element, set) = membership_parts(&fact)?;
                if !matches!(set, Obj::StandardSet(StandardSet::R))
                    || !canonical_objs_equal(
                        element,
                        &evidence.bindings[index],
                        MatchLimits::default(),
                    )
                    .map_err(|error| error.message)?
                {
                    return Err(format!(
                        "registered arithmetic parameter child {index} changed its exact real binding"
                    ));
                }
                continue;
            }
            semantic_premises.push(CompiledFactProofBody {
                fact,
                proposition: String::new(),
                proof_expression,
            });
        }

        let proof = match rule {
            RegisteredArithmeticRule::Sign(rule) => {
                render_additive_sign_rule_from_compiled_children(
                    target,
                    rule,
                    &semantic_premises,
                    &self.environment_stack,
                )?
            }
            RegisteredArithmeticRule::AdditiveOrder(rule) => self
                .construct_lean_additive_order_rule_from_compiled_children(
                    target,
                    rule,
                    &semantic_premises,
                )?,
            RegisteredArithmeticRule::WeakOrderFromStrictOrder => {
                let [premise] = semantic_premises.as_slice() else {
                    unreachable!("registered less-equal rule retained one premise")
                };
                let (strict_left, strict_right, premise_is_strict) =
                    order_relation_parts(&premise.fact)?;
                let (weak_left, weak_right, target_is_strict) = order_relation_parts(target)?;
                if !premise_is_strict
                    || target_is_strict
                    || obj_equality_key(strict_left) != obj_equality_key(weak_left)
                    || obj_equality_key(strict_right) != obj_equality_key(weak_right)
                {
                    return Err(
                        "registered strict-to-weak order rule changed its relation or ordered endpoints"
                            .into(),
                    );
                }
                render_fact(target, &self.environment_stack)?;
                if strict_left.to_string() == "0" {
                    format!(
                        "Litex.Positive.toNonnegative ({})",
                        premise.proof_expression
                    )
                } else {
                    format!("Litex.Lt.toLe ({})", premise.proof_expression)
                }
            }
            RegisteredArithmeticRule::SubtractionSign { strict } => {
                let [premise] = semantic_premises.as_slice() else {
                    unreachable!("registered subtraction-sign rule retained one premise")
                };
                let (premise_left, premise_right, premise_is_strict) =
                    order_relation_parts(&premise.fact)?;
                let (target_zero, target_expression) = positive_order_parts(target, strict)?;
                let Obj::Sub(subtraction) = target_expression else {
                    return Err(
                        "registered subtraction-sign rule changed its target operator".into(),
                    );
                };
                if premise_is_strict != strict
                    || target_zero.to_string() != "0"
                    || obj_equality_key(premise_left)
                        != obj_equality_key(subtraction.right.as_ref())
                    || obj_equality_key(premise_right)
                        != obj_equality_key(subtraction.left.as_ref())
                {
                    return Err(
                        "registered subtraction-sign rule changed its ordered operands or strictness"
                            .into(),
                    );
                }
                render_fact(target, &self.environment_stack)?;
                let theorem = if strict {
                    "complexSubPositiveOfLess"
                } else {
                    "complexSubNonnegativeOfLessEqual"
                };
                format!("Litex.Rules.{theorem} ({})", premise.proof_expression)
            }
        };
        Ok(Some(proof))
    }

    pub(super) fn validate_registered_local_builtin_target_and_child_arity(
        &self,
        target: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<(), String> {
        let registered_fingerprint = registered_local_builtin_fingerprint_by_id(&evidence.rule_id)
            .map_err(|error| {
                format!("failed to read registered local builtin metadata: {error:?}")
            })?
            .ok_or_else(|| {
                format!(
                    "unknown local builtin RuleId `{}`",
                    evidence.rule_id.as_str()
                )
            })?;
        if registered_fingerprint != evidence.semantic_fingerprint {
            return Err(format!(
                "stale local builtin fingerprint for `{}`",
                evidence.rule_id.as_str()
            ));
        }
        let Some((set_rule, expected_binding_count, expected_semantic_premise_count)) =
            registered_set_rule(&evidence.rule_id, &evidence.semantic_fingerprint)
        else {
            return Ok(());
        };
        if !matches!(target, Fact::AtomicFact(_)) {
            return Err("local builtin certificate target must be atomic".into());
        }
        if evidence.bindings.len() != expected_binding_count
            || evidence.parameter_requirement_count != expected_binding_count
        {
            return Err(
                "local builtin certificate has the wrong binding or requirement arity".into(),
            );
        }
        let membership_parameter_count = usize::from(matches!(
            set_rule,
            LeanSetBuiltinCompilationKind::UnionMembershipLeft
                | LeanSetBuiltinCompilationKind::UnionMembershipRight
                | LeanSetBuiltinCompilationKind::IntersectMembershipBoth
                | LeanSetBuiltinCompilationKind::SetMinusMembership
        ));
        let expected_child_count =
            expected_binding_count + expected_semantic_premise_count - membership_parameter_count;
        if subgoals.len() != expected_child_count {
            return Err("local builtin certificate has the wrong child-proof arity".into());
        }
        Ok(())
    }
}
