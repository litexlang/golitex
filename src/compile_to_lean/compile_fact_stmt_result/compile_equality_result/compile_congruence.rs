use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::{
    helper::set_builders_alpha_equal, SameFreeParamShapeProof,
};

impl LitexToLeanCompiler {
    pub(super) fn compile_tuple_component_strategy(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(
            (&fact.left, &fact.right),
            (
                Obj::ProductShape(ProductShape::Tuple(_)),
                Obj::ProductShape(ProductShape::Tuple(_))
            )
        ) || requirements.len() != children.len()
        {
            return Err(LeanCompileError::unsupported("TupleStrategy/Requirements"));
        }
        for (requirement, child) in requirements.iter().zip(children) {
            if source_subject(child)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "TupleStrategy/RequirementSubject",
                ));
            }
        }
        self.compile_matching_one_arg_by_one(fact, children, position)
    }

    pub(in crate::compile_to_lean) fn compile_matching_one_arg_by_one(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let integer_operation = |closed| {
            format!("(fun (a b : M.Value) => Litex.SetSemantics.sepValue (M := M) (M.standard .integer) (fun z => ∃ lower upper k : ℤ, a = M.number (lower : ℂ) ∧ b = M.number (upper : ℂ) ∧ z = M.number (k : ℂ) ∧ lower ≤ k ∧ k {} upper))", if closed { "≤" } else { "<" })
        };
        let interval_constructor = match (&fact.left, &fact.right) {
            (Obj::SetFormer(SetFormer::Range(left)), Obj::SetFormer(SetFormer::Range(right))) => {
                Some((
                    vec![
                        (left.start.as_ref(), right.start.as_ref()),
                        (left.end.as_ref(), right.end.as_ref()),
                    ],
                    integer_operation(false),
                ))
            }
            (
                Obj::SetFormer(SetFormer::ClosedRange(left)),
                Obj::SetFormer(SetFormer::ClosedRange(right)),
            ) => Some((
                vec![
                    (left.start.as_ref(), right.start.as_ref()),
                    (left.end.as_ref(), right.end.as_ref()),
                ],
                integer_operation(true),
            )),
            (
                Obj::SetFormer(SetFormer::IntervalObj(left)),
                Obj::SetFormer(SetFormer::IntervalObj(right)),
            ) => {
                let (a, b, lc, rc) = real_interval_parts(left);
                let (c, d, left_closed, right_closed) = real_interval_parts(right);
                if (lc, rc) != (left_closed, right_closed) {
                    return Err(LeanCompileError::unsupported("IntervalCongruence/Kind"));
                }
                Some((vec![(a,c),(b,d)],format!("(fun (a b : M.Value) => Litex.SetSemantics.sepValue (M := M) (M.standard .real) (fun z => Litex.realBound {lc} a z ∧ Litex.realBound {rc} z b))")))
            }
            (
                Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(left)),
                Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(right)),
            ) => {
                let (a, lower, closed) = real_ray_parts(left);
                let (b, right_lower, right_closed) = real_ray_parts(right);
                if (lower, closed) != (right_lower, right_closed) {
                    return Err(LeanCompileError::unsupported("IntervalCongruence/Kind"));
                }
                Some((vec![(a,b)],format!("(fun (a : M.Value) => Litex.SetSemantics.sepValue (M := M) (M.standard .real) (fun z => if {lower} then Litex.realBound {closed} a z else Litex.realBound {closed} z a))")))
            }
            _ => None,
        };
        if let Some((pairs, operation)) = interval_constructor {
            if children.len() != pairs.len() {
                return Err(LeanCompileError::unsupported("IntervalCongruence/Children"));
            }
            let mut equalities = Vec::with_capacity(children.len());
            for (index, ((left, right), child)) in pairs.into_iter().zip(children).enumerate() {
                if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::EqualFact(eq))if eq.left.ir()==left.ir()&&eq.right.ir()==right.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "IntervalCongruence/ChildSubject",
                    ));
                }
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let checked = self.compile_verify(child, &prior)?;
                let formed = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
                equalities.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(left, &formed)?,
                    self.compile_normalization_value(right, &formed)?,
                    checked.1
                ));
            }
            // The fixed denotations preserve the original endpoint hosts and
            // interval kind. Both actual parent WD trees remain mandatory.
            self.compile_object_reference(&fact.left, position)?;
            self.compile_object_reference(&fact.right, position)?;
            return Ok(if equalities.len() == 1 {
                format!("(congrArg {operation} {})", equalities[0])
            } else {
                format!(
                    "(congrArg₂ {operation} {} {})",
                    equalities[0], equalities[1]
                )
            });
        }
        let finite_constructor = match (&fact.left, &fact.right) {
            (
                Obj::SetFormer(SetFormer::ListSet(left)),
                Obj::SetFormer(SetFormer::ListSet(right)),
            ) if left.list.len() == right.list.len() => Some((
                left.list
                    .iter()
                    .zip(&right.list)
                    .map(|(a, b)| (a.as_ref(), b.as_ref()))
                    .collect::<Vec<_>>(),
                "literal",
            )),
            (Obj::SetFormer(SetFormer::SeqSet(left)), Obj::SetFormer(SetFormer::SeqSet(right))) => {
                Some((vec![(left.set.as_ref(), right.set.as_ref())], "sequence"))
            }
            (
                Obj::SetFormer(SetFormer::FiniteSeqSet(left)),
                Obj::SetFormer(SetFormer::FiniteSeqSet(right)),
            ) => Some((
                vec![
                    (left.set.as_ref(), right.set.as_ref()),
                    (left.n.as_ref(), right.n.as_ref()),
                ],
                "finite_sequence",
            )),
            (
                Obj::ProductShape(ProductShape::Cart(left)),
                Obj::ProductShape(ProductShape::Cart(right)),
            ) if left.args.len() == right.args.len() => Some((
                left.args
                    .iter()
                    .zip(&right.args)
                    .map(|(a, b)| (a.as_ref(), b.as_ref()))
                    .collect::<Vec<_>>(),
                "cartesian",
            )),
            _ => None,
        };
        if let Some((pairs, constructor)) = finite_constructor {
            if children.len() != pairs.len() {
                return Err(LeanCompileError::unsupported(
                    "FiniteConstructorCongruence/Children",
                ));
            }
            let mut equalities = Vec::with_capacity(children.len());
            for (index, ((left, right), child)) in pairs.into_iter().zip(children).enumerate() {
                if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==left.ir() && eq.right.ir()==right.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FiniteConstructorCongruence/ChildSubject",
                    ));
                }
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let checked = self.compile_verify(child, &prior)?;
                let formed = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
                equalities.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(left, &formed)?,
                    self.compile_normalization_value(right, &formed)?,
                    checked.1
                ));
            }
            // Denotation congruence retains both original formations, including
            // literal distinctness and finite-sequence natural-length evidence.
            let left = self.compile_object_reference(&fact.left, position)?;
            let right = self.compile_object_reference(&fact.right, position)?;
            return Ok(match constructor {
                "literal" => equalities.iter().rev().fold("(rfl : Litex.SetSemantics.emptyValue (M := M) = Litex.SetSemantics.emptyValue (M := M))".to_owned(),|tail,head|format!("(congrArg₂ (Litex.SetSemantics.insertValue (M := M)) {head} {tail})")),
                "cartesian" => format!("(congrArg (Litex.FiniteFunction.cartValue (M := M)) (funext {}))",finite_vector_proof(&equalities)),
                "sequence" => format!("(by\n  let _left := {left}\n  let _right := {right}\n  exact Litex.seqSetSameOfCarrier _left _right {})",equalities[0]),
                "finite_sequence" => format!("(by\n  let _left := {left}\n  let _right := {right}\n  exact Litex.finiteSeqSameOfArgs _left _right {} {})",equalities[0],equalities[1]),
                _ => unreachable!(),
            });
        }
        let set_constructor = match (&fact.left, &fact.right) {
        (Obj::SetOperator(SetOperator::Union(left)), Obj::SetOperator(SetOperator::Union(right))) => Some((
            vec![(left.left.as_ref(), right.left.as_ref()), (left.right.as_ref(), right.right.as_ref())],
            "(Litex.SetSemantics.unionValue (M := M))",
        )),
        (Obj::SetOperator(SetOperator::Intersect(left)), Obj::SetOperator(SetOperator::Intersect(right))) => Some((
            vec![(left.left.as_ref(), right.left.as_ref()), (left.right.as_ref(), right.right.as_ref())],
            "(fun (a b : M.Value) => Litex.SetSemantics.sepValue (M := M) a (fun z => M.mem z b))",
        )),
        (Obj::SetOperator(SetOperator::SetMinus(left)), Obj::SetOperator(SetOperator::SetMinus(right))) => Some((
            vec![(left.left.as_ref(), right.left.as_ref()), (left.right.as_ref(), right.right.as_ref())],
            "(fun (a b : M.Value) => Litex.SetSemantics.sepValue (M := M) a (fun z => ¬ M.mem z b))",
        )),
        (Obj::SetOperator(SetOperator::SymmetricDifference(left)), Obj::SetOperator(SetOperator::SymmetricDifference(right))) => Some((
            vec![(left.left.as_ref(), right.left.as_ref()), (left.right.as_ref(), right.right.as_ref())],
            "(Litex.symmetricDifferenceValue (M := M))",
        )),
        (Obj::SetOperator(SetOperator::PowerSet(left)), Obj::SetOperator(SetOperator::PowerSet(right))) => Some((
            vec![(left.set.as_ref(), right.set.as_ref())],
            "(Litex.SetSemantics.powerValue (M := M))",
        )),
        (Obj::SetOperator(SetOperator::FamilyUnion(left)), Obj::SetOperator(SetOperator::FamilyUnion(right))) => Some((
            vec![(left.left.as_ref(), right.left.as_ref())],
            "(fun A => Litex.IndexedUnionSemantics.indexedUnionValue (M := M) A id)",
        )),
        (Obj::SetOperator(SetOperator::FamilyIntersect(left)), Obj::SetOperator(SetOperator::FamilyIntersect(right))) => Some((
            vec![(left.left.as_ref(), right.left.as_ref())],
            "(Litex.familyIntersectValue (M := M))",
        )),
        _ => None,
    };
        if let Some((pairs, operation)) = set_constructor {
            if children.len() != pairs.len() {
                return Err(LeanCompileError::unsupported(
                    "SetConstructorCongruence/Children",
                ));
            }
            let mut equalities = Vec::with_capacity(pairs.len());
            for (index, ((left, right), child)) in pairs.into_iter().zip(children).enumerate() {
                if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir() == left.ir() && eq.right.ir() == right.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "SetConstructorCongruence/ChildSubject",
                    ));
                }
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let checked = self.compile_verify(child, &prior)?;
                let formed = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
                equalities.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(left, &formed)?,
                    self.compile_normalization_value(right, &formed)?,
                    checked.1
                ));
            }
            // In particular, FamilyIntersect consumes both original nonempty
            // requirements; a denotation equality does not manufacture WD.
            self.compile_object_reference(&fact.left, position)?;
            self.compile_object_reference(&fact.right, position)?;
            return Ok(if equalities.len() == 1 {
                format!("(congrArg {operation} {})", equalities[0])
            } else {
                format!(
                    "(congrArg₂ {operation} {} {})",
                    equalities[0], equalities[1]
                )
            });
        }
        let constructor = match (&fact.left, &fact.right) {
            (
                Obj::FunctionSpace(FunctionSpace::FnRange(left)),
                Obj::FunctionSpace(FunctionSpace::FnRange(right)),
            ) => Some((
                vec![(left.function.as_ref(), right.function.as_ref())],
                "functionRangeValueCongr",
            )),
            (
                Obj::FunctionSpace(FunctionSpace::Preimage(left)),
                Obj::FunctionSpace(FunctionSpace::Preimage(right)),
            ) => Some((
                vec![
                    (left.function.as_ref(), right.function.as_ref()),
                    (left.value.as_ref(), right.value.as_ref()),
                ],
                "pointPreimageValueCongr",
            )),
            (
                Obj::FunctionSpace(FunctionSpace::PreimageSet(left)),
                Obj::FunctionSpace(FunctionSpace::PreimageSet(right)),
            ) => Some((
                vec![
                    (left.function.as_ref(), right.function.as_ref()),
                    (left.target_set.as_ref(), right.target_set.as_ref()),
                ],
                "setPreimageValueCongr",
            )),
            _ => None,
        };
        if let Some((pairs, law)) = constructor {
            if children.len() != pairs.len() {
                return Err(LeanCompileError::unsupported(
                    "FunctionConstructorCongruence/Children",
                ));
            }
            let mut equalities = Vec::with_capacity(pairs.len());
            for (index, ((left, right), child)) in pairs.into_iter().zip(children).enumerate() {
                if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir() == left.ir() && eq.right.ir() == right.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FunctionConstructorCongruence/ChildSubject",
                    ));
                }
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let checked = self.compile_verify(child, &prior)?;
                let formed = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
                equalities.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(left, &formed)?,
                    self.compile_normalization_value(right, &formed)?,
                    checked.1
                ));
            }
            // Both actual constructors keep their original complete interfaces
            // and formation evidence. Child WD belongs to its original stage.
            self.compile_object_reference(&fact.left, position)?;
            self.compile_object_reference(&fact.right, position)?;
            return Ok(format!("(Litex.{law} (M := M) {})", equalities.join(" ")));
        }
        if let (
            Obj::FunctionSpace(FunctionSpace::Composition(left)),
            Obj::FunctionSpace(FunctionSpace::Composition(right)),
        ) = (&fact.left, &fact.right)
        {
            if children.len() != 2 {
                return Err(LeanCompileError::unsupported(
                    "CompositionCongruence/Children",
                ));
            }
            let mut equalities = Vec::with_capacity(2);
            for (index, ((left, right), child)) in
                [(&left.outer, &right.outer), (&left.inner, &right.inner)]
                    .into_iter()
                    .zip(children)
                    .enumerate()
            {
                if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir()==left.ir() && eq.right.ir()==right.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "CompositionCongruence/ChildSubject",
                    ));
                }
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let checked = self.compile_verify(child, &prior)?;
                let formed = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
                equalities.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(left, &formed)?,
                    self.compile_normalization_value(right, &formed)?,
                    checked.1
                ));
            }
            self.compile_object_reference(&fact.left, position)?;
            self.compile_object_reference(&fact.right, position)?;
            return Ok(format!(
                "(Litex.compositionValueCongr (M := M) {} {})",
                equalities[0], equalities[1]
            ));
        }
        if matches!(
            (&fact.left, &fact.right),
            (Obj::BoundOperator(_), Obj::BoundOperator(_))
        ) {
            return self.compile_real_extremum_congruence(fact, children, position);
        }
        if matches!(
            (&fact.left, &fact.right),
            (
                Obj::MatrixOperator(MatrixOperator::Rank(_)),
                Obj::MatrixOperator(MatrixOperator::Rank(_))
            )
        ) {
            return self.compile_matrix_rank_congruence(fact, children, position);
        }
        if let (
            Obj::ProductShape(ProductShape::Tuple(left)),
            Obj::ProductShape(ProductShape::Tuple(right)),
        ) = (&fact.left, &fact.right)
        {
            if left.args.is_empty()
                || left.args.len() != right.args.len()
                || children.len() != left.args.len()
            {
                return Err(LeanCompileError::new(
                    "TupleCongruence/Children",
                    "Tuple congruence needs one original equality per ordered component.",
                ));
            }
            let mut components = Vec::with_capacity(children.len());
            for (index, ((left, right), child)) in
                left.args.iter().zip(&right.args).zip(children).enumerate()
            {
                match source_subject(child)? {
                    Fact::AtomicFact(AtomicFact::EqualFact(eq))
                        if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "TupleCongruence/ChildSubject",
                            "The child is not this exact ordered component equality.",
                        ))
                    }
                }
                let child_position = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                let compiled = self.compile_verify(child, &child_position)?;
                let formed =
                    SourcePosition::new(Some(&child_position), SourceOwner::Verify(child), 2);
                components.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(left, &formed)?,
                    self.compile_normalization_value(right, &formed)?,
                    compiled.1
                ));
            }
            return Ok(format!(
                "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext {}))",
                finite_vector_proof(&components),
            ));
        }
        let (Obj::FnObj(left), Obj::FnObj(right)) = (&fact.left, &fact.right) else {
            return self.compile_arithmetic_congruence(fact, children, position);
        };
        // The selected certificate flattens the shared suffix: outer groups
        // first, followed by the remaining callable prefix. Both calls retain
        // their original formation; no prefix equality is searched again.
        let group_arities: Vec<_> = left
            .body
            .iter()
            .rev()
            .zip(right.body.iter().rev())
            .map(|(left, right)| (left.len(), right.len()))
            .collect();
        if group_arities.is_empty()
            || group_arities
                .iter()
                .any(|(left, right)| left != right || *left == 0)
        {
            return Err(LeanCompileError::unsupported(
                "Equality/MatchingOneArgByOne/FunctionArity",
            ));
        }
        let multiple_groups = left.body.len() != 1 || right.body.len() != 1;
        let pairs = crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(
            &fact.left,
            &fact.right,
        )
        .ok_or_else(|| {
            LeanCompileError::new(
                "FunctionCongruence/Constructor",
                "The selected certificate does not peel these original function calls.",
            )
        })?;
        if children.len() != pairs.len() {
            return Err(LeanCompileError::new(
                "FunctionCongruence/Children",
                "Function congruence has the wrong ordered argument and head arity.",
            ));
        }
        let mut compiled = Vec::with_capacity(children.len());
        for (index, (result, (a, b))) in children.iter().zip(pairs).enumerate() {
            match source_subject(result)? {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == a.ir() && eq.right.ir() == b.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "FunctionCongruence/ChildSubject",
                        "The child is not this exact ordered argument or function-head equality.",
                    ))
                }
            }
            let child_position = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let checked = self.compile_verify(result, &child_position)?;
            if multiple_groups || left.body[0].len() > 2 {
                let formed =
                    SourcePosition::new(Some(&child_position), SourceOwner::Verify(result), 2);
                compiled.push(format!(
                    "(show {} = {} from {})",
                    self.compile_normalization_value(&a, &formed)?,
                    self.compile_normalization_value(&b, &formed)?,
                    checked.1
                ));
            } else {
                compiled.push(checked.1);
            }
        }
        self.compile_object_reference(&fact.left, position)?;
        self.compile_object_reference(&fact.right, position)?;
        let (head, arguments) = compiled
            .split_last()
            .ok_or_else(|| LeanCompileError::unsupported("FunctionCongruence/Children"))?;
        if !multiple_groups {
            return Self::function_call_congruence(head, arguments);
        }
        // All children were checked above in certificate order. Compose the
        // already checked equalities from the innermost shared group outward.
        let mut equality = head.clone();
        let mut end = arguments.len();
        for (arity, _) in group_arities.iter().rev() {
            let start = end - arity;
            equality = Self::function_call_congruence(&equality, &arguments[start..end])?;
            end = start;
        }
        Ok(equality)
    }

    pub(in crate::compile_to_lean) fn compile_arithmetic_congruence_strategy(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        // Preserve the exact producer gate;this strategy peels ArithmeticOperator only.
        if !matches!(
            (&fact.left, &fact.right),
            (Obj::ArithmeticOperator(_), Obj::ArithmeticOperator(_))
        ) {
            return Err(LeanCompileError::unsupported(
                "ArithmeticCongruence/Constructor",
            ));
        }
        let (_, pairs) = arithmetic_constructor_pairs(&fact.left, &fact.right)
            .ok_or_else(|| LeanCompileError::unsupported("ArithmeticCongruence/Constructor"))?;
        if requirements.len() != pairs.len() || children.len() != requirements.len() {
            return Err(LeanCompileError::new(
                "ArithmeticCongruence/Requirements",
                "The selected strategy has the wrong ordered requirement arity.",
            ));
        }
        for ((requirement, child), (left, right)) in requirements.iter().zip(children).zip(pairs) {
            let subject = source_subject(child)?;
            if subject.fact_id() != requirement.fact_id() || subject.ir() != requirement.ir() {
                return Err(LeanCompileError::new(
                    "ArithmeticCongruence/RequirementSubject",
                    "The child does not verify the exact recorded requirement and ID.",
                ));
            }
            match requirement {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ArithmeticCongruence/RequirementSubject",
                        "The requirement is not this exact ordered operand equality.",
                    ))
                }
            }
        }
        self.compile_arithmetic_congruence(fact, children, position)
    }

    pub(in crate::compile_to_lean) fn compile_arithmetic_congruence(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (operation, pairs) =
            arithmetic_constructor_pairs(&fact.left, &fact.right).ok_or_else(|| {
                LeanCompileError::unsupported("Equality/MatchingOneArgByOne/Constructor")
            })?;
        if children.len() != pairs.len() {
            return Err(LeanCompileError::new(
                "ArithmeticCongruence/Children",
                "Constructor congruence has the wrong ordered child arity.",
            ));
        }
        let mut compiled = Vec::new();
        for (index, (result, (left, right))) in children.iter().zip(pairs).enumerate() {
            let child_position = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let child = self.compile_verify(result, &child_position)?;
            match &source_subject(result)? {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ArithmeticCongruence/ChildSubject",
                        "Congruence child does not prove this exact ordered operand pair.",
                    ))
                }
            }
            // The child's closed WD lets cannot determine metavariables from
            // outside their scope. Give congrArg the exact semantic endpoints,
            // using only this child's two already checked formation stages.
            let formed = SourcePosition::new(Some(&child_position), SourceOwner::Verify(result), 2);
            compiled.push(format!(
                "(show {} = {} from {})",
                self.compile_normalization_value(left, &formed)?,
                self.compile_normalization_value(right, &formed)?,
                child.1,
            ));
        }
        let operation_term = arithmetic_operation_term(operation);
        if compiled.len() == 1 {
            Ok(format!("(congrArg {operation_term} {})", compiled[0]))
        } else if compiled.len() == 2 {
            Ok(format!(
                "(congrArg₂ {operation_term} {} {})",
                compiled[0], compiled[1]
            ))
        } else {
            curried_value_congruence(&operation_term, &compiled)
        }
    }

    // Source IR identifies signed literals with their explicit numeric
    // constructors. Replay that identity instead of treating it as Lean reduction.
    fn compile_same_ir_value(
        &self,
        left: &Obj,
        right: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if left.ir() != right.ir() {
            return Err(LeanCompileError::unsupported(
                "Equality/IdentityChildSubject",
            ));
        }
        if left == right {
            return Ok(format!(
                "(Litex.sameRefl {})",
                self.compile_object_reference(left, position)?
            ));
        }
        if matches!((left,right),
            (Obj::Literal(Literal::Number(_)),Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)))
                | (Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)),Obj::Literal(Literal::Number(_)))
            if matches!(p.arg.as_ref(),Obj::Literal(Literal::Number(_))))
        {
            let (negative, literal, reverse) = match (left, right) {
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)),
                    Obj::Literal(Literal::Number(n)),
                ) => (p, n, false),
                (
                    Obj::Literal(Literal::Number(n)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)),
                ) => (p, n, true),
                _ => unreachable!(),
            };
            let Obj::Literal(Literal::Number(unsigned)) = negative.arg.as_ref() else {
                unreachable!()
            };
            let unsigned = number_literal(unsigned, "ℂ")?;
            let signed = number_literal(literal, "ℂ")?;
            let proof=format!("((M.neg_numbers {unsigned}).trans (congrArg M.number (by norm_num : -{unsigned} = {signed})))");
            return Ok(if reverse {
                format!("({proof}).symm")
            } else {
                proof
            });
        }
        if let Some(value) = EvalRational::from_obj(left) {
            if EvalRational::from_obj(right).as_ref() == Some(&value) {
                let a = self.compile_numeric_observation(left, position)?;
                let b = self.compile_numeric_observation(right, position)?;
                if a.3.as_ref() != Some(&value) || b.3.as_ref() != Some(&value) {
                    return Err(LeanCompileError::unsupported(
                        "Equality/IdentityNumericCapture",
                    ));
                }
                return Ok(format!(
                    "(({}).trans ((congrArg M.number (by norm_num : {} = {})).trans ({}).symm))",
                    a.1, a.0, b.0, b.1
                ));
            }
        }
        if let Some((operation, pairs)) = arithmetic_constructor_pairs(left, right) {
            let children = pairs
                .into_iter()
                .map(|(a, b)| self.compile_same_ir_value(a, b, position))
                .collect::<Result<Vec<_>, _>>()?;
            return curried_value_congruence(&arithmetic_operation_term(operation), &children);
        }
        Ok(format!(
            "(show {} = {} from rfl)",
            self.compile_normalization_value(left, position)?,
            self.compile_normalization_value(right, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_identity(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &TheyAreTheSameProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            TheyAreTheSameProof::SameIr(_) if left.ir() == right.ir() => {
                self.compile_same_ir_value(left, right, position)
            }
            TheyAreTheSameProof::SameIr(_) => Err(LeanCompileError::new(
                "Equality/IdentitySubject",
                "Exact identity evidence has different source endpoints.",
            )),
            TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::SetBuilder(_)) => {
                let (
                    Obj::SetFormer(SetFormer::SetBuilder(left_set)),
                    Obj::SetFormer(SetFormer::SetBuilder(right_set)),
                ) = (left, right)
                else {
                    return Err(LeanCompileError::new(
                        "Equality/SetBuilderAlphaSubject",
                        "Set-builder alpha evidence requires two set builders.",
                    ));
                };
                if !set_builders_alpha_equal(left_set, right_set) {
                    return Err(LeanCompileError::new(
                        "Equality/SetBuilderAlphaSubject",
                        "The recorded endpoints differ beyond renaming bound parameters.",
                    ));
                }
                let left = self.compile_object_reference(left, position)?;
                let right = self.compile_object_reference(right, position)?;
                // Elaborate both dependent predicates before reflexivity is
                // used as an argument of an enclosing equality composition.
                Ok(format!("(by\n  let _left := {left}\n  let _right := {right}\n  exact (show Litex.Same _left _right from rfl))"))
            }
            TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::FnSet(_)) => {
                let (
                    Obj::FunctionSpace(FunctionSpace::FnSet(a)),
                    Obj::FunctionSpace(FunctionSpace::FnSet(b)),
                ) = (left, right)
                else {
                    return Err(LeanCompileError::unsupported("Equality/FnSetAlphaSubject"));
                };
                if !crate::execute::execute_fact_stmt::fn_sets_alpha_equal(a, b) {
                    return Err(LeanCompileError::unsupported("Equality/FnSetAlphaSubject"));
                }
                let left = self.compile_object_reference(left, position)?;
                let right = self.compile_object_reference(right, position)?;
                // A visible template conversion can retain a semanticObject
                // representation. Same compares denotations, so infer each
                // compiled endpoint's actual host independently.
                Ok(format!("(by\n  let _left := {left}\n  let _right := {right}\n  exact (show Litex.Same _left _right from rfl))"))
            }
            TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::AnonymousFn(_)) => {
                let (
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(a)),
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(b)),
                ) = (left, right)
                else {
                    return Err(LeanCompileError::unsupported(
                        "Equality/AnonymousFnAlphaSubject",
                    ));
                };
                if !crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::anonymous_fns_alpha_equal(a,b) {
                    return Err(LeanCompileError::unsupported("Equality/AnonymousFnAlphaSubject"));
                }
                let left = self.compile_object_reference(left, position)?;
                let right = self.compile_object_reference(right, position)?;
                Ok(format!("(by\n  let _left := {left}\n  let _right := {right}\n  exact (show Litex.Same _left _right from rfl))"))
            }
            TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::Compound(_)) => {
                let supported = matches!(
                    (left, right),
                    (Obj::ArithmeticOperator(_), Obj::ArithmeticOperator(_))
                        | (Obj::ComplexOperator(_), Obj::ComplexOperator(_))
                        | (
                            Obj::MatrixOperator(MatrixOperator::InnerProduct(_)),
                            Obj::MatrixOperator(MatrixOperator::InnerProduct(_))
                        )
                        | (
                            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(_)),
                            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(_))
                        )
                        | (
                            Obj::FunctionSpace(FunctionSpace::FnRange(_)),
                            Obj::FunctionSpace(FunctionSpace::FnRange(_))
                        )
                        | (
                            Obj::IteratedOperator(IteratedOperator::Sum(_)),
                            Obj::IteratedOperator(IteratedOperator::Sum(_))
                        )
                        | (
                            Obj::IteratedOperator(IteratedOperator::Product(_)),
                            Obj::IteratedOperator(IteratedOperator::Product(_))
                        )
                        | (
                            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_)),
                            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_))
                        )
                        | (
                            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)),
                            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_))
                        )
                        | (
                            Obj::IteratedOperator(IteratedOperator::Reduce(_)),
                            Obj::IteratedOperator(IteratedOperator::Reduce(_))
                        )
                        | (
                            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(_)),
                            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(_))
                        )
                        | (
                            Obj::ProductShape(ProductShape::Cart(_)),
                            Obj::ProductShape(ProductShape::Cart(_))
                        )
                        | (
                            Obj::ProductShape(ProductShape::Tuple(_)),
                            Obj::ProductShape(ProductShape::Tuple(_))
                        )
                        | (
                            Obj::FunctionSpace(FunctionSpace::Preimage(_)),
                            Obj::FunctionSpace(FunctionSpace::Preimage(_))
                        )
                        | (
                            Obj::FunctionSpace(FunctionSpace::PreimageSet(_)),
                            Obj::FunctionSpace(FunctionSpace::PreimageSet(_))
                        )
                        | (
                            Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)),
                            Obj::ExpLogOperator(ExpLogOperator::Sqrt(_))
                        )
                );
                if !supported || !crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(left,right) {
                    return Err(LeanCompileError::unsupported("Equality/FiniteAggregateAlphaSubject"));
                }
                let left = self.compile_object_reference(left, position)?;
                let right = self.compile_object_reference(right, position)?;
                Ok(format!("(by\n  let _left := {left}\n  let _right := {right}\n  exact (show Litex.Same _left _right from rfl))"))
            }
        }
    }
}
