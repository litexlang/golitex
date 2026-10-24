use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution;
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_atomic_builtin_rewrite(
        &self,
        goal: &AtomicFact,
        proof: &AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof) =>
                self.compile_atomic_equality_rewrite(
                    goal,
                    &proof.rewritten_fact,
                    &proof.cited_equal_fact_ids,
                    &proof.proof_of_rewritten_fact,
                    true,
                    position,
                ),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(proof) =>
                self.compile_atomic_equality_rewrite(
                    goal,
                    &proof.rewritten_fact,
                    &proof.cited_equal_fact_ids,
                    &proof.proof_of_rewritten_fact,
                    false,
                    position,
                ),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(proof) =>
                self.compile_atomic_function_unfold(goal, proof, position),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(proof) => self.compile_order_dual(goal, proof, position),
        }
    }

    fn compile_atomic_function_unfold(
        &self,
        goal: &AtomicFact,
        proof: &AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let residual = match &proof.rewritten_fact {
            Fact::AtomicFact(fact) if same_atomic_family(goal, fact) => fact,
            _ => return Err(LeanCompileError::new(
                "AtomicFnUnfold/Family",
                "The recorded residual changes the original predicate, polarity or argument arity.",
            )),
        };
        if proof.unfold_equal_proofs.is_empty() {
            return Err(LeanCompileError::new(
                "AtomicFnUnfold/Stages",
                "The selected function-unfold route has no actual equality verification.",
            ));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::AtomicFnUnfold(proof), 0);
        let original = atomic_fact_args_ref(goal);
        let rewritten = atomic_fact_args_ref(residual);
        let mut checked = Vec::new();
        let mut index = 0;
        for (argument, endpoint) in original.iter().zip(&rewritten) {
            if argument.ir() == endpoint.ir() {
                checked.push(None);
                continue;
            }
            if !matches!(argument, Obj::FnObj(_)) {
                return Err(LeanCompileError::new("AtomicFnUnfold/Argument", "Only an original top-level function application may change in this selected route."));
            }
            let equal = proof.unfold_equal_proofs.get(index).ok_or_else(|| {
                LeanCompileError::new(
                    "AtomicFnUnfold/Stages",
                    "A changed argument has no ordered actual unfolding equality.",
                )
            })?;
            match source_subject(equal)? {
                Fact::AtomicFact(AtomicFact::EqualFact(fact)) if fact.left.ir() == argument.ir() && fact.right.ir() == endpoint.ir() => {}
                _ => return Err(LeanCompileError::new("AtomicFnUnfold/EqualitySubject", "The recorded unfolding equality has another original argument or expanded endpoint.")),
            }
            checked.push(Some(
                self.compile_verify(
                    equal,
                    &SourcePosition {
                        before: index,
                        ..scope
                    },
                )?
                .1,
            ));
            index += 1;
        }
        if index != proof.unfold_equal_proofs.len() {
            return Err(LeanCompileError::new(
                "AtomicFnUnfold/Stages",
                "The payload adds or reorders an equality beyond the changed source arguments.",
            ));
        }
        let complete = SourcePosition {
            before: index,
            ..scope
        };
        if source_subject(&proof.proof_of_rewritten_fact)? != proof.rewritten_fact {
            return Err(LeanCompileError::new("AtomicFnUnfold/ChildSubject", "The successful child does not prove the exact original residual fact and identity."));
        }
        let child = self.compile_verify(&proof.proof_of_rewritten_fact, &complete)?;
        let original_terms = original
            .iter()
            .map(|arg| self.compile_object_reference(arg, &complete))
            .collect::<Result<Vec<_>, _>>()?;
        let rewritten_terms = rewritten
            .iter()
            .map(|arg| self.compile_object_reference(arg, &complete))
            .collect::<Result<Vec<_>, _>>()?;
        let variables = (0..original.len())
            .map(|index| format!("_unfold_arg{index}"))
            .collect::<Vec<_>>();
        let predicate = self.compile_atomic_raw_proposition(goal, &variables, &complete)?;
        let from = rewritten_terms
            .iter()
            .map(|term| format!("(Litex.denote {term})"))
            .collect::<Vec<_>>();
        let to = original_terms
            .iter()
            .map(|term| format!("(Litex.denote {term})"))
            .collect::<Vec<_>>();
        let mut current = from.clone();
        let mut equality = format!(
            "(Eq.refl ((fun {} => {predicate}) {}))",
            variables
                .iter()
                .map(|name| format!("({name} : M.Value)"))
                .collect::<Vec<_>>()
                .join(" "),
            current.join(" ")
        );
        for (index, argument) in checked.iter().enumerate() {
            let Some(argument) = argument else {
                continue;
            };
            let mut next = current.clone();
            next[index] = to[index].clone();
            let mut application = current.clone();
            application[index] = "_unfold_value".into();
            let congruence = format!("(congrArg (fun (_unfold_value : M.Value) => (fun {} => {predicate}) {}) ({argument}).symm)", variables.iter().map(|name| format!("({name} : M.Value)")).collect::<Vec<_>>().join(" "), application.join(" "));
            equality = format!("(({equality}).trans {congruence})");
            current = next;
        }
        // Semantic argument equalities transport this same captured predicate;
        // the child, equality verifications and actual definition routes stay live.
        Ok(format!("(by\n  change (fun {} => {predicate}) {}\n  have _unfold_child : (fun {} => {predicate}) {} := {}\n  exact Eq.mp {equality} _unfold_child\n)", variables.iter().map(|name| format!("({name} : M.Value)")).collect::<Vec<_>>().join(" "), to.join(" "), variables.iter().map(|name| format!("({name} : M.Value)")).collect::<Vec<_>>().join(" "), from.join(" "), child.1))
    }

    pub(in crate::compile_to_lean) fn compile_atomic_equality_rewrite(
        &self,
        goal: &AtomicFact,
        rewritten: &Fact,
        cited_ids: &[FactId],
        child: &VerifyFactResult,
        closed_numeric: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(
            goal,
            AtomicFact::InFact(_)
                | AtomicFact::IsSetFact(_)
                | AtomicFact::NotEqualFact(_)
                | AtomicFact::SubsetFact(_)
                | AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
        ) {
            return Err(LeanCompileError::unsupported(
                "Atomic/BuiltinRewrite/PredicateTransport",
            ));
        }
        let residual = match rewritten {
            Fact::AtomicFact(fact) if same_atomic_family(goal, fact) => fact,
            _ => {
                return Err(LeanCompileError::new(
                    "AtomicRewrite/Family",
                    "The residual changes the source predicate family, polarity or arity.",
                ))
            }
        };
        if cited_ids.is_empty()
            || cited_ids
                .iter()
                .enumerate()
                .any(|(index, id)| cited_ids[..index].contains(id))
        {
            return Err(LeanCompileError::new(
                "AtomicRewrite/Citations",
                "A substitution needs nonempty, nonduplicated recorded equality citations.",
            ));
        }
        let mut equalities = Vec::new();
        for id in cited_ids {
            let fact = self.resolve_fact(*id, position)?;
            let equality = match &fact {
                Fact::AtomicFact(AtomicFact::EqualFact(equality)) if equality.fact_id == *id => {
                    equality
                }
                _ => {
                    return Err(LeanCompileError::new(
                        "AtomicRewrite/CitationFamily",
                        "A substitution citation is not the recorded source equality.",
                    ))
                }
            };
            if *self.cited_fact_reference(*id, position)?.0 != fact {
                return Err(LeanCompileError::new(
                    "AtomicRewrite/CitationProducer",
                    "A substitution equality differs from its active compiled producer.",
                ));
            }
            equalities.push(equality.clone());
        }
        let compiled_child = self.compile_verify(child, position)?;
        if source_subject(child)? != *rewritten {
            return Err(LeanCompileError::new(
                "AtomicRewrite/ChildSubject",
                "The successful child does not prove the exact recorded residual fact.",
            ));
        }
        let after_residual =
            SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let position = &after_residual;
        let original_args = atomic_fact_args_ref(goal);
        let residual_args = atomic_fact_args_ref(residual);
        let changed = original_args
            .iter()
            .zip(&residual_args)
            .filter(|(original, residual)| original.ir() != residual.ir())
            .count();
        if changed == 0 || (!closed_numeric && changed != 1) {
            return Err(LeanCompileError::new(
                "AtomicRewrite/ChangedArguments",
                "The selected substitution has no changed argument or changes more than its one recorded path.",
            ));
        }
        let mut arguments = Vec::new();
        let mut used_ids = Vec::new();
        for (original, residual) in original_args.iter().zip(&residual_args) {
            if original.ir() == residual.ir() {
                arguments.push(format!(
                    "(Litex.sameRefl {})",
                    self.compile_object_reference(residual, position)?
                ));
                continue;
            }
            if closed_numeric {
                // Replay either the exact whole-argument endpoint or the
                // captured substitutions under matching arithmetic constructors.
                // Keep the original residual AST, without recalculating it.
                if ClosedNumericExpr::try_from_obj(original).is_some()
                    || ClosedNumericExpr::try_from_obj(residual).is_none()
                {
                    return Err(LeanCompileError::unsupported(
                        "AtomicRewrite/ClosedTopLevelSubject",
                    ));
                }
                let matching: Vec<_> = equalities
                    .iter()
                    .enumerate()
                    .filter(|(_, equality)| {
                        (equality.left.ir() == original.ir()
                            && equality.right.ir() == residual.ir())
                            || (equality.right.ir() == original.ir()
                                && equality.left.ir() == residual.ir())
                    })
                    .collect();
                if matching.is_empty() && arithmetic_constructor_pairs(original, residual).is_some()
                {
                    let cited = cited_ids
                        .iter()
                        .copied()
                        .zip(equalities.iter().cloned())
                        .collect::<Vec<_>>();
                    let equality = self.compile_cited_equality_substitution(
                        original,
                        residual,
                        &cited,
                        &mut used_ids,
                        position,
                    )?;
                    arguments.push(format!("({equality}).symm"));
                    continue;
                }
                if matching.len() != 1 {
                    return Err(LeanCompileError::new(
                        "AtomicRewrite/ClosedTopLevelCitation",
                        "A changed whole argument needs one selected equality with those exact original and closed residual endpoints.",
                    ));
                }
                let id = cited_ids[matching[0].0];
                if !used_ids.contains(&id) {
                    used_ids.push(id);
                }
                arguments.push(self.compile_registered_equality(id, residual, original, position)?);
            } else {
                // KnownEqualObj records one ordered path for one top-level
                // argument. Only its listed edges can choose the next endpoint.
                let mut current: Obj = (**original).clone();
                let mut path = format!(
                    "(Litex.sameRefl {})",
                    self.compile_object_reference(original, position)?
                );
                for (id, equality) in cited_ids.iter().zip(&equalities) {
                    let next = if equality.left.ir() == current.ir() {
                        &equality.right
                    } else if equality.right.ir() == current.ir() {
                        &equality.left
                    } else {
                        return Err(LeanCompileError::new(
                            "AtomicRewrite/PathOrder",
                            "The recorded equality does not continue the ordered substitution path.",
                        ));
                    };
                    if next.ir() == current.ir() {
                        return Err(LeanCompileError::new(
                            "AtomicRewrite/PathProgress",
                            "A substitution path edge does not change its source endpoint.",
                        ));
                    }
                    let edge = self.compile_registered_equality(*id, &current, next, position)?;
                    path = format!("(({path}).trans {edge})");
                    current = next.clone();
                    used_ids.push(*id);
                }
                if current.ir() != residual.ir() {
                    return Err(LeanCompileError::new(
                        "AtomicRewrite/PathEndpoint",
                        "The recorded substitution path does not end at this residual argument.",
                    ));
                }
                arguments.push(format!("({path}).symm"));
            }
        }
        if used_ids.as_slice() != cited_ids {
            return Err(LeanCompileError::new(
                "AtomicRewrite/CitationOrder",
                "Every recorded equality must be used in its source substitution order.",
            ));
        }
        match (residual, goal) {
            (AtomicFact::InFact(from), AtomicFact::InFact(to)) => Ok(format!(
                "(Litex.inOfSame {} {} {} {} {} {} {})",
                self.compile_object_reference(&from.element, position)?,
                self.compile_object_reference(&to.element, position)?,
                self.compile_object_reference(&from.set, position)?,
                self.compile_object_reference(&to.set, position)?,
                arguments[0],
                arguments[1],
                compiled_child.1,
            )),
            (AtomicFact::SubsetFact(from), AtomicFact::SubsetFact(to)) => Ok(format!(
                "(Litex.subsetOfSame {} {} {} {} {} {} {})",
                self.compile_object_reference(&from.left, position)?,
                self.compile_object_reference(&from.right, position)?,
                self.compile_object_reference(&to.left, position)?,
                self.compile_object_reference(&to.right, position)?,
                arguments[0],
                arguments[1],
                compiled_child.1,
            )),
            (AtomicFact::IsSetFact(from), AtomicFact::IsSetFact(to)) => Ok(format!(
                "(Litex.isSetOfSame {} {} {} {})",
                self.compile_object_reference(&from.set, position)?,
                self.compile_object_reference(&to.set, position)?,
                arguments[0],
                compiled_child.1,
            )),
            (AtomicFact::NotEqualFact(from), AtomicFact::NotEqualFact(to)) => Ok(format!(
                "(Litex.notSameOfSame {} {} {} {} {} {} {})",
                self.compile_object_reference(&from.left, position)?,
                self.compile_object_reference(&to.left, position)?,
                self.compile_object_reference(&from.right, position)?,
                self.compile_object_reference(&to.right, position)?,
                arguments[0],
                arguments[1],
                compiled_child.1,
            )),
            (
                from @ (AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)),
                to @ (AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)),
            ) => self.compile_order_known_atomic_transport(
                from,
                to,
                &arguments,
                &compiled_child.1,
                position,
            ),
            (
                from @ (AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)),
                to @ (AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)),
            ) => {
                // Negation reverses the implication: move a hypothetical
                // positive goal to the residual, then apply the checked child.
                // These polarity views retain the original IDs and create no
                // verification result or new equality evidence.
                let positive_goal = crate::ast::fact::negate_atomic_fact(to, to.fact_id())
                    .ok_or_else(|| LeanCompileError::unsupported("AtomicRewrite/OrderNegation"))?;
                let positive_residual = crate::ast::fact::negate_atomic_fact(from, from.fact_id())
                    .ok_or_else(|| LeanCompileError::unsupported("AtomicRewrite/OrderNegation"))?;
                let reverse_arguments = arguments
                    .iter()
                    .map(|proof| format!("({proof}).symm"))
                    .collect::<Vec<_>>();
                let transported = self.compile_order_known_atomic_transport(
                    &positive_goal,
                    &positive_residual,
                    &reverse_arguments,
                    "_rewrite_positive",
                    position,
                )?;
                Ok(format!(
                    "(fun _rewrite_positive => ({}) {transported})",
                    compiled_child.1,
                ))
            }
            _ => Err(LeanCompileError::unsupported(
                "Atomic/BuiltinRewrite/PredicateTransport",
            )),
        }
    }
}
