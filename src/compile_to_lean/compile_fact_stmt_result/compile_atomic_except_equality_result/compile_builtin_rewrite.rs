use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
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
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(_) =>
                Err(LeanCompileError::unsupported("Atomic/BuiltinRewrite/FnUnfold")),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(proof) => self.compile_order_dual(goal, proof, position),
        }
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
            AtomicFact::InFact(_) | AtomicFact::IsSetFact(_) | AtomicFact::NotEqualFact(_)
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
                // A whole-argument alias keeps the exact closed endpoint of
                // its selected source equality. The source producer preserves
                // that closed AST rather than replacing it by a computed value.
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
            _ => Err(LeanCompileError::unsupported(
                "Atomic/BuiltinRewrite/PredicateTransport",
            )),
        }
    }
}
