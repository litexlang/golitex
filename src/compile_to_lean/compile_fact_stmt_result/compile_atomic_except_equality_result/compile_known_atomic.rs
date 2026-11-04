use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_known_atomic(
        &self,
        proof: &AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
        goal: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if matches!(goal, AtomicFact::EqualFact(_)) {
            return Err(LeanCompileError::new(
                "KnownAtomic/Family",
                "Non-equality citation evidence cannot select the equality family.",
            ));
        }
        let resolved = self.resolve_fact(proof.cite_fact_id, position)?;
        let cited = match &resolved {
            Fact::AtomicFact(cited) => cited,
            _ => {
                return Err(LeanCompileError::new(
                    "KnownAtomic",
                    "Citation resolves to a non-atomic fact.",
                ))
            }
        };
        let registered = self.cited_fact_reference(proof.cite_fact_id, position)?;
        if *registered.0 != resolved || !same_atomic_family(cited, goal) {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Citation differs from its registered producer or target family.",
            ));
        }
        let cited_args = atomic_fact_args_ref(cited);
        let goal_args = atomic_fact_args_ref(goal);
        if proof.why_parameters_of_known_fact_are_equal_to_givens.len() != goal_args.len() {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Argument equality evidence has the wrong ordered arity.",
            ));
        }
        let mut arguments = Vec::new();
        let mut exact_identity = true;
        for ((cited, given), equality) in cited_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.why_parameters_of_known_fact_are_equal_to_givens)
        {
            // This source stage retains a winner rather than a second fact/WD
            // wrapper. Its exact endpoints come from the citation and target.
            // The local obligation view is never registered as a source fact.
            let obligation = EqualFact {
                fact_id: goal.fact_id(),
                left: (*cited).clone(),
                right: (*given).clone(),
                line_file: None,
            };
            arguments.push(self.compile_equality_search(&obligation, equality, position)?);
            exact_identity &= cited.ir() == given.ir()
                && matches!(
                    equality,
                    EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                );
        }
        if exact_identity {
            return Ok(registered.1);
        }
        if matches!(
            cited,
            AtomicFact::MultivariableAnalysisFact(_) | AtomicFact::NotMultivariableAnalysisFact(_)
        ) {
            return self.compile_multivariable_predicate_transport(
                cited,
                goal,
                &arguments,
                &registered.1,
                position,
            );
        }
        match (cited, goal) {
            (AtomicFact::InFact(known), AtomicFact::InFact(given)) => Ok(format!(
                "(Litex.inOfSame {} {} {} {} {} {} {})",
                self.compile_object_reference(&known.element, position)?,
                self.compile_object_reference(&given.element, position)?,
                self.compile_object_reference(&known.set, position)?,
                self.compile_object_reference(&given.set, position)?,
                arguments[0],
                arguments[1],
                registered.1,
            )),
            (AtomicFact::IsSetFact(known), AtomicFact::IsSetFact(given)) => Ok(format!(
                "(Litex.isSetOfSame {} {} {} {})",
                self.compile_object_reference(&known.set, position)?,
                self.compile_object_reference(&given.set, position)?,
                arguments[0],
                registered.1,
            )),
            (AtomicFact::SubsetFact(known), AtomicFact::SubsetFact(given)) => Ok(format!(
                "(Litex.subsetOfSame {} {} {} {} {} {} {})",
                self.compile_object_reference(&known.left, position)?,
                self.compile_object_reference(&known.right, position)?,
                self.compile_object_reference(&given.left, position)?,
                self.compile_object_reference(&given.right, position)?,
                arguments[0],
                arguments[1],
                registered.1,
            )),
            (AtomicFact::NotEqualFact(known), AtomicFact::NotEqualFact(given)) => Ok(format!(
                "(Litex.notSameOfSame {} {} {} {} {} {} {})",
                self.compile_object_reference(&known.left, position)?,
                self.compile_object_reference(&given.left, position)?,
                self.compile_object_reference(&known.right, position)?,
                self.compile_object_reference(&given.right, position)?,
                arguments[0],
                arguments[1],
                registered.1,
            )),
            (
                known @ (AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)),
                given @ (AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)),
            ) => self.compile_order_known_atomic_transport(
                known,
                given,
                &arguments,
                &registered.1,
                position,
            ),
            _ if matches!(
                goal,
                AtomicFact::NormalAtomicFact(_)
                    | AtomicFact::NotNormalAtomicFact(_)
                    | AtomicFact::IsNonemptySetFact(_)
                    | AtomicFact::IsFiniteSetFact(_)
                    | AtomicFact::SupersetFact(_)
                    | AtomicFact::NotSupersetFact(_)
                    | AtomicFact::ProperSubsetFact(_)
                    | AtomicFact::NotProperSubsetFact(_)
                    | AtomicFact::ProperSupersetFact(_)
                    | AtomicFact::NotProperSupersetFact(_)
                    | AtomicFact::NotIsSetFact(_)
                    | AtomicFact::NotIsNonemptySetFact(_)
                    | AtomicFact::NotIsFiniteSetFact(_)
                    | AtomicFact::PrimeFact(_)
                    | AtomicFact::NotPrimeFact(_)
                    | AtomicFact::CoprimeFact(_)
                    | AtomicFact::NotCoprimeFact(_)
                    | AtomicFact::DvdFact(_)
                    | AtomicFact::NotDvdFact(_)
                    | AtomicFact::SequenceAnalysisFact(_)
                    | AtomicFact::NotSequenceAnalysisFact(_)
                    | AtomicFact::HasSequenceLimsupFact(_)
                    | AtomicFact::NotHasSequenceLimsupFact(_)
                    | AtomicFact::HasSequenceLiminfFact(_)
                    | AtomicFact::NotHasSequenceLiminfFact(_)
                    | AtomicFact::HasDerivativeAtFact(_)
                    | AtomicFact::NotHasDerivativeAtFact(_)
                    | AtomicFact::FunctionDifferentiableAtFact(_)
                    | AtomicFact::NotFunctionDifferentiableAtFact(_)
                    | AtomicFact::HasSequenceLimitFact(_)
                    | AtomicFact::NotHasSequenceLimitFact(_)
                    | AtomicFact::HasFunctionLimitFact(_)
                    | AtomicFact::NotHasFunctionLimitFact(_)
                    | AtomicFact::HasRiemannIntegralFact(_)
                    | AtomicFact::NotHasRiemannIntegralFact(_)
                    | AtomicFact::FunctionRiemannIntegrableFact(_)
                    | AtomicFact::NotFunctionRiemannIntegrableFact(_)
                    | AtomicFact::FunctionContinuousAtFact(_)
                    | AtomicFact::NotFunctionContinuousAtFact(_)
                    | AtomicFact::FunctionContinuousFact(_)
                    | AtomicFact::NotFunctionContinuousFact(_)
                    | AtomicFact::FunctionLipschitzFact(_)
                    | AtomicFact::NotFunctionLipschitzFact(_)
                    | AtomicFact::RealAccumulationFact(_)
                    | AtomicFact::NotRealAccumulationFact(_)
                    | AtomicFact::RealSetBoundFact(_)
                    | AtomicFact::NotRealSetBoundFact(_)
                    | AtomicFact::RealSetBoundedFact(_)
                    | AtomicFact::NotRealSetBoundedFact(_)
            ) =>
            {
                self.compile_raw_atomic_transport(cited, goal, &arguments, &registered.1, position)
            }
            _ => Err(LeanCompileError::unsupported(
                "KnownAtomic/PredicateTransport",
            )),
        }
    }

    // Same is equality of M.Value denotations, not equality of the host Obj
    // carriers. The preceding dispatcher has checked the original predicate,
    // polarity, ordered arity, citation and every selected equality winner.
    pub(in crate::compile_to_lean) fn compile_raw_atomic_transport(
        &self,
        cited: &AtomicFact,
        goal: &AtomicFact,
        arguments: &[String],
        citation: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !same_atomic_family(cited, goal)
            || atomic_fact_args_ref(cited).len() != arguments.len()
            || atomic_fact_args_ref(goal).len() != arguments.len()
        {
            return Err(LeanCompileError::unsupported(
                "AtomicTransport/FamilyOrArity",
            ));
        }
        if arguments.is_empty() {
            return Ok(citation.into());
        }
        let variables = (0..arguments.len())
            .map(|index| format!("_known_argument_{index}"))
            .collect::<Vec<_>>();
        let binders = variables
            .iter()
            .map(|variable| format!("({variable} : M.Value)"))
            .collect::<Vec<_>>()
            .join(" ");
        // User predicates use their prior declaration; builtin predicates use
        // their fixed meaning. Neither route performs new proof search.
        let meaning = self.compile_atomic_raw_proposition(goal, &variables, position)?;
        let predicate = format!("(fun {binders} => {meaning})");
        let values = |fact: &AtomicFact| {
            atomic_fact_args_ref(fact)
                .iter()
                .map(|argument| {
                    // Consume the original formed object before choosing its
                    // value representation. A range's fixed semantic value
                    // avoids copying a closed function's WD into every use of
                    // the transported predicate. If that value renderer cannot
                    // express this already-checked object, retain its original
                    // representation; no source WD or equality is reconstructed.
                    let object = self.compile_object_reference(argument, position)?;
                    if matches!(argument, Obj::FunctionSpace(FunctionSpace::FnRange(_))) {
                        if let Ok(value) = self.compile_function_raw_expression_bound(
                            argument,
                            position,
                            &std::collections::HashMap::new(),
                        ) {
                            return Ok(value);
                        }
                    }
                    Ok(format!("(Litex.denote {object})"))
                })
                .collect::<Result<Vec<_>, LeanCompileError>>()
        };
        let cited_values = values(cited)?;
        let goal_values = values(goal)?;
        let apply = |values: &[String]| format!("({predicate} {})", values.join(" "));
        let mut current = cited_values.clone();
        let mut equality = format!("(Eq.refl {})", apply(&current));
        let mut checked_equalities = Vec::new();
        for (index, argument_equality) in arguments.iter().enumerate() {
            let name = format!("_known_argument_eq_{index}");
            checked_equalities.push(format!(
                "have {name} : {} = {} := {argument_equality}",
                cited_values[index], goal_values[index]
            ));
            let mut changed = current.clone();
            changed[index] = "_known_value".to_string();
            let lifted = format!(
                "(congrArg (fun (_known_value : M.Value) => {}) {name})",
                apply(&changed),
            );
            equality = format!("(({equality}).trans {lifted})");
            current[index] = goal_values[index].clone();
        }
        Ok(format!(
            "(show {} from by\n  {}\n  have _known_citation : {} := {citation}\n  exact Eq.mp {equality} _known_citation\n)",
            apply(&goal_values),
            checked_equalities.join("\n").replace('\n', "\n  "),
            apply(&cited_values),
        ))
    }
}
