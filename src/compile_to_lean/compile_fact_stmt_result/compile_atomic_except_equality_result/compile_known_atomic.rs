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
        if cited_args.len() != goal_args.len()
            || proof.why_parameters_of_known_fact_are_equal_to_givens.len() != goal_args.len()
        {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Argument equality evidence has the wrong ordered arity.",
            ));
        }
        // SameIr is an empty identity witness. With the exact same original
        // argument objects, the cited proposition already is the target. No
        // new host constructor is needed merely to emit reflexivity, including
        // for value-level subjects introduced by a retained inference rule.
        if cited_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.why_parameters_of_known_fact_are_equal_to_givens)
            .all(|((cited, given), equality)| {
                cited == given
                    && matches!(
                        equality,
                        EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                    )
            })
        {
            return Ok(registered.1);
        }
        let mut arguments = Vec::new();
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
            // Predicate meaning belongs to the shared raw renderer. It fails
            // closed for an unmodeled family; the original citation and all
            // ordered equality certificates have already been checked above.
            _ => {
                self.compile_raw_atomic_transport(cited, goal, &arguments, &registered.1, position)
            }
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
                    if matches!(
                        argument,
                        Obj::ArithmeticOperator(_) | Obj::FunctionSpace(FunctionSpace::FnRange(_))
                    ) {
                        if let Ok(value) = self.compile_normalization_value(argument, position) {
                            let bridge =
                                self.compile_normalization_denotation(argument, position)?;
                            return Ok((value, bridge));
                        }
                    }
                    Ok((format!("(Litex.denote {object})"), "rfl".to_string()))
                })
                .collect::<Result<Vec<_>, LeanCompileError>>()
        };
        let (cited_values, cited_bridges): (Vec<_>, Vec<_>) = values(cited)?.into_iter().unzip();
        let (goal_values, goal_bridges): (Vec<_>, Vec<_>) = values(goal)?.into_iter().unzip();
        let apply = |values: &[String]| format!("({predicate} {})", values.join(" "));
        let mut current = cited_values.clone();
        let mut equality = format!("(Eq.refl {})", apply(&current));
        let mut checked_equalities = Vec::new();
        for (index, argument_equality) in arguments.iter().enumerate() {
            let name = format!("_known_argument_eq_{index}");
            // Equality evidence relates the original WD representations. When
            // the predicate uses raw values, cross that boundary explicitly;
            // equal source IR does not make cached host constructors reduce.
            let endpoint_equality = if cited_bridges[index] == "rfl" && goal_bridges[index] == "rfl"
            {
                argument_equality.clone()
            } else {
                format!(
                    "(({}).symm.trans (({argument_equality}).trans ({})))",
                    cited_bridges[index], goal_bridges[index]
                )
            };
            checked_equalities.push(format!(
                "have {name} : {} = {} := {endpoint_equality}",
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
