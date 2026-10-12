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
            (AtomicFact::NormalAtomicFact(_), AtomicFact::NormalAtomicFact(_)) => self
                .compile_concrete_known_atomic_transport(
                    cited,
                    goal,
                    &arguments,
                    &registered.1,
                    position,
                ),
            _ => Err(LeanCompileError::unsupported(
                "KnownAtomic/PredicateTransport",
            )),
        }
    }

    // Same is equality of M.Value denotations, not equality of the host Obj
    // carriers. The preceding dispatcher has checked the original predicate,
    // polarity, ordered arity, citation and every selected equality winner.
    fn compile_concrete_known_atomic_transport(
        &self,
        cited: &AtomicFact,
        goal: &AtomicFact,
        arguments: &[String],
        citation: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let variables = (0..arguments.len())
            .map(|index| format!("_known_argument_{index}"))
            .collect::<Vec<_>>();
        let binders = variables
            .iter()
            .map(|variable| format!("({variable} : M.Value)"))
            .collect::<Vec<_>>()
            .join(" ");
        // This renderer uses the actual prior concrete declaration and its
        // IdentifierIds. It does not run definition verification or search.
        let meaning = self.compile_atomic_raw_proposition(goal, &variables, position)?;
        let predicate = format!("(fun {binders} => {meaning})");
        let values = |fact: &AtomicFact| {
            atomic_fact_args_ref(fact)
                .iter()
                .map(|argument| {
                    self.compile_object_reference(argument, position)
                        .map(|object| format!("(Litex.denote {object})"))
                })
                .collect::<Result<Vec<_>, LeanCompileError>>()
        };
        let cited_values = values(cited)?;
        let goal_values = values(goal)?;
        let apply = |values: &[String]| format!("({predicate} {})", values.join(" "));
        let mut current = cited_values.clone();
        let mut equality = format!("(Eq.refl {})", apply(&current));
        for (index, argument_equality) in arguments.iter().enumerate() {
            let mut changed = current.clone();
            changed[index] = "_known_value".to_string();
            let lifted = format!(
                "(congrArg (fun (_known_value : M.Value) => {}) {argument_equality})",
                apply(&changed),
            );
            equality = format!("(({equality}).trans {lifted})");
            current[index] = goal_values[index].clone();
        }
        Ok(format!(
            "(show {} from by\n  have _known_citation : {} := {citation}\n  exact Eq.mp {equality} _known_citation\n)",
            apply(&goal_values),
            apply(&cited_values),
        ))
    }
}
