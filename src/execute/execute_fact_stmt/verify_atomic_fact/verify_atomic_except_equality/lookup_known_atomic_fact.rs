use super::{result::AtomicExceptEqualityFactKnownProof, AtomicExceptEqualityFactSearchedProof};
use crate::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity, AtomicFact, EqualFact,
};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::EquivalenceClassAdjacency;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, EqualFactSearchedProof,
};
use crate::runtime::Runtime;

impl Runtime {
    // The lookup form of by_known is for cite-only premises. Unlike normal
    // known-atomic argument matching, it cannot enter any verifier search.
    pub(in crate::execute) fn lookup_atomic_except_equality_fact_proof_by_known(
        &mut self,
        fact: &AtomicFact,
    ) -> Option<AtomicExceptEqualityFactSearchedProof> {
        if let Some(proof) = self.lookup_known_atomic_fact(fact) {
            return Some(AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                proof,
            ));
        }
        None
    }

    pub(in crate::execute) fn lookup_known_atomic_premise(
        &mut self,
        fact: AtomicFact,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let searched_proof = self.lookup_atomic_except_equality_fact_proof_by_known(&fact)?;
        Some(AtomicExceptEqualityFactKnownProof {
            fact,
            searched_proof: Box::new(searched_proof),
        })
    }

    // Read stored facts and stored equality paths only. In particular, never
    // enter WD, constructor congruence, peer comparison, or another truth search.
    pub(in crate::execute) fn lookup_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
    ) -> Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return None;
        }
        let key = (fact.prop_name(), atomic_fact_has_positive_polarity(fact));
        let goal_args = atomic_fact_args_ref(fact);
        // Membership already has a subject index. Check the submitted object
        // before scanning other subjects or exposing equality candidates.
        if let AtomicFact::InFact(member) = fact {
            let subject = member.element.ir();
            let direct = self.execution_environments_stack.iter().rev().find_map(|env| {
                env.special_properties.get(&subject)?.memberships.iter().find(|known| {
                    super::super::verify_equality::equivalence_class_graph::objects_match_directly(&known.set, &member.set)
                }).cloned()
            });
            if let Some(known) = direct {
                if let Some(proof) =
                    self.match_known_atomic_lookup(fact, &AtomicFact::InFact(known))
                {
                    return Some(proof);
                }
            }
        }
        let mut equivalents =
            super::super::verify_equality::equivalence_class_graph::EquivalentArguments::new(
                &goal_args,
                self.execution_environments_stack.len(),
            );
        let mut attempted = std::collections::HashSet::new();
        loop {
            // Borrow the bucket until a compatible source is found. Only that
            // source is cloned for proof construction, after the borrow ends.
            let candidate = self
                .execution_environments_stack
                .iter()
                .rev()
                .find_map(|env| {
                    env.facts
                        .known_atomic_except_equality_facts
                        .by_prop
                        .get(&key)?
                        .iter()
                        .find(|known| {
                            !attempted.contains(&known.fact_id())
                                && equivalents.matches(&atomic_fact_args_ref(known))
                        })
                        .cloned()
                });
            if let Some(known) = candidate {
                attempted.insert(known.fact_id());
                if let Some(proof) = self.match_known_atomic_lookup(fact, &known) {
                    return Some(proof);
                }
                continue;
            }
            if !equivalents.advance(self) {
                break;
            }
        }
        // Keep the existing multiplication certificate fallback. It is needed
        // only for sources containing a multiplication argument on both sides.
        for env_index in (0..self.execution_environments_stack.len()).rev() {
            let count = self.execution_environments_stack[env_index]
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
                .map_or(0, Vec::len);
            for index in 0..count {
                let known = &self.execution_environments_stack[env_index]
                    .facts
                    .known_atomic_except_equality_facts
                    .by_prop[&key][index];
                if attempted.contains(&known.fact_id()) {
                    continue;
                }
                let args = atomic_fact_args_ref(known);
                if args.len() != goal_args.len()
                    || !args.iter().zip(&goal_args).any(|(left, right)| {
                        multiplication_association_shape(left)
                            && multiplication_association_shape(right)
                    })
                {
                    continue;
                }
                let known = known.clone();
                if let Some(proof) = self.match_known_atomic_lookup(fact, &known) {
                    return Some(proof);
                }
            }
        }
        None
    }

    fn match_known_atomic_lookup(
        &mut self,
        goal: &AtomicFact,
        known: &AtomicFact,
    ) -> Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact> {
        let goal_args = atomic_fact_args_ref(goal);
        let args = atomic_fact_args_ref(known);
        if args.len() != goal_args.len() {
            return None;
        }
        let mut matches = Vec::new();
        for (left, right) in args.iter().zip(&goal_args) {
            let proof = match self.lookup_known_obj_equality(left, right) {
                Some(proof) => proof,
                None if multiplication_association_shape(left)
                    && multiplication_association_shape(right) =>
                {
                    let comparison = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: (*left).clone(),
                        right: (*right).clone(),
                        line_file: None,
                    };
                    let calculation = self
                        .search_equal_fact_by_calculation(
                            &comparison,
                            crate::execute::execute_fact_stmt::VerifyState::top_level(),
                        )
                        .ok()
                        .flatten()?;
                    EqualFactSearchedProof::ByBuiltinRule(
                        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByBuiltinRule::Calculation(calculation),
                    )
                }
                None => return None,
            };
            matches.push(proof);
        }
        Some(AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
            cite_fact_id: known.fact_id(),
            why_parameters_of_known_fact_are_equal_to_givens: matches,
        })
    }

    pub(in crate::execute) fn lookup_known_obj_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<EqualFactSearchedProof> {
        self.lookup_known_obj_equality_with_graph(left, right, &mut None)
    }

    pub(in crate::execute) fn lookup_known_obj_equality_with_graph(
        &mut self,
        left: &Obj,
        right: &Obj,
        adjacency: &mut Option<EquivalenceClassAdjacency>,
    ) -> Option<EqualFactSearchedProof> {
        let comparison = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        };
        if let Some(proof) = search_equal_fact_proof_by_they_are_the_same(&comparison) {
            return Some(proof.into());
        }
        let path = match adjacency.as_ref() {
            Some(graph) => super::super::verify_equality::equivalence_class_graph::equivalence_class_path_in_adjacency(graph, left, right),
            None => self.equivalence_class_path(left, right),
        };
        if let Some(path) = path {
            return Some(EqualFactSearchedProof::ByEquivalenceClass(
                KnownEqualityPathProof::new(path).into(),
            ));
        }
        // Direct compares the submitted pair and follows exact stored paths.
        // It does not scan unrelated graph endpoints for an alpha bridge.
        None
    }
}
// Only a multiplication tree's associativity/commutativity is accepted here.
// Addition/subtraction/division identities keep their dedicated rules and
// premise checks; known-fact matching must not silently simplify `x - 0` to
// `x` in an order obligation.
fn multiplication_association_shape(obj: &Obj) -> bool {
    if !matches!(
        obj,
        Obj::ArithmeticOperator(crate::ast::obj::ArithmeticOperator::Mul(_))
    ) {
        return false;
    }
    fn only_mul_nodes(obj: &Obj) -> bool {
        match obj {
            Obj::ArithmeticOperator(crate::ast::obj::ArithmeticOperator::Mul(m)) => {
                only_mul_nodes(&m.left) && only_mul_nodes(&m.right)
            }
            _ => true,
        }
    }
    only_mul_nodes(obj)
}
