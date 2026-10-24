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
        let mut candidates = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                candidates.extend(knowns.iter().cloned());
            }
        }
        // Candidate matching is read-only. Exact path queries borrow only
        // reachable edges; a caller-provided snapshot can still be reused.
        let mut adjacency = None;
        for known in candidates {
            let args = atomic_fact_args_ref(&known);
            if args.len() != goal_args.len() {
                continue;
            }
            let mut matches = Vec::new();
            for (left, right) in args.iter().zip(&goal_args) {
                let proof = match self.lookup_known_obj_equality_with_graph(
                    left,
                    right,
                    &mut adjacency,
                ) {
                    Some(proof) => proof,
                    // Stored-fact argument matching may also use a zero-premise
                    // algebraic identity such as `(a*b)*(c*d) = a*b*c*d`.
                    // This is a computed certificate, not a new truth search.
                    None if multiplication_association_shape(left)
                        && multiplication_association_shape(right) =>
                    {
                        let comparison = EqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: (*left).clone(),
                            right: (*right).clone(),
                            line_file: None,
                        };
                        let Some(calculation) = self
                            .search_equal_fact_by_calculation(
                                &comparison,
                                crate::execute::execute_fact_stmt::VerifyState::top_level(),
                            )
                            .ok()
                            .flatten()
                        else {
                            break;
                        };
                        EqualFactSearchedProof::ByBuiltinRule(
                            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByBuiltinRule::Calculation(
                                calculation,
                            ),
                        )
                    }
                    None => break,
                };
                matches.push(proof);
            }
            if matches.len() == args.len() {
                return Some(AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                    cite_fact_id: known.fact_id(),
                    why_parameters_of_known_fact_are_equal_to_givens: matches,
                });
            }
        }
        None
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
