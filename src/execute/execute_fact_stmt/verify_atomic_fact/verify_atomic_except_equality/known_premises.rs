//! Fixed premises use the read-only form of by_known. No WD, builtin, deep
//! search, or strategy is entered here; callers already established object WD.

use super::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{
    AtomicFact, GreaterEqualFact, GreaterFact, InFact, LessEqualFact, LessFact, NotEqualFact,
    NotSubsetFact, NotSupersetFact,
};
use crate::ast::obj::{Obj, StandardSet};
use crate::runtime::Runtime;

impl Runtime {
    pub(in crate::execute) fn known_not_equal_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_greater_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_less_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_greater_equal_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_less_equal_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_not_subset_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::NotSubsetFact(NotSubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_not_superset_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::NotSupersetFact(NotSupersetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    pub(in crate::execute) fn known_in_natural_proof(
        &mut self,
        element: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        });
        self.lookup_known_atomic_premise(fact)
    }

    // The enclosing order goal already checked this element's WD. The N+
    // carrier is intrinsic. Search truth at the supplied builtin-premise ceiling
    // so a declared function codomain can be cited without redefining raw known.
    pub(in crate::execute) fn search_in_positive_natural_premise(
        &mut self,
        element: &Obj,
        state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> crate::runtime::RuntimeResult<Option<AtomicExceptEqualityFactKnownProof>> {
        let fact = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: Obj::StandardSet(StandardSet::NPos),
            line_file: None,
        });
        let searched = self.search_atomic_except_equality_fact_proof(&fact, state)?;
        Ok(
            searched.map(|searched_proof| AtomicExceptEqualityFactKnownProof {
                fact,
                searched_proof: Box::new(searched_proof),
            }),
        )
    }
}
