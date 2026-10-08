use crate::ast::fact::{EqualFact, Fact};
use crate::ast::obj::Obj;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    EqualFactSearchedProof, KnownEqualityPathProof,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{FactId, Runtime, RuntimeResult};

#[cfg(test)]
#[path = "../../../tests/unit/execute/exact_property_lookup/tests.rs"]
mod exact_property_lookup_tests;

impl Runtime {
    /// Structural readers consume only this object's indexed properties.
    /// A directly recorded `f = fn(...) {...}` supplies a body; `f = g = h`
    /// does not authorize walking other objects' properties or equality classes.
    pub(crate) fn exact_property_object_values(
        &self,
        object: &Obj,
    ) -> Vec<(Obj, Vec<(Obj, Obj, FactId)>)> {
        let key = object.ir();
        let mut values = vec![(object.clone(), Vec::new())];
        for property in self.known_special_properties_of(object) {
            let SpecialProperty::Equality(fact) = property else {
                continue;
            };
            let value = if fact.left.ir() == key {
                fact.right
            } else if fact.right.ir() == key {
                fact.left
            } else {
                continue;
            };
            if values.iter().any(|(stored, _)| stored.ir() == value.ir()) {
                continue;
            }
            let path = vec![(object.clone(), value.clone(), fact.fact_id)];
            values.push((value, path));
        }
        values
    }

    pub(crate) fn exact_property_equality_path(
        &self,
        left: &Obj,
        right: &Obj,
    ) -> Option<Vec<(Obj, Obj, FactId)>> {
        let right_key = right.ir();
        self.exact_property_object_values(left)
            .into_iter()
            .find_map(|(value, path)| (value.ir() == right_key).then_some(path))
    }

    /// Pure identity/alpha comparison or one exact indexed equality citation.
    /// The existing path certificate records evidence, without graph discovery.
    pub(crate) fn lookup_exact_property_obj_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
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
        let path = self.exact_property_equality_path(left, right)?;
        Some(EqualFactSearchedProof::ByEquivalenceClass(
            KnownEqualityPathProof::new(path).into(),
        ))
    }

    // The stage dispatcher has already restricted this premise's permissions.
    pub(crate) fn verify_builtin_rule_premise(
        &mut self,
        premise: &Fact,
        premise_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        self.verify_fact(premise, premise_state)
    }
}
