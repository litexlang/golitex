use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    EqualFactSearchedProof, KnownEqualityPathProof,
};
use crate::prelude::*;
use std::collections::HashSet;

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
        let mut values = vec![(object.clone(), Vec::new())];
        values.extend(self.known_direct_equal_object_values(object, None));
        values
    }

    /// A matching literal first, followed by direct equality candidates in
    /// their original scope/source order. Unrelated buckets are never cloned.
    pub(crate) fn exact_property_object_values_of_shapes(
        &self,
        object: &Obj,
        shapes: &[EqualToObjShape],
    ) -> Vec<(Obj, Vec<(Obj, Obj, FactId)>)> {
        let mut values = Vec::new();
        if shapes.contains(&EqualToObjShape::of(object)) {
            values.push((object.clone(), Vec::new()));
        }
        values.extend(self.known_direct_equal_object_values(object, Some(shapes)));
        values
    }

    /// Stored equality bodies only; a bare anonymous literal is not a citation.
    pub(crate) fn known_equal_to_anonymous_functions(
        &self,
        object: &Obj,
    ) -> Vec<(AnonymousFn, Vec<(Obj, Obj, FactId)>)> {
        let mut functions = Vec::new();
        for (value, path) in
            self.known_direct_equal_object_values(object, Some(&[EqualToObjShape::AnonymousFn]))
        {
            if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = value {
                functions.push((function, path));
            }
        }
        functions
    }

    pub(crate) fn known_equal_to_tuples(
        &self,
        object: &Obj,
    ) -> Vec<(Tuple, Vec<(Obj, Obj, FactId)>)> {
        let mut tuples = Vec::new();
        for (value, path) in
            self.known_direct_equal_object_values(object, Some(&[EqualToObjShape::Tuple]))
        {
            if let Obj::ProductShape(ProductShape::Tuple(tuple)) = value {
                tuples.push((tuple, path));
            }
        }
        tuples
    }

    pub(crate) fn known_equal_to_carts(
        &self,
        object: &Obj,
    ) -> Vec<(Cart, Vec<(Obj, Obj, FactId)>)> {
        let mut carts = Vec::new();
        for (value, path) in
            self.known_direct_equal_object_values(object, Some(&[EqualToObjShape::Cart]))
        {
            if let Obj::ProductShape(ProductShape::Cart(cart)) = value {
                carts.push((cart, path));
            }
        }
        carts
    }

    pub(crate) fn known_equal_to_set_builders(
        &self,
        object: &Obj,
    ) -> Vec<(SetBuilder, Vec<(Obj, Obj, FactId)>)> {
        let mut builders = Vec::new();
        for (value, path) in
            self.known_direct_equal_object_values(object, Some(&[EqualToObjShape::SetBuilder]))
        {
            if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = value {
                builders.push((builder, path));
            }
        }
        builders
    }

    fn known_direct_equal_object_values(
        &self,
        object: &Obj,
        shapes: Option<&[EqualToObjShape]>,
    ) -> Vec<(Obj, Vec<(Obj, Obj, FactId)>)> {
        let key = object.ir();
        let mut seen = HashSet::from([key.clone()]);
        let mut values = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(properties) = env.special_properties.get(&key) else {
                continue;
            };
            let index = &properties.equalities;
            let positions = match shapes {
                Some(shapes) => index.indices_for_shapes(shapes),
                None => (0..index.ordered.len()).collect(),
            };
            for position in positions {
                let endpoint = index.ordered[position];
                let Some(Fact::AtomicFact(AtomicFact::EqualFact(fact))) =
                    env.facts.facts_by_id.get(&endpoint.fact_id)
                else {
                    continue;
                };
                let subject = match endpoint.value_side {
                    crate::exec_env::EqualitySide::Left => &fact.right,
                    crate::exec_env::EqualitySide::Right => &fact.left,
                };
                if subject.ir() != key {
                    continue;
                }
                let value = endpoint.value(fact);
                if shapes.is_some_and(|shapes| !shapes.contains(&EqualToObjShape::of(&value)))
                    || !seen.insert(value.ir())
                {
                    continue;
                }
                let path = vec![(object.clone(), value.clone(), endpoint.fact_id)];
                values.push((value, path));
            }
        }
        values
    }

    pub(crate) fn known_memberships_of(&self, object: &Obj) -> Vec<InFact> {
        let key = object.ir();
        let mut memberships = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(properties) = env.special_properties.get(&key) {
                memberships.extend(properties.memberships.iter().cloned());
            }
        }
        memberships
    }

    pub(crate) fn known_function_signature_properties_of(
        &self,
        object: &Obj,
    ) -> Vec<crate::exec_env::SpecialProperty> {
        let key = object.ir();
        let mut properties = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(rows) = env.special_properties.get(&key) {
                properties.extend(rows.function_signature_properties(&env.facts));
            }
        }
        properties
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
// Candidate construction uses the unit law only. Child certificates still
// own both operands' WD; zero products never erase domain obligations here.
pub(crate) fn multiply_derivative_terms(
    left: crate::ast::obj::Obj,
    right: crate::ast::obj::Obj,
) -> crate::ast::obj::Obj {
    use crate::ast::obj::{Literal, Obj};
    if matches!(&left, Obj::Literal(Literal::Number(n)) if n.normalized_value=="1") {
        return right;
    }
    if matches!(&right, Obj::Literal(Literal::Number(n)) if n.normalized_value=="1") {
        return left;
    }
    crate::rational_expression::helper::mul_objs(left, right)
}
