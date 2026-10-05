//! Derive finite function contracts from checked values and memberships.
//! No Cartesian-set identity is assigned a construction dimension.

use super::known_tuple::{KnownTupleShapeProof, tuple_function_head};
use crate::ast::obj::*;
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use super::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::runtime::Runtime;

pub struct FiniteFunctionSignatureProof {
    pub signature: FnSet,
    pub source: KnownTupleShapeProof,
}

impl Runtime {
    pub(crate) fn finite_function_signatures(&mut self, function: &Obj) -> Vec<FiniteFunctionSignatureProof> {
        let mut sources: Vec<_> = self.known_literal_tuple_candidates(function).into_iter()
            .map(KnownTupleShapeProof::TupleEquality).collect();
        if let Some(source) = self.lookup_known_tuple_shape(function) {
            if source.cart().is_some() { sources.push(source); }
        }
        let mut proofs = Vec::new();
        for source in sources {
            let carriers = match &source {
                KnownTupleShapeProof::TupleEquality(value) => value.value.args.iter().map(|value| {
                    Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![value.clone()] }))
                }).collect(),
                _ => source.cart().unwrap().args.iter().map(|set| set.as_ref().clone()).collect(),
            };
            let signature = self.finite_function_signature(source.dimension(), carriers);
            proofs.push(FiniteFunctionSignatureProof { signature, source });
        }
        proofs
    }

    pub(crate) fn cart_function_signature(&mut self, cart: &Cart) -> FnSet {
        self.finite_function_signature(cart.args.len(), cart.args.iter().map(|set| set.as_ref().clone()).collect())
    }

    pub(crate) fn cart_definition_for_set(&self, set: &Obj) -> Option<Cart> {
        equivalence_class_members_with_paths_in_adjacency(&self.visible_equivalence_class_adjacency(), set)
            .into_iter().find_map(|(value, _)| match value {
                Obj::ProductShape(ProductShape::Cart(cart)) => Some(cart), _ => None,
            })
    }

    pub(crate) fn cart_coordinate_membership_requirements(&mut self, function: &Obj, set: &Obj) -> Result<Vec<Fact>, String> {
        let Some(cart) = self.cart_definition_for_set(set) else { return Err("second argument must have a checked cart(...) definition".into()); };
        let literal = Obj::ProductShape(ProductShape::Cart(cart.clone()));
        let mut requirements = vec![AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(), left: set.clone(), right: literal, line_file: None,
        }).into()];
        if let Some(value) = self.known_literal_tuple_candidates(function).into_iter().next() {
            // Complete-domain matching precedes these obligations, including
            // the actual coordinate count. A truncated zip cannot certify it.
            for (element, carrier) in value.value.args.into_iter().zip(cart.args) {
                requirements.push(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(), element: *element, set: *carrier, line_file: None,
                }).into());
            }
        } else {
            for (index, carrier) in cart.args.into_iter().enumerate() {
                let argument = Obj::Literal(Literal::Number(Number { normalized_value: (index + 1).to_string() }));
                let element = super::function_domain::function_application(function, vec![Box::new(argument)])?;
                requirements.push(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(), element, set: *carrier, line_file: None,
                }).into());
            }
        }
        Ok(requirements)
    }

    fn finite_function_signature(&mut self, length: usize, carriers: Vec<Obj>) -> FnSet {
        // A union of singleton values permits repeated or not-yet-comparable
        // coordinates. A displayed set of all values would require distinctness.
        let mut carriers = carriers.into_iter();
        let mut ret_set = carriers.next().unwrap_or_else(|| Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })));
        for carrier in carriers {
            ret_set = Obj::SetOperator(SetOperator::Union(Union { left: Box::new(ret_set), right: Box::new(carrier) }));
        }
        let domain = Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
            start: Box::new(Obj::Literal(Literal::Number(Number { normalized_value: "1".into() }))),
            end: Box::new(Obj::Literal(Literal::Number(Number { normalized_value: length.to_string() }))),
        }));
        FnSet {
            set_bound_parameters: SetBoundParameterList { groups: vec![SetBoundParameterGroup {
                params: vec![self.fresh_internal_param()], param_type: Box::new(domain),
            }] }, dom_facts: vec![], ret_set: Box::new(ret_set),
        }
    }

    pub(crate) fn finite_function_application_receiver(&self, call: &FnObj) -> Option<Obj> {
        if call.body.last()?.len() != 1 { return None; }
        if call.body.len() == 1 { return Some(tuple_function_head(call)); }
        let mut receiver = call.clone();
        receiver.body.pop();
        Some(Obj::FnObj(receiver))
    }
}
