//! Cartesian sets are ordinary sets of exact finite-domain functions.
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::runtime::Runtime;
use super::super::by_they_are_the_same::{search_equal_fact_proof_by_they_are_the_same, TheyAreTheSameProof};

pub struct CartesianDefinitionProof {
    pub expanded_definition: Obj,
    pub definition_match: TheyAreTheSameProof,
}

impl Runtime {
    // cart(A,B) = {p finite_seq(union(A,B),2): p(1) in A, p(2) in B}.
    // Parent equality WD already checks both sides. This pure alpha match
    // accepts only the COMPLETE generated definition, never coordinate images.
    pub(super) fn cartesian_definition(&mut self, cart: &crate::ast::obj::Cart, other: &Obj)
        -> Option<CartesianDefinitionProof> {
        let expanded_definition = self.cart_function_set_definition(cart);
        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(), left: expanded_definition.clone(),
            right: other.clone(), line_file: None,
        };
        let definition_match = search_equal_fact_proof_by_they_are_the_same(&residual)?;
        Some(CartesianDefinitionProof { expanded_definition, definition_match })
    }
}
