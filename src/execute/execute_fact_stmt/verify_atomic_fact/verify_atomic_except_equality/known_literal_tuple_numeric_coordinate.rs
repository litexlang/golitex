use crate::execute::execute_fact_stmt::known_tuple::{
    literal_positive_usize, KnownTupleValueProof,
};
use crate::prelude::*;

pub struct LiteralTupleNumericCoordinateKnownProof {
    pub index: usize,
    pub tuple: KnownTupleValueProof,
    pub component_membership: ClosedMembershipCalculationProof,
}

impl Runtime {
    // Read one literal numeric coordinate from a checked call. For example,
    // (0,0)(1) in C follows from the closed calculation 0 in C.
    // No verification/search callback: keep the tuple equality and calculation.
    // The enclosing fact WD has checked the entire tuple and actual index.
    pub(super) fn known_literal_tuple_numeric_coordinate(
        &mut self,
        fact: &InFact,
    ) -> Option<LiteralTupleNumericCoordinateKnownProof> {
        if !matches!(fact.set, Obj::StandardSet(_)) {
            return None;
        }
        let Obj::FnObj(call) = &fact.element else {
            return None;
        };
        let receiver = self.finite_function_application_receiver(call)?;
        let index = literal_positive_usize(&call.body.last()?[0])?;
        for tuple in self.known_literal_tuple_candidates(&receiver) {
            let Some(coordinate) = tuple.value.args.get(index - 1) else {
                continue;
            };
            let component = AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: coordinate.as_ref().clone(),
                set: fact.set.clone(),
                line_file: fact.line_file.clone(),
            });
            let Some(ClosedAtomicExceptEqualityCalculationProof::In(component_membership)) =
                calculate_closed_atomic_except_equality_fact(&component)
            else {
                continue;
            };
            return Some(LiteralTupleNumericCoordinateKnownProof {
                index,
                tuple,
                component_membership,
            });
        }
        None
    }
}

pub struct UniformTupleCoordinateCarrierProof {
    pub tuple:KnownTupleValueProof,
    pub index:Obj,
    pub carrier:StandardSet,
    pub coordinates:Vec<crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipProof>,
}
impl Runtime {
    // After application WD, an unknown valid index selects one of these exact
    // tuple entries. Pure structural carrier evidence for every entry suffices;
    // no new premise search or inference is opened inside a binder.
    pub(super) fn known_uniform_tuple_coordinate_carrier(
        &mut self,
        fact: &InFact,
    ) -> Option<UniformTupleCoordinateCarrierProof> {
        let Obj::StandardSet(carrier) = &fact.set else {
            return None;
        };
        let Obj::FnObj(call) = &fact.element else {
            return None;
        };
        let receiver = self.finite_function_application_receiver(call)?;
        for tuple in self.known_literal_tuple_candidates(&receiver) {
            if tuple.value.args.is_empty() {
                continue;
            }
            let mut coordinates = Vec::new();
            for entry in &tuple.value.args {
                let Some(proof) = self.search_structural_membership(entry, carrier) else {
                    coordinates.clear();
                    break;
                };
                coordinates.push(proof);
            }
            if coordinates.len() == tuple.value.args.len() {
                return Some(UniformTupleCoordinateCarrierProof {
                    tuple,
                    index: *call.body.last()?[0].clone(),
                    carrier: carrier.clone(),
                    coordinates,
                });
            }
        }
        None
    }
}
