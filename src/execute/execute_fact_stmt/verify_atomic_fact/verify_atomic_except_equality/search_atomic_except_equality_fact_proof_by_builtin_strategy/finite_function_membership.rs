//! A checked finite-function call selects one coordinate, or one of all of them.
use super::result::FiniteFunctionApplicationMembershipStrategySingleStep;
use crate::ast::fact::{AtomicFact, Fact, InFact, SubsetFact};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::{
    known_tuple::{literal_positive_usize, KnownTupleShapeProof},
    VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_finite_function_application_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FiniteFunctionApplicationMembershipStrategySingleStep>> {
        let AtomicFact::InFact(fact) = fact else {
            return Ok(None);
        };
        let Obj::FnObj(call) = &fact.element else {
            return Ok(None);
        };
        let Some(receiver) = self.finite_function_application_receiver(call) else {
            return Ok(None);
        };
        let last = call.body.len() - 1;
        let index = literal_positive_usize(&call.body[last][0]);
        for source in self.finite_function_signatures(&receiver) {
            // The enclosing fact WD checked this entire actual application.
            // A checked value/member source fixes its complete domain, so
            // replaying argument WD here would lower its original permissions.
            let mut requirements: Vec<Fact> = Vec::new();
            let positions: Vec<_> = match index {
                Some(index) if index <= source.source.dimension() => vec![index - 1],
                Some(_) => continue,
                None => (0..source.source.dimension()).collect(),
            };
            match &source.source {
                KnownTupleShapeProof::TupleEquality(value) => {
                    for position in positions {
                        requirements.push(
                            AtomicFact::InFact(InFact {
                                fact_id: self.global_ids.allocate_fact_id(),
                                element: value.value.args[position].as_ref().clone(),
                                set: fact.set.clone(),
                                line_file: fact.line_file.clone(),
                            })
                            .into(),
                        );
                    }
                }
                _ => {
                    let cart = source.source.cart().unwrap();
                    for position in positions {
                        requirements.push(
                            AtomicFact::SubsetFact(SubsetFact {
                                fact_id: self.global_ids.allocate_fact_id(),
                                left: cart.args[position].as_ref().clone(),
                                right: fact.set.clone(),
                                line_file: fact.line_file.clone(),
                            })
                            .into(),
                        );
                    }
                }
            }
            let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, ctx)?
            else {
                continue;
            };
            return Ok(Some(
                FiniteFunctionApplicationMembershipStrategySingleStep {
                    source,
                    index,
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            ));
        }
        Ok(None)
    }
}
