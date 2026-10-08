//! Derive finite function contracts from checked values and memberships.
//! No Cartesian-set identity is assigned a construction dimension.

use super::known_tuple::{tuple_function_head, KnownTupleShapeProof};
use super::VerifyState;
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::ast::obj::*;
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::runtime::{Runtime, RuntimeResult};

pub struct FiniteFunctionSignatureProof {
    pub signature: FnSet,
    pub source: KnownTupleShapeProof,
}

/// Build coordinate `index + 1` of a checked finite-function member.
/// Literal coordinates reduce directly; other supported values use ordinary
/// application syntax. The caller supplies the exact-domain membership.
pub(crate) fn finite_function_coordinate(function: &Obj, index: usize) -> Result<Obj, String> {
    if let Obj::ProductShape(ProductShape::Tuple(tuple)) = function {
        return tuple
            .args
            .get(index)
            .map(|value| value.as_ref().clone())
            .ok_or_else(|| "coordinate is outside the tuple's complete domain".into());
    }
    let argument = Obj::Literal(Literal::Number(Number {
        normalized_value: (index + 1).to_string(),
    }));
    super::function_domain::function_application(function, vec![Box::new(argument)])
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/finite_function_coordinates/tests.rs"]
mod finite_function_coordinate_tests;

impl Runtime {
    pub(crate) fn finite_function_signatures(
        &mut self,
        function: &Obj,
    ) -> Vec<FiniteFunctionSignatureProof> {
        let mut sources: Vec<_> = self
            .known_literal_tuple_candidates(function)
            .into_iter()
            .map(KnownTupleShapeProof::TupleEquality)
            .collect();
        if let Some(source) = self.lookup_known_tuple_shape(function) {
            if source.cart().is_some() {
                sources.push(source);
            }
        }
        let mut proofs = Vec::new();
        for source in sources {
            let carriers = match &source {
                KnownTupleShapeProof::TupleEquality(value) => value
                    .value
                    .args
                    .iter()
                    .map(|value| {
                        Obj::SetFormer(SetFormer::ListSet(ListSet {
                            list: vec![value.clone()],
                        }))
                    })
                    .collect(),
                _ => source
                    .cart()
                    .unwrap()
                    .args
                    .iter()
                    .map(|set| set.as_ref().clone())
                    .collect(),
            };
            let signature = self.finite_function_signature(source.dimension(), carriers);
            proofs.push(FiniteFunctionSignatureProof { signature, source });
        }
        proofs
    }

    pub(crate) fn cart_function_signature(&mut self, cart: &Cart) -> FnSet {
        self.finite_function_signature(
            cart.args.len(),
            cart.args.iter().map(|set| set.as_ref().clone()).collect(),
        )
    }

    /// Complete Cartesian definition: exact I_n carrier and every factor.
    /// The empty product is the space of empty graphs, not the empty set.
    pub(crate) fn cart_function_set_definition(&mut self, cart: &Cart) -> Obj {
        let signature = self.cart_function_signature(cart);
        let carrier = Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
            set: signature.ret_set,
            n: Box::new(Obj::Literal(Literal::Number(Number {
                normalized_value: cart.args.len().to_string(),
            }))),
        }));
        if cart.args.is_empty() {
            return carrier;
        }
        let binding = self.fresh_internal_param();
        let function = Obj::Identifier(IdentifierObj::from_bound_name(&binding));
        let mut facts = Vec::new();
        for (index, factor) in cart.args.iter().enumerate() {
            let coordinate = finite_function_coordinate(&function, index)
                .expect("a fresh bound identifier supports application");
            let fact: AtomicFact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: coordinate,
                set: factor.as_ref().clone(),
                line_file: None,
            }
            .into();
            facts.push(crate::ast::fact::QuantifierFreeFact::AtomicFact(fact));
        }
        Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: binding,
            param_set: Box::new(carrier),
            facts,
        }))
    }

    /// Select an I_n comparison domain from checked values. Return R here
    /// is only a neutral placeholder: this stage proves domains, not R-valued
    /// membership. Both peers must subsequently prove their complete domain.
    pub(crate) fn tuple_equality_domain(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Result<FnSet, String>> {
        let subjects = if !self.known_literal_tuple_candidates(left).is_empty() {
            vec![left]
        } else if !self.known_literal_tuple_candidates(right).is_empty() {
            vec![right]
        } else {
            vec![left, right]
        };
        for subject in subjects {
            for source in self.complete_function_domains(subject, VerifyState::top_level())? {
                let mut signature = source.signature;
                if signature.set_bound_parameters.groups.len() != 1 {
                    continue;
                }
                let group = &signature.set_bound_parameters.groups[0];
                if group.params.len() != 1 {
                    continue;
                }
                let Obj::SetFormer(SetFormer::ClosedRange(range)) = group.param_type.as_ref()
                else {
                    continue;
                };
                let Obj::Literal(Literal::Number(start)) = range.start.as_ref() else {
                    continue;
                };
                if start.normalized_value != "1" {
                    continue;
                }
                signature.dom_facts.clear();
                signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
                return Ok(Ok(signature));
            }
        }
        Ok(Err(
            "tuple equality needs a checked complete one-based finite domain".into(),
        ))
    }

    pub(crate) fn tuple_coordinate_equality_requirements(
        &mut self,
        left: &Obj,
        right: &Obj,
        domain: &FnSet,
    ) -> Result<Vec<Fact>, String> {
        if let (
            Obj::ProductShape(ProductShape::Tuple(a)),
            Obj::ProductShape(ProductShape::Tuple(b)),
        ) = (left, right)
        {
            if a.args.len() != b.args.len() {
                // No truncated coordinate list: the mandatory domain stage
                // rejects this pair before any equality can be published.
                return Ok(vec![]);
            }
        }
        let literal = self
            .known_literal_tuple_candidates(left)
            .into_iter()
            .next()
            .or_else(|| {
                self.known_literal_tuple_candidates(right)
                    .into_iter()
                    .next()
            });
        if let Some(literal) = literal {
            let mut requirements = Vec::new();
            // Every position is checked. Exact matching of BOTH complete
            // domains happens before these premises can publish equality.
            for index in 0..literal.value.args.len() {
                requirements.push(
                    EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: finite_function_coordinate(left, index)?,
                        right: finite_function_coordinate(right, index)?,
                        line_file: None,
                    }
                    .into(),
                );
            }
            return Ok(requirements);
        }
        let parameter = self.fresh_internal_param();
        let argument = Obj::Identifier(IdentifierObj::from_bound_name(&parameter));
        let equality: AtomicFact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: super::function_domain::function_application(
                left,
                vec![Box::new(argument.clone())],
            )?,
            right: super::function_domain::function_application(right, vec![Box::new(argument)])?,
            line_file: None,
        }
        .into();
        Ok(vec![Fact::ForallFact(crate::ast::fact::ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: crate::ast::param::TypedParameterList {
                groups: vec![crate::ast::param::TypedParameterGroup {
                    params: vec![parameter],
                    param_type: crate::ast::param::ParamType::Obj(
                        domain.set_bound_parameters.groups[0]
                            .param_type
                            .as_ref()
                            .clone(),
                    ),
                }],
            },
            dom_facts: vec![],
            then_facts: vec![crate::ast::fact::ExistOrAndChainAtomicFact::AtomicFact(
                equality,
            )],
            line_file: None,
        })])
    }

    pub(crate) fn cart_definition_for_set(&self, set: &Obj) -> Option<Cart> {
        self.exact_property_object_values(set)
            .into_iter()
            .find_map(|(value, _)| match value {
                Obj::ProductShape(ProductShape::Cart(cart)) => Some(cart),
                _ => None,
            })
    }

    pub(crate) fn cart_coordinate_membership_requirements(
        &mut self,
        function: &Obj,
        set: &Obj,
    ) -> Result<Vec<Fact>, String> {
        let Some(cart) = self.cart_definition_for_set(set) else {
            return Err("second argument must have a checked cart(...) definition".into());
        };
        let literal = Obj::ProductShape(ProductShape::Cart(cart.clone()));
        let mut requirements = vec![AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: set.clone(),
            right: literal,
            line_file: None,
        })
        .into()];
        if let Some(value) = self
            .known_literal_tuple_candidates(function)
            .into_iter()
            .next()
        {
            // Complete-domain matching precedes these obligations, including
            // the actual coordinate count. A truncated zip cannot certify it.
            for (element, carrier) in value.value.args.into_iter().zip(cart.args) {
                requirements.push(
                    AtomicFact::InFact(InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: *element,
                        set: *carrier,
                        line_file: None,
                    })
                    .into(),
                );
            }
        } else {
            for (index, carrier) in cart.args.into_iter().enumerate() {
                let argument = Obj::Literal(Literal::Number(Number {
                    normalized_value: (index + 1).to_string(),
                }));
                let element = super::function_domain::function_application(
                    function,
                    vec![Box::new(argument)],
                )?;
                requirements.push(
                    AtomicFact::InFact(InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element,
                        set: *carrier,
                        line_file: None,
                    })
                    .into(),
                );
            }
        }
        Ok(requirements)
    }

    fn finite_function_signature(&mut self, length: usize, carriers: Vec<Obj>) -> FnSet {
        // A union of singleton values permits repeated or not-yet-comparable
        // coordinates. A displayed set of all values would require distinctness.
        let mut carriers = carriers.into_iter();
        let mut ret_set = carriers
            .next()
            .unwrap_or_else(|| Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })));
        for carrier in carriers {
            ret_set = Obj::SetOperator(SetOperator::Union(Union {
                left: Box::new(ret_set),
                right: Box::new(carrier),
            }));
        }
        let domain = Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
            start: Box::new(Obj::Literal(Literal::Number(Number {
                normalized_value: "1".into(),
            }))),
            end: Box::new(Obj::Literal(Literal::Number(Number {
                normalized_value: length.to_string(),
            }))),
        }));
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![self.fresh_internal_param()],
                    param_type: Box::new(domain),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(ret_set),
        }
    }

    pub(crate) fn finite_function_application_receiver(&self, call: &FnObj) -> Option<Obj> {
        if call.body.last()?.len() != 1 {
            return None;
        }
        if call.body.len() == 1 {
            return Some(tuple_function_head(call));
        }
        let mut receiver = call.clone();
        receiver.body.pop();
        Some(Obj::FnObj(receiver))
    }
}
