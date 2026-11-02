//! One fixed, total, unital commutative-ring contract. The zero ring is allowed.
use crate::prelude::*;

pub struct BuiltinCommRingDefinitionProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub(crate) fn comm_ring_domain_requirements(&mut self, args: &[&Obj]) -> Vec<Fact> {
        let carrier = args[0];
        let mut requirements = vec![Fact::from(IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: carrier.clone(),
            line_file: None,
        })];
        for (operation, arity) in [(args[1], 2), (args[2], 2), (args[3], 1)] {
            let params = (0..arity).map(|_| self.fresh_internal_param()).collect();
            let signature = Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
                set_bound_parameters: SetBoundParameterList {
                    groups: vec![SetBoundParameterGroup {
                        params,
                        param_type: Box::new(carrier.clone()),
                    }],
                },
                dom_facts: vec![],
                ret_set: Box::new(carrier.clone()),
            }));
            requirements.push(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: operation.clone(),
                    set: signature,
                    line_file: None,
                }
                .into(),
            );
        }
        for element in &args[4..] {
            requirements.push(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: (*element).clone(),
                    set: carrier.clone(),
                    line_file: None,
                }
                .into(),
            );
        }
        requirements
    }

    pub(crate) fn comm_ring_definition_requirements(&mut self, ring: &CommRingFact) -> Vec<Fact> {
        let x = self.fresh_internal_param();
        let y = self.fresh_internal_param();
        let z = self.fresh_internal_param();
        let a = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let b = Obj::Identifier(IdentifierObj::from_bound_name(&y));
        let c = Obj::Identifier(IdentifierObj::from_bound_name(&z));
        let add = |a: Obj, b: Obj| ring_call(&ring.add, vec![a, b]);
        let mul = |a: Obj, b: Obj| ring_call(&ring.mul, vec![a, b]);
        let neg = |a: Obj| ring_call(&ring.neg, vec![a]);
        // Keep each law independently usable at its natural arity.
        let laws = vec![
            (
                vec![x.clone(), y.clone(), z.clone()],
                add(add(a.clone(), b.clone()), c.clone()),
                add(a.clone(), add(b.clone(), c.clone())),
            ),
            (
                vec![x.clone(), y.clone()],
                add(a.clone(), b.clone()),
                add(b.clone(), a.clone()),
            ),
            (
                vec![x.clone()],
                add(ring.zero.clone(), a.clone()),
                a.clone(),
            ),
            (
                vec![x.clone()],
                add(a.clone(), neg(a.clone())),
                ring.zero.clone(),
            ),
            (
                vec![x.clone(), y.clone(), z.clone()],
                mul(mul(a.clone(), b.clone()), c.clone()),
                mul(a.clone(), mul(b.clone(), c.clone())),
            ),
            (
                vec![x.clone(), y.clone()],
                mul(a.clone(), b.clone()),
                mul(b.clone(), a.clone()),
            ),
            (vec![x.clone()], mul(ring.one.clone(), a.clone()), a.clone()),
            (
                vec![x, y, z],
                mul(a.clone(), add(b.clone(), c.clone())),
                add(mul(a.clone(), b), mul(a, c)),
            ),
        ];
        laws.into_iter()
            .map(|(params, left, right)| {
                let equality = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left,
                    right,
                    line_file: None,
                };
                Fact::ForallFact(ForallFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters: TypedParameterList {
                        groups: vec![TypedParameterGroup {
                            params,
                            param_type: ParamType::Obj(ring.carrier.clone()),
                        }],
                    },
                    dom_facts: vec![],
                    then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(equality.into())],
                    line_file: None,
                })
            })
            .collect()
    }
}

pub(crate) fn ring_call(function: &Obj, arguments: Vec<Obj>) -> Obj {
    let arguments = arguments.into_iter().map(Box::new).collect();
    if let Obj::FnObj(prefix) = function {
        let mut body = prefix.body.clone();
        body.push(arguments);
        return Obj::FnObj(FnObj {
            head: prefix.head.clone(),
            body,
        });
    }
    let head = match function {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(f.clone()))
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(f)) => {
            FnObjHead::FieldAccess(f.clone())
        }
        Obj::InstantiatedTemplateObj(t) => FnObjHead::InstantiatedTemplateObj(t.clone()),
        _ => FnObjHead::Object(Box::new(function.clone())),
    };
    Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![arguments],
    })
}
