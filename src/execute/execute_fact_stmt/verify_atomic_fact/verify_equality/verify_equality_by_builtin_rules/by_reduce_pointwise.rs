//! A stored pointwise proposition is a certificate for ordered-fold congruence.
use super::reduce_rule_helper::{reduce_application, ReduceObjectMatchProof};
use crate::ast::fact::{EqualFact, Fact, ForallFact, LessEqualFact};
use crate::ast::obj::{IdentifierObj, IteratedOperator, Obj, StandardSet};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_fact_stmt::verify_forall_fact::ForallParameterRenaming;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};

pub struct ReducePointwiseProof {
    pub matches: Vec<ReduceObjectMatchProof>,
    pub certificate: ReducePointwiseCertificate,
}
// The stored source has already passed its own binder/domain WD. Exact whole
// proposition matching transports that certificate, without re-searching it.
pub struct ReducePointwiseCertificate {
    pub fact: ForallFact,
    pub cite_fact_id: FactId,
    pub parameter_renamings: Vec<ForallParameterRenaming>,
}
impl Runtime {
    pub(super) fn search_reduce_pointwise(
        &mut self,
        fact: &EqualFact,
        _state: VerifyState,
    ) -> RuntimeResult<Option<ReducePointwiseProof>> {
        // Same interval, seed and operation plus a stored forall k: f(k)=g(k).
        // Reuse the entire stored proposition by the existing exact source
        // matcher. This does not instantiate a general forall search route.
        let (
            Obj::IteratedOperator(IteratedOperator::Reduce(left)),
            Obj::IteratedOperator(IteratedOperator::Reduce(right)),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        let mut matches = Vec::new();
        for (a, b) in [
            (&*left.start, &*right.start),
            (&*left.end, &*right.end),
            (&*left.op, &*right.op),
            (&*left.seed, &*right.seed),
        ] {
            let Some(proof) = self.match_reduce_object(a, b) else {
                return Ok(None);
            };
            matches.push(proof);
        }
        let parameter = self.fresh_internal_param();
        let index = Obj::Identifier(IdentifierObj::from_bound_name(&parameter));
        let Some(a) = reduce_application(&left.func, vec![index.clone()]) else {
            return Ok(None);
        };
        let Some(b) = reduce_application(&right.func, vec![index.clone()]) else {
            return Ok(None);
        };
        for reverse in [false, true] {
            for bounded in [false, true] {
                let dom_facts: Vec<Fact> = if bounded {
                    vec![
                        LessEqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: *left.start.clone(),
                            right: index.clone(),
                            line_file: fact.line_file.clone(),
                        }
                        .into(),
                        LessEqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: index.clone(),
                            right: *left.end.clone(),
                            line_file: fact.line_file.clone(),
                        }
                        .into(),
                    ]
                } else {
                    vec![]
                };
                let then: crate::ast::fact::AtomicFact = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: if reverse { b.clone() } else { a.clone() },
                    right: if reverse { a.clone() } else { b.clone() },
                    line_file: fact.line_file.clone(),
                }
                .into();
                let goal = ForallFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters: TypedParameterList {
                        groups: vec![TypedParameterGroup {
                            params: vec![parameter.clone()],
                            param_type: ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
                        }],
                    },
                    dom_facts,
                    then_facts: vec![crate::ast::fact::ExistOrAndChainAtomicFact::AtomicFact(
                        then,
                    )],
                    line_file: fact.line_file.clone(),
                };
                if let Some((cite_fact_id, parameter_renamings)) =
                    self.match_known_forall_source(&goal)
                {
                    return Ok(Some(ReducePointwiseProof {
                        matches,
                        certificate: ReducePointwiseCertificate {
                            fact: goal,
                            cite_fact_id,
                            parameter_renamings,
                        },
                    }));
                }
            }
        }
        Ok(None)
    }
}
