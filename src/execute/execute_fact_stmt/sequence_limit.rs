//! Real sequence limits: epsilon-tail semantics and proof-driven selection.
use crate::ast::names::{AtomicName, BoundName};
use crate::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup,
    TypedParameterList,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    LimitOperatorObjWellDefinedProofByDef, SequenceLimitObjWellDefinedProof,
};
use crate::prelude::*;
use crate::rational_expression::helper::sub_objs;

impl Runtime {
    // Consume only already proved candidates or existence. Never analyze the body.
    pub(crate) fn verify_sequence_limit_well_definedness(
        &mut self,
        value: &SequenceLimit,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let obj: Obj = value.clone().into();
        let sequence_wd = match self.verify_obj_well_definedness(&value.sequence, state.clone())? {
            VerifyObjWellDefinedResult::Success(p) => p,
            VerifyObjWellDefinedResult::Failed { reason, .. } => {
                return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
            }
        };
        let sequence_domain =
            if let Some(source) = self.checked_real_sequence_domain(&value.sequence, state)? {
                RealSequenceDomainProof::CompleteSignature(Box::new(source))
            } else {
                let membership_fact = sequence_membership(self, *value.sequence.clone());
                let membership = self.verify_fact(&membership_fact, state)?;
                if membership.is_failed() {
                    return Ok(limit_wd_failure(obj, membership));
                }
                RealSequenceDomainProof::Membership(Box::new(membership))
            };
        let mut convergence = None;
        for candidate in self.known_sequence_limit_candidates() {
            let fact = self.sequence_limit_candidate(*value.sequence.clone(), candidate.value);
            if let Some(proof) = self.lookup_known_atomic_premise(fact.clone().into()) {
                convergence = Some(SequenceConvergenceProof::Candidate(proof));
                break;
            }
        }
        let convergence = match convergence {
            Some(p) => p,
            None => {
                let existence = self.sequence_limit_existence(*value.sequence.clone());
                let result = self.verify_fact(&existence, state)?;
                if result.is_failed() {
                    return Ok(limit_wd_failure(obj, result));
                }
                SequenceConvergenceProof::Existence {
                    fact: existence,
                    proof: Box::new(result),
                }
            }
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj,
                proof: ObjWellDefinedProofByDef::LimitOperator(
                    LimitOperatorObjWellDefinedProofByDef::Sequence(
                        SequenceLimitObjWellDefinedProof {
                            sequence_wd: Box::new(sequence_wd),
                            sequence_domain,
                            convergence,
                        },
                    ),
                ),
            },
        ))
    }

    // The enclosing atomic WD already checked this sequence object. Consume
    // its complete signature rather than rechecking a guarded body at a lower ceiling.
    pub(crate) fn checked_real_sequence_domain(
        &mut self,
        sequence: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<super::function_domain::CompleteFunctionDomainProof>> {
        let index = self.fresh_internal_param();
        let target = FnSet {
            set_bound_parameters: set_bound(index, pos_nat()),
            dom_facts: vec![],
            ret_set: Box::new(real()),
        };
        for source in self.complete_function_domains(sequence, state)? {
            if super::fn_sets_alpha_equal(&source.signature, &target) {
                return Ok(Some(source));
            }
        }
        Ok(None)
    }

    pub(crate) fn known_sequence_limit_candidates(&self) -> Vec<HasSequenceLimitFact> {
        let key = (
            AtomicName::Plain {
                name: "has_seq_limit".into(),
            },
            true,
        );
        let mut result = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for fact in facts {
                    if let AtomicFact::HasSequenceLimitFact(f) = fact {
                        result.push(f.clone());
                    }
                }
            }
        }
        result
    }

    pub(crate) fn sequence_limit_candidate(
        &mut self,
        sequence: Obj,
        value: Obj,
    ) -> HasSequenceLimitFact {
        HasSequenceLimitFact {
            fact_id: self.global_ids.allocate_fact_id(),
            sequence,
            value,
            line_file: None,
        }
    }

    pub(crate) fn sequence_limit_existence(&mut self, sequence: Obj) -> Fact {
        let l = self.fresh_internal_param();
        let candidate = self.sequence_limit_candidate(sequence, identifier(&l));
        Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed(l, real()),
            facts: vec![QuantifierFreeFact::AtomicFact(candidate.into())],
            line_file: None,
        })
    }

    // forall epsilon>0, exists N>0: the N-tail lies in the preimage of the epsilon ball.
    // Tail inclusion keeps the existential body quantifier-free.
    pub(crate) fn sequence_limit_epsilon_fact(&mut self, sequence: Obj, value: Obj) -> Fact {
        let epsilon = self.fresh_internal_param();
        let n0 = self.fresh_internal_param();
        let tail =
            self.sequence_limit_tail_fact(sequence, value, identifier(&epsilon), identifier(&n0));
        let exists = PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed(n0, pos_nat()),
            facts: vec![QuantifierFreeFact::AtomicFact(tail.into())],
            line_file: None,
        };
        Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed(epsilon, Obj::StandardSet(StandardSet::RPos)),
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(exists)],
            line_file: None,
        })
    }

    pub(crate) fn sequence_limit_tail_fact(
        &mut self,
        sequence: Obj,
        value: Obj,
        epsilon: Obj,
        cutoff: Obj,
    ) -> SubsetFact {
        let n = self.fresh_internal_param();
        let guard: AtomicFact = GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: identifier(&n),
            right: cutoff,
            line_file: None,
        }
        .into();
        let tail = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: n,
            param_set: Box::new(pos_nat()),
            facts: vec![QuantifierFreeFact::AtomicFact(guard)],
        }));
        let y = self.fresh_internal_param();
        let distance = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
            arg: Box::new(sub_objs(identifier(&y), value)),
        }));
        let close: AtomicFact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: distance,
            right: epsilon,
            line_file: None,
        }
        .into();
        let ball = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: y,
            param_set: Box::new(real()),
            facts: vec![QuantifierFreeFact::AtomicFact(close)],
        }));
        let preimage: Obj = PreimageSet::new(sequence, ball).into();
        SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: tail,
            right: preimage,
            line_file: None,
        }
    }
}

pub enum RealSequenceDomainProof {
    CompleteSignature(Box<super::function_domain::CompleteFunctionDomainProof>),
    Membership(Box<VerifyFactResult>),
}

pub enum SequenceConvergenceProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Existence {
        fact: Fact,
        proof: Box<VerifyFactResult>,
    },
}

pub(super) fn limit_wd_failure(obj: Obj, result: VerifyFactResult) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj: obj.clone(),
        reason: FailToVerifyObjWellDefinedResult::LimitOperator(
            super::well_defined_results::verify_obj::FailToVerifyLimitOperatorObjWellDefinedResult::Sequence(
                super::well_defined_results::verify_obj::FailToVerifySequenceLimitObjWellDefined { obj, result: Box::new(result) }
            )
        ),
    }
}

pub(crate) fn sequence_membership(rt: &mut Runtime, sequence: Obj) -> Fact {
    let index = rt.fresh_internal_param();
    let signature = Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
        set_bound_parameters: set_bound(index, pos_nat()),
        dom_facts: vec![],
        ret_set: Box::new(real()),
    }));
    InFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        element: sequence,
        set: signature,
        line_file: None,
    }
    .into()
}
pub(super) fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn pos_nat() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
pub(super) fn identifier(p: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(p))
}
pub(super) fn typed(p: BoundName, set: Obj) -> TypedParameterList {
    TypedParameterList {
        groups: vec![TypedParameterGroup {
            params: vec![p],
            param_type: ParamType::Obj(set),
        }],
    }
}
fn set_bound(p: BoundName, set: Obj) -> SetBoundParameterList {
    SetBoundParameterList {
        groups: vec![SetBoundParameterGroup {
            params: vec![p],
            param_type: Box::new(set),
        }],
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/sequence_limit/tests.rs"]
mod sequence_limit_tests;
