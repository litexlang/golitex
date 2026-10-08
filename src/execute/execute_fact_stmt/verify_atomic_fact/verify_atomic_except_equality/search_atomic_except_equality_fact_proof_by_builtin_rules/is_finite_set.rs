use crate::ast::fact::{AtomicFact, Fact, InFact, IsFiniteSetFact};
use crate::ast::obj::{FunctionSpace, Literal, Number, Obj, SetFormer};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};

// These constructors carry finiteness intrinsically.
// Example: prove `$is_finite_set({1, 2})`, `$is_finite_set(closed_range(1, n))`.
pub enum IsFiniteSetFactSearchProofByBuiltinRule {
    FiniteIndexUnion(super::finite_index_union::FiniteIndexUnionProof),
    SurjectiveImageOfFiniteSet(SurjectiveImageOfFiniteSetBuiltinRuleProof),
    FunctionRangeOfFiniteDomain(FunctionRangeOfFiniteDomainProof),
    ListSet(ListSetFiniteBuiltinRuleProof),
    ClosedRange(ClosedRangeFiniteBuiltinRuleProof),
    Range(RangeFiniteBuiltinRuleProof),
    // Length-zero finite sequence carrier is always finite (one empty sequence).
    // Example: `$is_finite_set(finite_seq(R, 0))`.
    FiniteSeqZeroLength(FiniteSeqZeroLengthFiniteBuiltinRuleProof),
    // Finite codomain ⇒ finite length-n sequence carrier.
    // Example: `$is_finite_set({1})` proves `$is_finite_set(finite_seq({1}, 3))`.
    FiniteSeqFromFiniteCodomain(FiniteSeqFromFiniteCodomainBuiltinRuleProof),
}

pub struct SurjectiveImageOfFiniteSetBuiltinRuleProof {
    pub cite_surjective_fact_id: FactId,
    pub domain_finite_proof: VerifyFactResult,
}
pub struct FunctionRangeOfFiniteDomainProof {
    pub function_membership: VerifyFactResult,
    pub domain_finite: VerifyFactResult,
}

pub struct ListSetFiniteBuiltinRuleProof {}

pub struct ClosedRangeFiniteBuiltinRuleProof {}

pub struct RangeFiniteBuiltinRuleProof {}

pub struct FiniteSeqZeroLengthFiniteBuiltinRuleProof {}

pub struct FiniteSeqFromFiniteCodomainBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    // Builtin: list sets and integer ranges are finite by construction.
    // Example: prove `$is_finite_set({1, 2})`, `$is_finite_set(1...n)`.
    pub fn search_is_finite_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &IsFiniteSetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsFiniteSetFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.search_finite_index_union(fact, verify_state)? {
            return Ok(Some(proof));
        }
        let mut candidates = Vec::new();
        let key = (
            crate::ast::names::AtomicName::Plain {
                name: crate::parse::keywords::SURJECTIVE.into(),
            },
            true,
        );
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for known in knowns {
                    if let AtomicFact::SurjectiveFact(s) = known {
                        if s.codomain.ir() == fact.set.ir() {
                            candidates.push((s.fact_id, s.domain.clone()));
                        }
                    }
                }
            }
        }
        for (cite_surjective_fact_id, domain) in candidates {
            let premise = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                set: domain,
                line_file: None,
            }));
            let domain_finite_proof =
                self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if !domain_finite_proof.is_failed() {
                return Ok(Some(
                    IsFiniteSetFactSearchProofByBuiltinRule::SurjectiveImageOfFiniteSet(
                        SurjectiveImageOfFiniteSetBuiltinRuleProof {
                            cite_surjective_fact_id,
                            domain_finite_proof,
                        },
                    ),
                ));
            }
        }
        match &fact.set {
            Obj::FunctionSpace(FunctionSpace::FnRange(range)) => {
                let Some(signature) = self.resolve_callable_fn_set(&range.function) else {
                    return Ok(None);
                };
                if signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>()
                    != 1
                {
                    return Ok(None);
                }
                let Some(group) = signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .find(|g| !g.params.is_empty())
                else {
                    return Ok(None);
                };
                let finite = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: *group.param_type.clone(),
                    line_file: None,
                }));
                let domain_finite =
                    self.verify_builtin_rule_premise(&finite, verify_state.clone())?;
                if domain_finite.is_failed() {
                    return Ok(None);
                }
                let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: *range.function.clone(),
                    set: Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
                    line_file: None,
                }));
                let function_membership =
                    self.verify_builtin_rule_premise(&membership, verify_state)?;
                if function_membership.is_failed() {
                    return Ok(None);
                }
                Ok(Some(
                    IsFiniteSetFactSearchProofByBuiltinRule::FunctionRangeOfFiniteDomain(
                        FunctionRangeOfFiniteDomainProof {
                            function_membership,
                            domain_finite,
                        },
                    ),
                ))
            }
            Obj::SetFormer(SetFormer::ListSet(_)) => Ok(Some(
                IsFiniteSetFactSearchProofByBuiltinRule::ListSet(ListSetFiniteBuiltinRuleProof {}),
            )),
            Obj::SetFormer(SetFormer::ClosedRange(_)) => {
                Ok(Some(IsFiniteSetFactSearchProofByBuiltinRule::ClosedRange(
                    ClosedRangeFiniteBuiltinRuleProof {},
                )))
            }
            Obj::SetFormer(SetFormer::Range(_)) => Ok(Some(
                IsFiniteSetFactSearchProofByBuiltinRule::Range(RangeFiniteBuiltinRuleProof {}),
            )),
            Obj::SetFormer(SetFormer::FiniteSeqSet(seq)) => {
                if is_zero_obj(seq.n.as_ref()) {
                    return Ok(Some(
                        IsFiniteSetFactSearchProofByBuiltinRule::FiniteSeqZeroLength(
                            FiniteSeqZeroLengthFiniteBuiltinRuleProof {},
                        ),
                    ));
                }
                let premise = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: seq.set.as_ref().clone(),
                    line_file: None,
                }));
                let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
                if proof.is_failed() {
                    return Ok(None);
                }
                Ok(Some(
                    IsFiniteSetFactSearchProofByBuiltinRule::FiniteSeqFromFiniteCodomain(
                        FiniteSeqFromFiniteCodomainBuiltinRuleProof {
                            proof_of_requirement_facts: vec![proof],
                        },
                    ),
                ))
            }
            _ => Ok(None),
        }
    }
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}
