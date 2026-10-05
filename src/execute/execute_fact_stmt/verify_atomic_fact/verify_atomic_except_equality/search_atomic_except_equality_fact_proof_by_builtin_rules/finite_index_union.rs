//! A finite union of finite fibres. Consume the exact stored fibre certificate.
use super::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule;
use crate::ast::fact::{ExistOrAndChainAtomicFact, Fact, ForallFact, IsFiniteSetFact};
use crate::ast::obj::{IdentifierObj, Obj, SetOperator};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::reduce_rule_helper::reduce_application;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_forall_fact::ForallParameterRenaming;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};

pub struct FiniteIndexUnionProof {
    pub index_finite: VerifyFactResult,
    pub fibres: FiniteFibresCertificate,
}
pub struct FiniteFibresCertificate {
    pub fact: ForallFact,
    pub cite_fact_id: FactId,
    pub parameter_renamings: Vec<ForallParameterRenaming>,
}

impl Runtime {
    pub(super) fn search_finite_index_union(
        &mut self,
        fact: &IsFiniteSetFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<IsFiniteSetFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::IndexUnion(union)) = &fact.set else {
            return Ok(None);
        };
        let parameter = self.fresh_internal_param();
        let index = Obj::Identifier(IdentifierObj::from_bound_name(&parameter));
        let Some(fibre) = reduce_application(&union.family_fn, vec![index]) else {
            return Ok(None);
        };
        let fibres_fact = ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![parameter],
                    param_type: ParamType::Obj(*union.index_set.clone()),
                }],
            },
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(
                IsFiniteSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: fibre,
                    line_file: fact.line_file.clone(),
                }
                .into(),
            )],
            line_file: fact.line_file.clone(),
        };
        let Some((cite_fact_id, parameter_renamings)) =
            self.match_known_forall_source(&fibres_fact)
        else {
            return Ok(None);
        };
        let index_fact: Fact = IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: *union.index_set.clone(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let index_finite = self.verify_builtin_rule_premise(&index_fact, state)?;
        if index_finite.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            IsFiniteSetFactSearchProofByBuiltinRule::FiniteIndexUnion(FiniteIndexUnionProof {
                index_finite,
                fibres: FiniteFibresCertificate {
                    fact: fibres_fact,
                    cite_fact_id,
                    parameter_renamings,
                },
            }),
        ))
    }
}
