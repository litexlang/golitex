use crate::new_pipeline::ast::fact::{AtomicFact, NotSupersetFact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::SUBSET;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `not A $superset B`.
pub enum NotSupersetFactSearchProofByBuiltinRule {
    // Duality: known `not B $subset A` proves `not A $superset B`.
    // Example: trust `not {1} $subset {2}`; prove `not {2} $superset {1}`.
    FromKnownNotSubset(FromKnownNotSubsetBuiltinRuleProof),
}

pub struct FromKnownNotSubsetBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    pub fn search_not_superset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotSupersetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSupersetFactSearchProofByBuiltinRule>> {
        if let Some(cite_fact_id) = self.known_not_subset_fact_id(&fact.right, &fact.left) {
            return Ok(Some(
                NotSupersetFactSearchProofByBuiltinRule::FromKnownNotSubset(
                    FromKnownNotSubsetBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }
        Ok(None)
    }

    pub(crate) fn known_not_subset_fact_id(
        &self,
        left: &crate::new_pipeline::ast::obj::Obj,
        right: &crate::new_pipeline::ast::obj::Obj,
    ) -> Option<FactId> {
        let key = (
            AtomicName::Plain {
                name: SUBSET.into(),
            },
            false,
        );
        let left_ir = left.ir();
        let right_ir = right.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env.facts.known_atomic_except_equality_facts.by_prop.get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::NotSubsetFact(f) = known {
                    if f.left.ir() == left_ir && f.right.ir() == right_ir {
                        return Some(f.fact_id);
                    }
                }
            }
        }
        None
    }
}
