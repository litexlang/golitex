use crate::ast::fact::{AtomicFact, Fact, NormalAtomicFact};
use crate::ast::names::AtomicName;
use crate::exec_env::exec_env::PropRewriteProperty;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Known / registered rewrite for atomic-except-equality facts.
//
// Distinct from opaque resolve_obj: cites a registered prop rewrite property
// (by AtomicName) instead of silently rewriting objects in Runtime.
//
// Examples:
// - Reflexivity: prove `$same(a, a)` from a registered reflexive property.
// - Symmetry: prove `$same(b, a)` from alternate `$same(a, b)` via registered symmetry.
pub enum AtomicExceptEqualityFactSearchProofByKnownRewrite {
    Reflexivity(AtomicExceptEqualityFactSearchProofByKnownReflexivity),
    Symmetry(AtomicExceptEqualityFactSearchProofByKnownSymmetry),
}

pub struct AtomicExceptEqualityFactSearchProofByKnownReflexivity {
    pub cite_prop: AtomicName,
}

pub struct AtomicExceptEqualityFactSearchProofByKnownSymmetry {
    pub cite_prop: AtomicName,
    pub argument_permutation: Vec<usize>,
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    // Search registered Reflexivity then Symmetry (gated by can_use_rewrite).
    pub fn search_atomic_except_equality_fact_proof_by_known_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownRewrite>> {
        if let Some(proof) = self.search_known_reflexivity_rewrite(fact)? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByKnownRewrite::Reflexivity(proof),
            ));
        }
        if let Some(proof) = self.search_known_symmetry_rewrite(fact, verify_state)? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByKnownRewrite::Symmetry(proof),
            ));
        }
        Ok(None)
    }

    fn search_known_reflexivity_rewrite(
        &self,
        fact: &AtomicFact,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownReflexivity>> {
        let AtomicFact::NormalAtomicFact(normal) = fact else {
            return Ok(None);
        };
        if normal.body.len() != 2 {
            return Ok(None);
        }
        if normal.body[0].ir() != normal.body[1].ir() {
            return Ok(None);
        }
        if !self.prop_has_rewrite_property(&normal.predicate, |p| {
            matches!(p, PropRewriteProperty::Reflexive)
        }) {
            return Ok(None);
        }
        Ok(Some(AtomicExceptEqualityFactSearchProofByKnownReflexivity {
            cite_prop: normal.predicate.clone(),
        }))
    }

    fn search_known_symmetry_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownSymmetry>> {
        let AtomicFact::NormalAtomicFact(normal) = fact else {
            return Ok(None);
        };
        let gathers = self.symmetric_gathers_for_prop(&normal.predicate);
        for gather in gathers {
            let Some(alternate_atomic) =
                reorder_normal_atomic_by_gather(normal, &gather, self.global_ids.allocate_fact_id())
            else {
                continue;
            };
            let residual_state = VerifyState {
            can_use_builtin_rule_round: verify_state.can_use_builtin_rule_round,
                can_use_def_and_known_forall_and_known_strategy: verify_state.can_use_def_and_known_forall_and_known_strategy,
                can_use_rewrite: false,
                store_well_defined_fact: false,
                equality_class_search: verify_state.equality_class_search,
};
            let proof_of_alternate_fact =
                self.verify_atomic_fact(&alternate_atomic, residual_state)?;
            if proof_of_alternate_fact.is_failed() {
                continue;
            }
            return Ok(Some(AtomicExceptEqualityFactSearchProofByKnownSymmetry {
                cite_prop: normal.predicate.clone(),
                argument_permutation: gather,
                alternate_fact: alternate_atomic.into(),
                proof_of_alternate_fact,
            }));
        }
        Ok(None)
    }

    fn prop_has_rewrite_property(
        &self,
        prop: &AtomicName,
        pred: impl Fn(&PropRewriteProperty) -> bool,
    ) -> bool {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(props) = env.prop_rewrite_properties.get(prop) {
                if props.iter().any(&pred) {
                    return true;
                }
            }
        }
        false
    }

    fn symmetric_gathers_for_prop(&self, prop: &AtomicName) -> Vec<Vec<usize>> {
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(props) = env.prop_rewrite_properties.get(prop) {
                for p in props {
                    if let PropRewriteProperty::SymmetricArgumentPermutate(gathers) = p {
                        out.extend(gathers.iter().cloned());
                    }
                }
            }
        }
        out
    }
}

fn reorder_normal_atomic_by_gather(
    fact: &NormalAtomicFact,
    gather: &[usize],
    fact_id: crate::runtime::runtime_ids::FactId,
) -> Option<AtomicFact> {
    let n = fact.body.len();
    if gather.len() != n || n < 2 {
        return None;
    }
    let mut seen = vec![false; n];
    for &i in gather {
        if i >= n || seen[i] {
            return None;
        }
        seen[i] = true;
    }
    let new_body: Vec<_> = gather.iter().map(|&i| fact.body[i].clone()).collect();
    Some(AtomicFact::NormalAtomicFact(NormalAtomicFact {
        fact_id,
        predicate: fact.predicate.clone(),
        body: new_body,
        line_file: fact.line_file.clone(),
    }))
}
