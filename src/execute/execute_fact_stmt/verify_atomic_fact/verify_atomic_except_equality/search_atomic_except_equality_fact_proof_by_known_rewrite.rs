use crate::exec_env::exec_env::PropRewriteProperty;
use crate::prelude::*;

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
    Transitivity(AtomicExceptEqualityFactSearchProofByKnownTransitivity),
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

pub struct AtomicExceptEqualityFactSearchProofByKnownTransitivity {
    pub cite_prop: AtomicName,
    pub application: super::search_transitive_relation::TransitiveRelationProof,
}

impl Runtime {
    // Registered properties share the existing single-rewrite permission.
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
        if let AtomicFact::NormalAtomicFact(normal) = fact {
            if normal.body.len() == 2
                && self.prop_has_rewrite_property(&normal.predicate, |property| {
                    matches!(property, PropRewriteProperty::Transitive)
                })
            {
                if let Some(application) = self.search_transitive_relation(fact, verify_state)? {
                    return Ok(Some(
                        AtomicExceptEqualityFactSearchProofByKnownRewrite::Transitivity(
                            AtomicExceptEqualityFactSearchProofByKnownTransitivity {
                                cite_prop: normal.predicate.clone(),
                                application,
                            },
                        ),
                    ));
                }
            }
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
        Ok(Some(
            AtomicExceptEqualityFactSearchProofByKnownReflexivity {
                cite_prop: normal.predicate.clone(),
            },
        ))
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
            let Some(alternate_atomic) = reorder_normal_atomic_by_gather(
                normal,
                &gather,
                self.global_ids.allocate_fact_id(),
            ) else {
                continue;
            };
            let residual_state = verify_state.without_rewrite();
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
        self.visible_prop_rewrite_properties(prop).iter().any(pred)
    }

    fn symmetric_gathers_for_prop(&self, prop: &AtomicName) -> Vec<Vec<usize>> {
        let mut out = Vec::new();
        for p in self.visible_prop_rewrite_properties(prop) {
            if let PropRewriteProperty::SymmetricArgumentPermutate(gathers) = p {
                out.extend(gathers);
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
    // Registration records conclusion[k] = premise[gather[k]]. Recover the
    // premise from a requested conclusion with the inverse permutation.
    let mut new_body = fact.body.clone();
    for (k, &i) in gather.iter().enumerate() {
        new_body[i] = fact.body[k].clone();
    }
    Some(AtomicFact::NormalAtomicFact(NormalAtomicFact {
        fact_id,
        predicate: fact.predicate.clone(),
        body: new_body,
        line_file: fact.line_file.clone(),
    }))
}

#[cfg(test)]
mod round2_tests {
    use super::*;

    #[test]
    fn round2_cyclic_symmetry_recovers_the_forward_premise() {
        let fact = NormalAtomicFact {
            fact_id: FactId::new(1),
            predicate: AtomicName::plain("cycle".into()),
            body: [2, 3, 1]
                .into_iter()
                .map(|n| Obj::Literal(Literal::Number(Number::new(n.to_string()))))
                .collect(),
            line_file: None,
        };
        let AtomicFact::NormalAtomicFact(recovered) =
            reorder_normal_atomic_by_gather(&fact, &[1, 2, 0], FactId::new(2)).unwrap()
        else {
            panic!("normal predicate");
        };
        assert_eq!(
            recovered
                .body
                .iter()
                .map(|x| x.readable_string())
                .collect::<Vec<_>>(),
            ["1", "2", "3"]
        );
        assert!(reorder_normal_atomic_by_gather(&fact, &[0, 0, 2], FactId::new(3)).is_none());
        assert!(reorder_normal_atomic_by_gather(&fact, &[0, 1, 3], FactId::new(3)).is_none());
    }
}
