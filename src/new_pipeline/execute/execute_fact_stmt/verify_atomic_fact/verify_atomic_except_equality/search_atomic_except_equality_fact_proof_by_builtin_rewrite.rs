use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, FnEqualInFact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotFnEqualInFact, NotGreaterEqualFact, NotGreaterFact, NotLessEqualFact,
    NotLessFact, NotNormalAtomicFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::{PROPER_SUBSET, PROPER_SUPERSET};
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rewrite for atomic-except-equality facts.
//
// Part of replacing legacy opaque resolve_obj: order duals must appear as
// explicit Result certificates, not silent pre-normalization of objects.
//
// Mathematical property: binary order / proper-subset / fn_eq_in duality —
// `a > b` iff `b < a`, and likewise for weak/negated order, proper subset, and
// fn_eq_in argument swap.
//
// Example:
//   have a R, b R
//   trust a < b
//   b > a
// Search order places this after builtin/known/strategy/definition/forall, so
// closed numerics like `2 > 1` still win on ClosedNumericComparison first.
pub enum AtomicExceptEqualityFactSearchProofByBuiltinRewrite {
    // Rewrite a goal to an order-dual alternate fact, then prove the alternate.
    // Example: goal `b > a` via alternate `a < b`.
    OrderDual(AtomicExceptEqualityFactSearchProofByBuiltinOrderDual),
}

pub struct AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    // Builtin rewrite: prove goal by proving its order dual (rewrite off).
    // Example: see AtomicExceptEqualityFactSearchProofByBuiltinRewrite.
    pub fn search_atomic_except_equality_fact_proof_by_builtin_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinRewrite>> {
        let Some(alternate) = order_dual_atomic_fact(fact, || self.ids.allocate_fact_id()) else {
            return Ok(None);
        };
        let residual_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        let proof_of_alternate_fact = self.verify_atomic_fact(&alternate, residual_state)?;
        if proof_of_alternate_fact.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(
                AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
                    alternate_fact: alternate.into(),
                    proof_of_alternate_fact,
                },
            ),
        ))
    }
}

// Aligns with legacy transposed_binary_order_equivalent (no NotEqual; no plain subset).
fn order_dual_atomic_fact(
    fact: &AtomicFact,
    mut next_fact_id: impl FnMut() -> FactId,
) -> Option<AtomicFact> {
    match fact {
        AtomicFact::LessFact(f) => Some(AtomicFact::GreaterFact(GreaterFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterFact(f) => Some(AtomicFact::LessFact(LessFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessEqualFact(f) => Some(AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterEqualFact(f) => Some(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessFact(f) => Some(AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterFact(f) => Some(AtomicFact::NotLessFact(NotLessFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessEqualFact(f) => {
            Some(AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
                fact_id: next_fact_id(),
                left: f.right.clone(),
                right: f.left.clone(),
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NotGreaterEqualFact(f) => {
            Some(AtomicFact::NotLessEqualFact(NotLessEqualFact {
                fact_id: next_fact_id(),
                left: f.right.clone(),
                right: f.left.clone(),
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::FnEqualInFact(f) => Some(AtomicFact::FnEqualInFact(FnEqualInFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotFnEqualInFact(f) => Some(AtomicFact::NotFnEqualInFact(NotFnEqualInFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NormalAtomicFact(f)
            if f.body.len() == 2
                && matches!(
                    &f.predicate,
                    AtomicName::Plain { name } if name == PROPER_SUBSET || name == PROPER_SUPERSET
                ) =>
        {
            let AtomicName::Plain { name } = &f.predicate else {
                return None;
            };
            let dual_name = if name == PROPER_SUBSET {
                PROPER_SUPERSET
            } else {
                PROPER_SUBSET
            };
            Some(AtomicFact::NormalAtomicFact(NormalAtomicFact {
                fact_id: next_fact_id(),
                predicate: AtomicName::plain(dual_name.to_string()),
                body: vec![f.body[1].clone(), f.body[0].clone()],
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NotNormalAtomicFact(f)
            if f.body.len() == 2
                && matches!(
                    &f.predicate,
                    AtomicName::Plain { name } if name == PROPER_SUBSET || name == PROPER_SUPERSET
                ) =>
        {
            let AtomicName::Plain { name } = &f.predicate else {
                return None;
            };
            let dual_name = if name == PROPER_SUBSET {
                PROPER_SUPERSET
            } else {
                PROPER_SUBSET
            };
            Some(AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact {
                fact_id: next_fact_id(),
                predicate: AtomicName::plain(dual_name.to_string()),
                body: vec![f.body[1].clone(), f.body[0].clone()],
                line_file: f.line_file.clone(),
            }))
        }
        _ => None,
    }
}
