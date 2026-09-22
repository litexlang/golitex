use super::helper::atomic_fact_with_args;
use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, FnEqualInFact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotFnEqualInFact, NotGreaterEqualFact, NotGreaterFact, NotLessEqualFact,
    NotLessFact, NotNormalAtomicFact,
};
use crate::new_pipeline::ast::fact::atomic_fact_args_ref;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::replace_obj_matching_ir;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::{PROPER_SUBSET, PROPER_SUPERSET};
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rewrite for atomic-except-equality facts.
//
// Why this stage exists (ClosedNumeric part):
//   Order / membership builtins such as ClosedNumericComparison need closed
//   numeric args. Goals often still carry identifiers equal to a stored closed
//   form (`have a R = 10`, goal `a > 0`). Rewrite fills those representatives
//   into the goal, then proves the residual with rewrite off — explicit cite,
//   not silent resolve_obj.
//
// Also here:
//   KnownEqualObjSubstitution — replace a goal arg by a one-hop known equal
//   peer (e.g. `1 $in S` with stored `S = {…}`), then prove the residual.
//   OrderDual (prove via order / proper-subset / fn_eq_in dual).
// Search order: ClosedNumeric, KnownEqualObj, then OrderDual.
pub enum AtomicExceptEqualityFactSearchProofByBuiltinRewrite {
    ClosedNumericEqualSubstitution(
        AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution,
    ),
    KnownEqualObjSubstitution(AtomicExceptEqualityFactSearchProofByKnownEqualObjSubstitution),
    OrderDual(AtomicExceptEqualityFactSearchProofByBuiltinOrderDual),
}

// Closed-numeric index substitution on a non-equality atomic goal.
// Mathematical property: if `a = closed` is indexed (`ClosedNumericExpr` view),
// then P(F[a], …) follows from P(F[closed], …) for supported F.
//
// Example:
//   trust a = 10
//   a > 0
// rewrite goal to `10 > 0`, then ClosedNumericComparison proves it.
pub struct AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution {
    pub rewritten_fact: Fact,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub proof_of_rewritten_fact: VerifyFactResult,
}

// One-hop known-equality substitution on a non-equality atomic goal.
// Mathematical property: if `a = b` is a stored generating edge, then P(…, a, …)
// follows from P(…, b, …).
//
// Example:
//   have S set = {x R: x > 0}
//   1 $in S
// rewrite set arg to the stored set-builder, then SetBuilderMembership.
pub struct AtomicExceptEqualityFactSearchProofByKnownEqualObjSubstitution {
    pub rewritten_fact: Fact,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub proof_of_rewritten_fact: VerifyFactResult,
}

pub struct AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    // Builtin rewrite dispatcher: ClosedNumeric, KnownEqualObj, then OrderDual.
    pub fn search_atomic_except_equality_fact_proof_by_builtin_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinRewrite>> {
        if let Some(proof) = self
            .search_atomic_except_equality_by_closed_numeric_equal_substitution(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
                    proof,
                ),
            ));
        }
        if let Some(proof) = self
            .search_atomic_except_equality_by_known_equal_obj_substitution(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(
                    proof,
                ),
            ));
        }
        if let Some(proof) =
            self.search_atomic_except_equality_by_order_dual(fact, verify_state)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(proof),
            ));
        }
        Ok(None)
    }

    fn search_atomic_except_equality_by_closed_numeric_equal_substitution(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution>>
    {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }
        let entries = self.visible_closed_numeric_equal_entries();
        let mut rewritten_args: Vec<Obj> = atomic_fact_args_ref(fact)
            .into_iter()
            .cloned()
            .collect();
        let mut cited_equal_fact_ids = Vec::new();

        for (from_ir, closed, fact_id) in &entries {
            let closed_obj = closed.to_obj();
            let mut changed = false;
            let next_args: Vec<Obj> = rewritten_args
                .iter()
                .map(|arg| {
                    let next = replace_obj_matching_ir(arg, from_ir, &closed_obj);
                    if next.ir() != arg.ir() {
                        changed = true;
                    }
                    next
                })
                .collect();
            if !changed {
                continue;
            }
            rewritten_args = next_args;
            cited_equal_fact_ids.push(*fact_id);
        }

        if cited_equal_fact_ids.is_empty() {
            return Ok(None);
        }

        let Some(rewritten) =
            atomic_fact_with_args(fact, rewritten_args, self.ids.allocate_fact_id())
        else {
            return Ok(None);
        };
        let residual_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        let proof_of_rewritten_fact = self.verify_atomic_fact(&rewritten, residual_state)?;
        if proof_of_rewritten_fact.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution {
                rewritten_fact: rewritten.into(),
                cited_equal_fact_ids,
                proof_of_rewritten_fact,
            },
        ))
    }

    // Try one-hop known equals for each goal arg; first residual success wins.
    // Example: `1 $in S` with stored `S = {x R: x > 0}` → prove `1 $in {…}`.
    fn search_atomic_except_equality_by_known_equal_obj_substitution(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownEqualObjSubstitution>>
    {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }
        let args: Vec<Obj> = atomic_fact_args_ref(fact)
            .into_iter()
            .cloned()
            .collect();
        let adjacency = self.visible_equivalence_class_adjacency();
        let residual_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };

        for (arg_index, arg) in args.iter().enumerate() {
            let from_ir = arg.ir();
            let Some(neighbors) = adjacency.get(&from_ir) else {
                continue;
            };
            for (_peer_key, equal_fact) in neighbors.iter() {
                let peer = if equal_fact.left.ir() == from_ir {
                    &equal_fact.right
                } else {
                    &equal_fact.left
                };
                if peer.ir() == from_ir {
                    continue;
                }
                let mut rewritten_args = args.clone();
                rewritten_args[arg_index] =
                    replace_obj_matching_ir(&rewritten_args[arg_index], &from_ir, peer);
                if rewritten_args[arg_index].ir() == from_ir {
                    continue;
                }
                let Some(rewritten) =
                    atomic_fact_with_args(fact, rewritten_args, self.ids.allocate_fact_id())
                else {
                    continue;
                };
                let proof_of_rewritten_fact =
                    self.verify_atomic_fact(&rewritten, residual_state.clone())?;
                if proof_of_rewritten_fact.is_failed() {
                    continue;
                }
                return Ok(Some(
                    AtomicExceptEqualityFactSearchProofByKnownEqualObjSubstitution {
                        rewritten_fact: rewritten.into(),
                        cited_equal_fact_ids: vec![equal_fact.fact_id],
                        proof_of_rewritten_fact,
                    },
                ));
            }
        }
        Ok(None)
    }

    fn search_atomic_except_equality_by_order_dual(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinOrderDual>> {
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
        Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
            alternate_fact: alternate.into(),
            proof_of_alternate_fact,
        }))
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
