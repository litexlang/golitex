use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_closed_numeric_equal_substitution::rewrite_closed_numeric_subterms;
use super::helper::atomic_fact_with_args;
use crate::ast::fact::{
    AtomicFact, Fact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact,
    NotGreaterEqualFact, NotGreaterFact, NotLessEqualFact, NotLessFact,
    NotProperSubsetFact, NotProperSupersetFact, ProperSubsetFact, ProperSupersetFact,
};
use crate::ast::fact::atomic_fact_args_ref;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::replace_obj_matching_ir;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::FactId;
use crate::runtime::{Runtime, RuntimeResult};

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
//   KnownEqualObjSubstitution — replace a goal arg by a checked equal
//   peer (e.g. `1 $in S` with stored `S = {…}`), then prove the residual.
//   FnApplicationUnfoldSubstitution — unfold top-level `f(args)` via have-fn
//   definition into the body, then prove the residual (needed when equals are
//   not yet stored, e.g. under forall for `$is_choice_function_for`).
//   OrderDual (prove via order / proper-subset).
// Search order: ClosedNumeric, KnownEqualObj, FnApplicationUnfold, then OrderDual.
pub enum AtomicExceptEqualityFactSearchProofByBuiltinRewrite {
    ClosedNumericEqualSubstitution(
        AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution,
    ),
    KnownEqualObjSubstitution(AtomicExceptEqualityFactSearchProofByKnownEqualObjSubstitution),
    FnApplicationUnfoldSubstitution(
        AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution,
    ),
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

// Known-equality substitution on a non-equality atomic goal.
// Mathematical property: if `a = b` has a stored equality path, then P(…, a, …)
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

// Unfold each top-level FnObj arg via have-fn / anon-fn definition, then prove residual.
// Mathematical property: if `f = fn(...) { body }`, then P(f(args), …) follows from
// P(subst(body), …).
//
// Example:
//   have fn f_choice(alpha {1}) {1} = 1
//   have fn g_choice(alpha {1}) power_set({1}) = {1}
//   forall alpha {1}:
//       f_choice(alpha) $in g_choice(alpha)
// unfolds both applications to prove `1 $in {1}`.
pub struct AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution {
    pub rewritten_fact: Fact,
    pub unfold_equal_proofs: Vec<VerifyFactResult>,
    pub proof_of_rewritten_fact: VerifyFactResult,
}

pub struct AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    // Builtin rewrite dispatcher: ClosedNumeric, KnownEqualObj, FnUnfold, then OrderDual.
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
        if let Some(proof) = self
            .search_atomic_except_equality_by_fn_application_unfold_substitution(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(
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
        let mut rewritten_args = Vec::new();
        let mut cited_equal_fact_ids = Vec::new();
        for arg in atomic_fact_args_ref(fact) {
            let (rewritten, citations) = rewrite_closed_numeric_subterms(arg, &entries);
            rewritten_args.push(rewritten);
            for id in citations {
                if !cited_equal_fact_ids.contains(&id) {
                    cited_equal_fact_ids.push(id);
                }
            }
        }

        if cited_equal_fact_ids.is_empty() {
            return Ok(None);
        }

        let Some(rewritten) =
            atomic_fact_with_args(fact, rewritten_args, self.global_ids.allocate_fact_id())
        else {
            return Ok(None);
        };
        let residual_state = verify_state.without_rewrite();
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

    // Try the finite checked equality class for each goal arg. The residual
    // disables rewrite, so aliases consume stored paths without recursive
    // rewriting or broader child permissions. Every used edge is cited.
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
        let residual_state = verify_state.without_rewrite();

        for (arg_index, arg) in args.iter().enumerate() {
            let from_ir = arg.ir();
            for (peer, path) in equivalence_class_members_with_paths_in_adjacency(&adjacency, arg) {
                if path.is_empty() {
                    continue;
                }
                let mut rewritten_args = args.clone();
                rewritten_args[arg_index] =
                    replace_obj_matching_ir(&rewritten_args[arg_index], &from_ir, &peer);
                if rewritten_args[arg_index].ir() == from_ir {
                    continue;
                }
                let Some(rewritten) =
                    atomic_fact_with_args(fact, rewritten_args, self.global_ids.allocate_fact_id())
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
                        cited_equal_fact_ids: path.into_iter().map(|(_, _, fact_id)| fact_id).collect(),
                        proof_of_rewritten_fact,
                    },
                ));
            }
        }
        Ok(None)
    }

    // Unfold every top-level FnObj arg in one pass, then prove the residual.
    // Example: `f_choice(alpha) $in g_choice(alpha)` → `1 $in {1}` under forall.
    fn search_atomic_except_equality_by_fn_application_unfold_substitution(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution>>
    {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }
        if !verify_state.allows(crate::execute::execute_fact_stmt::VerifyStateLevel::DefinitionAndForall) {
            return Ok(None);
        }
        let args: Vec<Obj> = atomic_fact_args_ref(fact)
            .into_iter()
            .cloned()
            .collect();
        let equal_child_state = verify_state.without_rewrite();
        let residual_state = verify_state.without_rewrite();

        let mut rewritten_args = args.clone();
        let mut unfold_equal_proofs = Vec::new();
        for (arg_index, arg) in args.iter().enumerate() {
            let Obj::FnObj(fn_obj) = arg else {
                continue;
            };
            let Some(expansion) =
                self.expanded_named_or_literal_anon_fn_application_body(fn_obj)?
            else {
                continue;
            };
            let expanded_body = expansion.expanded_body;
            if expanded_body.ir() == arg.ir() {
                continue;
            }
            let equal_goal = crate::ast::fact::EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: arg.clone(),
                right: expanded_body.clone(),
                line_file: None,
            };
            let equal_proof = self.verify_equal_fact(&equal_goal, equal_child_state.clone())?;
            if equal_proof.is_failed() {
                continue;
            }
            rewritten_args[arg_index] = expanded_body;
            unfold_equal_proofs.push(equal_proof);
        }
        if unfold_equal_proofs.is_empty() {
            return Ok(None);
        }
        let Some(rewritten) =
            atomic_fact_with_args(fact, rewritten_args, self.global_ids.allocate_fact_id())
        else {
            return Ok(None);
        };
        let proof_of_rewritten_fact = self.verify_atomic_fact(&rewritten, residual_state)?;
        if proof_of_rewritten_fact.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution {
                rewritten_fact: rewritten.into(),
                unfold_equal_proofs,
                proof_of_rewritten_fact,
            },
        ))
    }

    fn search_atomic_except_equality_by_order_dual(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinOrderDual>> {
        let Some(alternate) = order_dual_atomic_fact(fact, || self.global_ids.allocate_fact_id()) else {
            return Ok(None);
        };
        let residual_state = verify_state.without_rewrite();
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
        AtomicFact::ProperSubsetFact(f) => Some(AtomicFact::ProperSupersetFact(ProperSupersetFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::ProperSupersetFact(f) => Some(AtomicFact::ProperSubsetFact(ProperSubsetFact {
            fact_id: next_fact_id(),
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotProperSubsetFact(f) => {
            Some(AtomicFact::NotProperSupersetFact(NotProperSupersetFact {
                fact_id: next_fact_id(),
                left: f.right.clone(),
                right: f.left.clone(),
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NotProperSupersetFact(f) => {
            Some(AtomicFact::NotProperSubsetFact(NotProperSubsetFact {
                fact_id: next_fact_id(),
                left: f.right.clone(),
                right: f.left.clone(),
                line_file: f.line_file.clone(),
            }))
        }
        _ => None,
    }
}
