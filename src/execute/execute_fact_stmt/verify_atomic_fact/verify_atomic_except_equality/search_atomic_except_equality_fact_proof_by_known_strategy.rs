//! Non-equality atomic → user-defined known strategy.
//!
//! Used only from the StrategySearch subtree (top `verify_by_strategy` or
//! nested strategy requirements). Source: `strategy_definitions` on the
//! ExecEnv stack (not ambient known_forall).
//!
//! Apply pipeline for one strategy then-clause (soft miss → continue):
//! 1. then must be a direct AtomicFact with matching prop / polarity
//! 2. `match_forall_conclusion_args`
//! 3. prove param-type and dom requirements inside StrategySearch
//!
//! Example:
//!   strategy use_is_one: ? forall x R: x = 1 =>: $is_one(x)
//!   goal `$is_one(a)` with `a = 1` known
//!   → ByKnownStrategy { strategy_name: use_is_one, then_index: 0, … }

use crate::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity, AtomicFact, ExistOrAndChainAtomicFact,
    ForallFact,
};
use crate::ast::names::PlainName;
use crate::ast::stmt::DefStrategyStmt;
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::SearchProofByKnownStrategy;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    ForallParamTypeRequirementProof, ProveForallInstantiationRequirementsProof,
};
use crate::ast::fact::{Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact};
use crate::ast::obj::Obj;
use crate::ast::param::ParamType;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_known_strategy(
        &mut self,
        goal: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<SearchProofByKnownStrategy>> {
        let candidates = self.visible_strategy_definitions();
        for (name, stmt) in candidates {
            if let Some(proof) =
                self.try_apply_known_strategy(goal, &name, &stmt.forall_fact, ctx)?
            {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn visible_strategy_definitions(&self) -> Vec<(PlainName, DefStrategyStmt)> {
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (name, stmt) in env.definitions.strategy_definitions.iter() {
                out.push((name.clone(), stmt.clone()));
            }
        }
        out
    }

    fn try_apply_known_strategy(
        &mut self,
        goal: &AtomicFact,
        strategy_name: &PlainName,
        forall: &ForallFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<SearchProofByKnownStrategy>> {
        for (then_index, then) in forall.then_facts.iter().enumerate() {
            let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = then else {
                continue;
            };
            // Equality conclusions belong to the equality search path, not here.
            if matches!(conclusion, AtomicFact::EqualFact(_)) {
                continue;
            }
            if conclusion.prop_name() != goal.prop_name()
                || atomic_fact_has_positive_polarity(conclusion)
                    != atomic_fact_has_positive_polarity(goal)
            {
                continue;
            }

            let param_ids = forall.typed_parameters.ordered_param_ids();
            let conclusion_args = atomic_fact_args_ref(conclusion);
            let goal_args = atomic_fact_args_ref(goal);

            let Some(matched) =
                self.match_forall_conclusion_args(&conclusion_args, &goal_args, &param_ids)?
            else {
                continue;
            };

            let subst =
                subst_from_ordered_params(&param_ids, &matched.forall_parameters_match_what_args);
            let Some(instantiation_requirements) =
                self.prove_forall_instantiation_requirements_in_strategy(forall, &subst, ctx)?
            else {
                continue;
            };

            return Ok(Some(SearchProofByKnownStrategy {
                strategy_name: strategy_name.clone(),
                then_index,
                forall_parameters_match_what_args: matched.forall_parameters_match_what_args,
                arg_match_proofs: matched.arg_match_proofs,
                instantiation_requirements,
            }));
        }
        Ok(None)
    }

    fn prove_forall_instantiation_requirements_in_strategy(
        &mut self,
        forall: &ForallFact,
        subst: &HashMap<IdentifierId, Obj>,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<ProveForallInstantiationRequirementsProof>> {
        let child = ctx.after_layer();
        let mut param_type_requirements = Vec::new();
        for group in &forall.typed_parameters.groups {
            let param_type = match self.inst_param_type(&group.param_type, subst) {
                Ok(param_type) => param_type,
                Err(_) => return Ok(None),
            };
            for param in &group.params {
                let Some(arg) = subst.get(&param.id) else {
                    return Ok(None);
                };
                let type_fact = type_fact_for_instantiated_arg_strategy(
                    arg.clone(),
                    &param_type,
                    self.global_ids.allocate_fact_id(),
                );
                let proof = self.verify_fact_in_strategy(&type_fact, child)?;
                if proof.is_failed() {
                    return Ok(None);
                }
                param_type_requirements.push(ForallParamTypeRequirementProof {
                    param_id: param.id,
                    arg: arg.clone(),
                    type_fact,
                    proof,
                });
            }
        }

        let mut dom_facts = Vec::new();
        for dom in &forall.dom_facts {
            let fact = match self.inst_fact(dom, subst) {
                Ok(fact) => fact,
                Err(_) => return Ok(None),
            };
            dom_facts.push(fact);
        }
        let mut proof_of_dom_facts = Vec::with_capacity(dom_facts.len());
        for fact in &dom_facts {
            let proof = self.verify_fact_in_strategy(fact, child)?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_dom_facts.push(proof);
        }

        Ok(Some(ProveForallInstantiationRequirementsProof {
            param_type_requirements,
            dom_facts,
            proof_of_dom_facts,
        }))
    }
}

fn type_fact_for_instantiated_arg_strategy(
    arg: Obj,
    param_type: &ParamType,
    fact_id: crate::runtime::FactId,
) -> Fact {
    match param_type {
        ParamType::Obj(param_set) => Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id,
            element: arg,
            set: param_set.clone(),
            line_file: None,
        })),
        ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: arg,
            line_file: None,
        })),
        ParamType::NonemptySet(_) => {
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                fact_id,
                set: arg,
                line_file: None,
            }))
        }
        ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: arg,
            line_file: None,
        })),
    }
}
