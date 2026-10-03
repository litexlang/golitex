//! Integer translation preserves both index order and the seed of a left fold.
use super::reduce_rule_helper::{reduce_function_at, ReduceObjectMatchProof};
use crate::ast::fact::{EqualFact, Fact, LessEqualFact};
use crate::ast::names::BoundName;
use crate::ast::obj::{IdentifierObj, IteratedOperator, Literal, Obj, StandardSet};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal::AnonFnApplicationBodyProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::helper::{add_objs, sub_objs};
use crate::runtime::{Runtime, RuntimeResult};

pub struct ReduceTranslationProof {
    pub shift: Obj,
    pub matches: Vec<ReduceObjectMatchProof>,
    pub parameter: BoundName,
    pub assumptions: Vec<Fact>,
    pub function_expansions: Vec<AnonFnApplicationBodyProof>,
    pub pointwise: ReduceObjectMatchProof,
    pub local_env: Box<ExecEnv>,
}
impl Runtime {
    pub(super) fn search_reduce_translation(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ReduceTranslationProof>> {
        // reduce(a,b,f,op,s)=reduce(c,d,g,op,s), a-c=b-d and
        // f(k+a-c)=g(k). Interval membership and callable closure come from WD.
        for (lhs, rhs) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::IteratedOperator(IteratedOperator::Reduce(left)) = lhs else {
                continue;
            };
            let Obj::IteratedOperator(IteratedOperator::Reduce(right)) = rhs else {
                continue;
            };
            let raw_shift = sub_objs(*left.start.clone(), *right.start.clone());
            let shift =
                crate::rational_expression::evaluate_obj_to_normalized_decimal_number(&raw_shift)
                    .map(|n| Obj::Literal(Literal::Number(n)))
                    .unwrap_or(raw_shift);
            let shifted_end = add_objs(*right.end.clone(), shift.clone());
            let mut matches = Vec::new();
            for (a, b) in [
                (&*left.end, &shifted_end),
                (&*left.op, &*right.op),
                (&*left.seed, &*right.seed),
            ] {
                let Some(proof) = self.match_reduce_object(a, b) else {
                    break;
                };
                matches.push(proof);
            }
            if matches.len() != 3 {
                continue;
            }
            let parameter = self.fresh_internal_param();
            let index = Obj::Identifier(IdentifierObj::from_bound_name(&parameter));
            let assumptions: Vec<Fact> = vec![
                LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: *right.start.clone(),
                    right: index.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into(),
                LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: index.clone(),
                    right: *right.end.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into(),
            ];
            let (result, local_env) = self.run_in_local_env_and_take_env(|rt| {
                let params = TypedParameterList {
                    groups: vec![TypedParameterGroup {
                        params: vec![parameter.clone()],
                        param_type: ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
                    }],
                };
                rt.define_typed_parameters_in_current_env(&params, None, state)?;
                for assumption in &assumptions {
                    rt.store_fact_and_infer(assumption, state)?;
                }
                let mut expansions = Vec::new();
                let Some(a) = reduce_function_at(
                    rt,
                    &left.func,
                    &add_objs(index.clone(), shift.clone()),
                    &mut expansions,
                )?
                else {
                    return Ok(None);
                };
                let Some(b) = reduce_function_at(rt, &right.func, &index, &mut expansions)? else {
                    return Ok(None);
                };
                Ok(rt.match_reduce_object(&a, &b).map(|p| (expansions, p)))
            })?;
            if let Some((function_expansions, pointwise)) = result {
                return Ok(Some(ReduceTranslationProof {
                    shift,
                    matches,
                    parameter,
                    assumptions,
                    function_expansions,
                    pointwise,
                    local_env,
                }));
            }
        }
        Ok(None)
    }
}
