use crate::ast::obj::{FnObj, FnObjHead, IdentifierObj, Literal, Number, Obj};
use crate::ast::param::SetBoundParameterList;
use crate::runtime::runtime_ids::IdentifierId;
use std::collections::HashSet;

pub const MAX_EVAL_DEPTH: usize = 64;

pub fn is_number_literal(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(_)))
}

pub fn number_literal_key(obj: &Obj) -> Option<String> {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => {
            Some(normalized_value.clone())
        }
        _ => None,
    }
}

pub fn fn_obj_plain_name(fn_obj: &FnObj) -> Option<String> {
    match fn_obj.head.as_ref() {
        FnObjHead::Identifier(IdentifierObj::Plain { name, .. }) => Some(name.clone()),
        _ => None,
    }
}

pub fn flatten_fn_obj_args(fn_obj: &FnObj) -> Vec<Obj> {
    let mut out = Vec::new();
    for group in &fn_obj.body {
        for arg in group {
            out.push(arg.as_ref().clone());
        }
    }
    out
}

pub fn algo_call_key(fn_name: &str, evaluated_args: &[Obj]) -> Option<String> {
    let mut parts = Vec::with_capacity(evaluated_args.len());
    for arg in evaluated_args {
        crate::rational_expression::ClosedNumericExpr::try_from_obj(arg)?;
        parts.push(arg.ir().display_string());
    }
    Some(format!("{fn_name}({})", parts.join(",")))
}

pub fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

pub fn build_algo_param_subst(
    params: &SetBoundParameterList,
    evaluated_args: &[Obj],
) -> Option<std::collections::HashMap<IdentifierId, Obj>> {
    if set_bound_parameter_count(params) != evaluated_args.len() {
        return None;
    }
    let mut map = std::collections::HashMap::new();
    let mut i = 0;
    for group in &params.groups {
        for param in &group.params {
            map.insert(param.id, evaluated_args[i].clone());
            i += 1;
        }
    }
    Some(map)
}

// Per-evaluation state, never stored on Runtime/ExecEnv. Nested aggregates share
// the same allowance instead of each receiving a fresh full range budget.
pub const MAX_AGGREGATE_TERMS: usize = 1024;
pub struct ActiveAlgoCalls {
    calls: HashSet<String>,
    pub aggregate_terms_remaining: usize,
    pub aggregate_evaluations: Vec<super::aggregate_evaluation_result::AggregateEvaluationResult>,
    pub function_evaluations:
        Vec<super::aggregate_evaluation_result::FunctionApplicationEvaluationResult>,
    pub algo_evaluations: Vec<super::aggregate_evaluation_result::AlgoApplicationEvaluationResult>,
    pub cited_equal_fact_ids: Vec<crate::runtime::FactId>,
    pub proof_mode: bool,
    pub function_proof_state: crate::execute::execute_fact_stmt::VerifyState,
}
impl ActiveAlgoCalls {
    pub fn new() -> Self {
        Self {
            calls: HashSet::new(),
            aggregate_terms_remaining: MAX_AGGREGATE_TERMS,
            aggregate_evaluations: vec![],
            function_evaluations: vec![],
            algo_evaluations: vec![],
            cited_equal_fact_ids: vec![],
            proof_mode: false,
            function_proof_state: crate::execute::execute_fact_stmt::VerifyState::top_level()
                ,
        }
    }
    pub fn contains(&self, key: &str) -> bool {
        self.calls.contains(key)
    }
    pub fn insert(&mut self, key: String) {
        self.calls.insert(key);
    }
    pub fn remove(&mut self, key: &str) {
        self.calls.remove(key);
    }
}
