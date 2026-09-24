//! Helpers for algo setup: resolve FnSet, retag params, build agreement foralls.

use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, negate_atomic_fact, AndChainAtomicFact, AtomicFact, EqualFact,
    ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, OrFact,
};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{
    ArithmeticOperator, FnObj, FnObjHead, IdentifierObj, IntegerOperator, Obj, FnSet,
};
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

use super::result::{ExecDefAlgoSetup, ExecDefAlgoStmtFailed};

pub(super) fn resolve_target_fn_set(
    runtime: &Runtime,
    stmt: &DefAlgoStmt,
) -> Result<(FnSet, FactId), ExecDefAlgoStmtFailed> {
    let head = match runtime.identifier_obj_for_plain_free_ref(stmt.name.clone()) {
        Ok(h) => h,
        Err(_) => return Err(ExecDefAlgoStmtFailed::TargetFnMissing),
    };
    let candidates = runtime.collect_in_function_set_candidates(&Obj::Identifier(head));
    let Some((fn_set, fact_id)) = candidates.into_iter().next() else {
        return Err(ExecDefAlgoStmtFailed::TargetFnMissing);
    };
    Ok((fn_set, fact_id))
}

pub(super) fn build_algo_setup(
    runtime: &mut Runtime,
    stmt: &DefAlgoStmt,
    fn_set: FnSet,
) -> RuntimeResult<Result<ExecDefAlgoSetup, ExecDefAlgoStmtFailed>> {
    let fn_param_count = set_bound_parameter_count(&fn_set.set_bound_parameters);
    if fn_param_count != stmt.param_bindings.len() {
        return Ok(Err(ExecDefAlgoStmtFailed::BadShape(format!(
            "algo param count {} does not match fn arity {}",
            stmt.param_bindings.len(),
            fn_param_count
        ))));
    }
    if stmt.cases.is_empty() && stmt.default_return.is_none() {
        return Ok(Err(ExecDefAlgoStmtFailed::BadShape(
            "algo has no case and no default return".to_string(),
        )));
    }

    let algo_bounds = algo_param_bound_names(runtime, stmt);
    let mut active_fn_param_map: HashMap<IdentifierId, Obj> = HashMap::new();
    let mut algo_param_objs: Vec<Obj> = Vec::with_capacity(algo_bounds.len());
    let mut typed_groups: Vec<TypedParameterGroup> = Vec::new();
    let mut algo_bound_iter = algo_bounds.iter();

    for group in &fn_set.set_bound_parameters.groups {
        let inst_type = match runtime.inst_obj(group.param_type.as_ref(), &active_fn_param_map) {
            Ok(o) => o,
            Err(err) => {
                return Ok(Err(ExecDefAlgoStmtFailed::BadShape(format!(
                    "algo: failed to instantiate fn param type: {err}"
                ))));
            }
        };
        for fn_param in &group.params {
            let Some(algo_bound) = algo_bound_iter.next() else {
                return Ok(Err(ExecDefAlgoStmtFailed::BadShape(
                    "algo: internal param zip error".to_string(),
                )));
            };
            let algo_obj = Obj::Identifier(IdentifierObj::from_bound_name(algo_bound));
            active_fn_param_map.insert(fn_param.id, algo_obj.clone());
            algo_param_objs.push(algo_obj);
            typed_groups.push(TypedParameterGroup {
                params: vec![algo_bound.clone()],
                param_type: ParamType::Obj(inst_type.clone()),
            });
        }
    }

    let mut requirement_facts: Vec<Fact> = Vec::new();
    for group in &typed_groups {
        let ParamType::Obj(set) = &group.param_type else {
            return Ok(Err(ExecDefAlgoStmtFailed::BadShape(
                "algo: expected Obj param type".to_string(),
            )));
        };
        for param in &group.params {
            requirement_facts.push(Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: runtime.global_ids.allocate_fact_id(),
                element: Obj::Identifier(IdentifierObj::from_bound_name(param)),
                set: set.clone(),
                line_file: Some(stmt.line_file.clone()),
            })));
        }
    }
    for dom in &fn_set.dom_facts {
        match runtime.inst_quantifier_free_fact(dom, &active_fn_param_map) {
            Ok(qf) => requirement_facts.push(quantifier_free_fact_to_fact(qf)),
            Err(err) => {
                return Ok(Err(ExecDefAlgoStmtFailed::BadShape(format!(
                    "algo: failed to instantiate fn domain fact: {err}"
                ))));
            }
        }
    }

    let head = match runtime.identifier_obj_for_plain_free_ref(stmt.name.clone()) {
        Ok(h) => h,
        Err(_) => return Ok(Err(ExecDefAlgoStmtFailed::TargetFnMissing)),
    };
    let function_call = Obj::FnObj(FnObj {
        head: Box::new(FnObjHead::Identifier(head)),
        body: vec![algo_param_objs.into_iter().map(Box::new).collect()],
    });

    Ok(Ok(ExecDefAlgoSetup {
        fn_set,
        parameter_definition: TypedParameterList {
            groups: typed_groups,
        },
        function_call,
        requirement_facts,
    }))
}

pub(super) fn case_agreement_forall(
    runtime: &mut Runtime,
    stmt: &DefAlgoStmt,
    setup: &ExecDefAlgoSetup,
    case_index: usize,
) -> Fact {
    let case = &stmt.cases[case_index];
    let mut dom_facts = setup.requirement_facts.clone();
    dom_facts.push(Fact::AtomicFact(case.condition.clone()));

    let equal = AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: setup.function_call.clone(),
        right: case.return_stmt.value.clone(),
        line_file: Some(case.line_file.clone()),
    });

    Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: setup.parameter_definition.clone(),
        dom_facts,
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(equal)],
        line_file: Some(case.line_file.clone()),
    })
}

pub(super) fn default_agreement_forall(
    runtime: &mut Runtime,
    stmt: &DefAlgoStmt,
    setup: &ExecDefAlgoSetup,
) -> Result<Fact, ExecDefAlgoStmtFailed> {
    let Some(default_return) = &stmt.default_return else {
        return Err(ExecDefAlgoStmtFailed::BadShape(
            "algo default branch missing".to_string(),
        ));
    };

    let mut dom_facts = setup.requirement_facts.clone();
    for case in &stmt.cases {
        let Some(negated) =
            negate_atomic_fact(&case.condition, runtime.global_ids.allocate_fact_id())
        else {
            return Err(ExecDefAlgoStmtFailed::BadShape(
                "algo: cannot negate case condition for default branch".to_string(),
            ));
        };
        dom_facts.push(Fact::AtomicFact(negated));
    }

    let equal = AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: setup.function_call.clone(),
        right: default_return.value.clone(),
        line_file: Some(default_return.line_file.clone()),
    });

    Ok(Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: setup.parameter_definition.clone(),
        dom_facts,
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(equal)],
        line_file: Some(default_return.line_file.clone()),
    }))
}

pub(super) fn coverage_forall(
    runtime: &mut Runtime,
    stmt: &DefAlgoStmt,
    setup: &ExecDefAlgoSetup,
) -> Result<Fact, ExecDefAlgoStmtFailed> {
    if stmt.cases.is_empty() {
        return Err(ExecDefAlgoStmtFailed::BadShape(
            "algo coverage: no cases".to_string(),
        ));
    }

    let branches: Vec<AndChainAtomicFact> = stmt
        .cases
        .iter()
        .map(|c| AndChainAtomicFact::AtomicFact(c.condition.clone()))
        .collect();
    let or_fact = OrFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        facts: branches,
        line_file: Some(stmt.line_file.clone()),
    };

    Ok(Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: setup.parameter_definition.clone(),
        dom_facts: setup.requirement_facts.clone(),
        then_facts: vec![ExistOrAndChainAtomicFact::OrFact(or_fact)],
        line_file: Some(stmt.line_file.clone()),
    }))
}

fn algo_param_bound_names(runtime: &mut Runtime, stmt: &DefAlgoStmt) -> Vec<BoundName> {
    let mut out = Vec::with_capacity(stmt.param_bindings.len());
    for name in &stmt.param_bindings {
        if let Some(id) = find_plain_id_in_algo_stmt(stmt, name) {
            out.push(BoundName::new(id, name.clone()));
        } else {
            out.push(BoundName::new(
                runtime.global_ids.allocate_identifier_id(),
                name.clone(),
            ));
        }
    }
    out
}

fn find_plain_id_in_algo_stmt(stmt: &DefAlgoStmt, name: &str) -> Option<IdentifierId> {
    for case in &stmt.cases {
        if let Some(id) = find_plain_id_in_atomic(&case.condition, name) {
            return Some(id);
        }
        if let Some(id) = find_plain_id_in_obj(&case.return_stmt.value, name) {
            return Some(id);
        }
    }
    if let Some(default) = &stmt.default_return {
        if let Some(id) = find_plain_id_in_obj(&default.value, name) {
            return Some(id);
        }
    }
    None
}

fn find_plain_id_in_atomic(fact: &AtomicFact, name: &str) -> Option<IdentifierId> {
    for obj in atomic_fact_args_ref(fact) {
        if let Some(id) = find_plain_id_in_obj(obj, name) {
            return Some(id);
        }
    }
    None
}

fn find_plain_id_in_obj(obj: &Obj, name: &str) -> Option<IdentifierId> {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id, name: n }) if n == name => Some(*id),
        Obj::FnObj(f) => {
            for group in &f.body {
                for arg in group {
                    if let Some(id) = find_plain_id_in_obj(arg, name) {
                        return Some(id);
                    }
                }
            }
            None
        }
        Obj::ArithmeticOperator(op) => find_plain_id_in_arith(op, name),
        Obj::IntegerOperator(op) => find_plain_id_in_int(op, name),
        _ => None,
    }
}

fn find_plain_id_in_arith(op: &ArithmeticOperator, name: &str) -> Option<IdentifierId> {
    use ArithmeticOperator::*;
    let objs: Vec<&Obj> = match op {
        Add(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Sub(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Mul(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Div(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Neg(a) => vec![a.arg.as_ref()],
        Pow(a) => vec![a.base.as_ref(), a.exponent.as_ref()],
        Abs(a) => vec![a.arg.as_ref()],
        Min(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Max(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Floor(a) => vec![a.arg.as_ref()],
        Ceil(a) => vec![a.arg.as_ref()],
        Sign(a) => vec![a.arg.as_ref()],
    };
    for o in objs {
        if let Some(id) = find_plain_id_in_obj(o, name) {
            return Some(id);
        }
    }
    None
}

fn find_plain_id_in_int(op: &IntegerOperator, name: &str) -> Option<IdentifierId> {
    use IntegerOperator::*;
    let objs: Vec<&Obj> = match op {
        Mod(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Quot(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Gcd(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Lcm(a) => vec![a.left.as_ref(), a.right.as_ref()],
        Factorial(a) => vec![a.arg.as_ref()],
    };
    for o in objs {
        if let Some(id) = find_plain_id_in_obj(o, name) {
            return Some(id);
        }
    }
    None
}

fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    list.groups.iter().map(|g| g.params.len()).sum()
}
