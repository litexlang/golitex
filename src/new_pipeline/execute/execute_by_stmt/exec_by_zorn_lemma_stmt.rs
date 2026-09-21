use std::collections::HashMap;

use super::helper::{
    proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ExecByStmtResult, ExecByZornLemmaStmtFailed, ExecByZornLemmaStmtResult,
    ExecByZornLemmaStmtSuccess,
};
use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact,
    IsNonemptySetFact, NormalAtomicFact, OrFact, PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::{AtomicName, BoundName};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj, PowerSet};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::ast::stmt::{ByZornLemmaStmt, DefPropStmt};
use crate::new_pipeline::parse::prop_registration_shape::plain_prop_name;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_zorn_lemma_stmt(
    runtime: &mut Runtime,
    stmt: &ByZornLemmaStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let set_wd = runtime.verify_obj_well_definedness(&stmt.set, proof_verify_state())?;
    if set_wd.is_failed() {
        return Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Failed(
            ExecByZornLemmaStmtFailed::SetWd(set_wd),
        )));
    }

    if let Err(msg) = validate_zorn_named_properties(runtime, stmt) {
        return Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Failed(
            ExecByZornLemmaStmtFailed::PropInterface(msg),
        )));
    }

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof_steps = match run_fact_only_proof_steps(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => {
                return Ok(Err(ExecByZornLemmaStmtFailed::ProofBody(failed)));
            }
        };

        let obligations_facts = zorn_lemma_obligations(
            rt,
            &stmt.set,
            &stmt.prop_name,
            &stmt.upper_bound_prop_name,
            &stmt.line_file,
        );
        let mut obligations = Vec::with_capacity(obligations_facts.len());
        for (index, fact) in obligations_facts.into_iter().enumerate() {
            let proof = verify_goal_fact(rt, &fact)?;
            if proof.is_failed() {
                return Ok(Err(ExecByZornLemmaStmtFailed::Obligation {
                    index,
                    result: proof,
                }));
            }
            obligations.push(proof);
        }
        Ok(Ok((proof_steps, obligations)))
    })?;

    let (proof_steps, obligations) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Failed(
                failed,
            )));
        }
    };

    // Trusted Zorn step. Both quantified conditions that occur below an
    // existential are public named props: the chain obligation concludes
    // `exist u S st {$U(c, u)}`, and this step concludes
    // `exist m S st {$M(m)}`. Their exact definitions were checked above.
    let maximal_fact =
        zorn_lemma_maximal_fact(runtime, &stmt.set, &stmt.maximal_prop_name, &stmt.line_file);
    let stored = match store_goal_fact(runtime, &maximal_fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Failed(
                ExecByZornLemmaStmtFailed::Store(msg),
            )));
        }
    };

    Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Success(
        ExecByZornLemmaStmtSuccess {
            set_wd,
            proof_steps,
            obligations,
            local_env,
            stored,
        },
    )))
}

fn validate_zorn_named_properties(
    runtime: &mut Runtime,
    stmt: &ByZornLemmaStmt,
) -> Result<(), String> {
    let relation_name = plain_prop_name(&stmt.prop_name);
    match user_defined_prop_arity(runtime, relation_name) {
        Some(2) => {}
        Some(_) => {
            return Err(format!(
                "by zorn_lemma: relation `{relation_name}` must be a binary user-defined prop"
            ));
        }
        None => {
            return Err(format!(
                "by zorn_lemma: relation `{relation_name}` must be a user-defined prop"
            ));
        }
    }
    validate_zorn_upper_bound_prop(runtime, stmt)?;
    validate_zorn_maximal_prop(runtime, stmt)?;
    Ok(())
}

fn validate_zorn_upper_bound_prop(
    runtime: &mut Runtime,
    stmt: &ByZornLemmaStmt,
) -> Result<(), String> {
    let name = plain_prop_name(&stmt.upper_bound_prop_name);
    let Some(definition) = runtime.def_prop_visible_in_stack(name).cloned() else {
        return Err(format!(
            "by zorn_lemma: upper-bound `{name}` must be a concrete named prop"
        ));
    };
    if typed_param_count(&definition.typed_parameters) != 2 {
        return Err(format!(
            "by zorn_lemma: upper-bound `{name}` must have two parameters `(c power_set(S), u S)`"
        ));
    }

    let chain = fresh_bound_obj(runtime, "_zorn_c");
    let upper = fresh_bound_obj(runtime, "_zorn_u");
    let args = vec![chain.clone(), upper.clone()];
    let expected_sets = vec![
        Obj::PowerSet(PowerSet {
            set: Box::new(stmt.set.clone()),
        }),
        stmt.set.clone(),
    ];
    if !zorn_prop_header_types_match(runtime, &definition, &args, &expected_sets)? {
        return Err(format!(
            "by zorn_lemma: upper-bound `{name}` must bind `(c power_set({}), u {})`",
            stmt.set.display_string(),
            stmt.set.display_string()
        ));
    }

    let expected = zorn_upper_bound_forall_fact(
        runtime,
        &chain,
        &upper,
        &stmt.prop_name,
        &stmt.line_file,
    );
    if !zorn_prop_has_exact_forall_definition(runtime, &definition, &args, &expected)? {
        return Err(format!(
            "by zorn_lemma: upper-bound `{name}` must have exactly the definition `forall x c: ${}(x, u)`",
            stmt.prop_name
        ));
    }
    Ok(())
}

fn validate_zorn_maximal_prop(
    runtime: &mut Runtime,
    stmt: &ByZornLemmaStmt,
) -> Result<(), String> {
    let name = plain_prop_name(&stmt.maximal_prop_name);
    let Some(definition) = runtime.def_prop_visible_in_stack(name).cloned() else {
        return Err(format!(
            "by zorn_lemma: maximality `{name}` must be a concrete named prop"
        ));
    };
    if typed_param_count(&definition.typed_parameters) != 1 {
        return Err(format!(
            "by zorn_lemma: maximality `{name}` must have one parameter `(m S)`"
        ));
    }

    let maximal = fresh_bound_obj(runtime, "_zorn_m");
    let args = vec![maximal.clone()];
    let expected_sets = vec![stmt.set.clone()];
    if !zorn_prop_header_types_match(runtime, &definition, &args, &expected_sets)? {
        return Err(format!(
            "by zorn_lemma: maximality `{name}` must bind `(m {})`",
            stmt.set.display_string()
        ));
    }

    let expected = zorn_maximal_forall_fact(
        runtime,
        &stmt.set,
        &maximal,
        &stmt.prop_name,
        &stmt.line_file,
    );
    if !zorn_prop_has_exact_forall_definition(runtime, &definition, &args, &expected)? {
        return Err(format!(
            "by zorn_lemma: maximality `{name}` must have exactly the definition `forall x {}: ${}(m, x) => x = m`",
            stmt.set.display_string(),
            stmt.prop_name
        ));
    }
    Ok(())
}

fn zorn_prop_header_types_match(
    runtime: &mut Runtime,
    definition: &DefPropStmt,
    args: &[Obj],
    expected_sets: &[Obj],
) -> Result<bool, String> {
    let subst = typed_params_to_arg_map(&definition.typed_parameters, args)?;
    let mut actual_sets = Vec::new();
    for group in &definition.typed_parameters.groups {
        let ParamType::Obj(actual) = &group.param_type else {
            return Ok(false);
        };
        let inst = runtime
            .inst_obj(actual, &subst)
            .map_err(|e| e.to_string())?;
        for _ in &group.params {
            actual_sets.push(inst.clone());
        }
    }
    if actual_sets.len() != expected_sets.len() {
        return Ok(false);
    }
    Ok(actual_sets
        .iter()
        .zip(expected_sets.iter())
        .all(|(a, e)| a.ir() == e.ir()))
}

fn zorn_prop_has_exact_forall_definition(
    runtime: &mut Runtime,
    definition: &DefPropStmt,
    args: &[Obj],
    expected: &ForallFact,
) -> Result<bool, String> {
    let [Fact::ForallFact(actual)] = definition.iff_facts.as_slice() else {
        return Ok(false);
    };
    let subst = typed_params_to_arg_map(&definition.typed_parameters, args)?;
    let Fact::ForallFact(actual_inst) = runtime
        .inst_fact(&Fact::ForallFact(actual.clone()), &subst)
        .map_err(|e| e.to_string())?
    else {
        return Ok(false);
    };
    Ok(forall_body_ir_equal(&actual_inst, expected))
}

fn forall_body_ir_equal(left: &ForallFact, right: &ForallFact) -> bool {
    let left_ids = left.typed_parameters.ordered_param_ids();
    let right_ids = right.typed_parameters.ordered_param_ids();
    if left_ids.len() != right_ids.len() {
        return false;
    }
    if left.typed_parameters.groups.len() != right.typed_parameters.groups.len() {
        return false;
    }
    for (lg, rg) in left
        .typed_parameters
        .groups
        .iter()
        .zip(right.typed_parameters.groups.iter())
    {
        if lg.params.len() != rg.params.len() {
            return false;
        }
        if param_type_ir(&lg.param_type) != param_type_ir(&rg.param_type) {
            return false;
        }
    }
    if left.dom_facts.len() != right.dom_facts.len()
        || left.then_facts.len() != right.then_facts.len()
    {
        return false;
    }
    let mut map: HashMap<IdentifierId, IdentifierId> = HashMap::new();
    for (l, r) in left_ids.into_iter().zip(right_ids.into_iter()) {
        map.insert(l, r);
    }
    let left_dom: Vec<_> = left
        .dom_facts
        .iter()
        .map(|f| remap_fact_binder_ids(f, &map))
        .collect();
    let right_dom: Vec<_> = right.dom_facts.iter().map(|f| f.ir().0).collect();
    if left_dom != right_dom {
        return false;
    }
    let left_then: Vec<_> = left
        .then_facts
        .iter()
        .map(|f| remap_exist_or_and_binder_ids(f, &map))
        .collect();
    let right_then: Vec<_> = right
        .then_facts
        .iter()
        .map(|f| {
            let as_fact: Fact = f.clone().into();
            as_fact.ir().0
        })
        .collect();
    left_then == right_then
}

fn param_type_ir(param_type: &ParamType) -> String {
    match param_type {
        ParamType::Set(_) => "set".to_string(),
        ParamType::NonemptySet(_) => "nonempty_set".to_string(),
        ParamType::FiniteSet(_) => "finite_set".to_string(),
        ParamType::Obj(obj) => obj.ir().0,
    }
}

fn remap_fact_binder_ids(fact: &Fact, map: &HashMap<IdentifierId, IdentifierId>) -> String {
    // Cheap IR rewrite: replace `#oldId#` binder prefixes when present in nested IR.
    let mut s = fact.ir().0;
    for (from, to) in map {
        let from_tag = format!("#{}#", from.value());
        let to_tag = format!("#{}#", to.value());
        s = s.replace(&from_tag, &to_tag);
    }
    s
}

fn remap_exist_or_and_binder_ids(
    fact: &ExistOrAndChainAtomicFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> String {
    let as_fact: Fact = fact.clone().into();
    remap_fact_binder_ids(&as_fact, map)
}

fn zorn_lemma_obligations(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    upper_bound_prop_name: &AtomicName,
    line_file: &LineFile,
) -> Vec<Fact> {
    vec![
        IsNonemptySetFact {
            fact_id: runtime.ids.allocate_fact_id(),
            set: set.clone(),
            line_file: Some(line_file.clone()),
        }
        .into(),
        zorn_reflexive_fact(runtime, set, prop_name, line_file),
        zorn_transitive_fact(runtime, set, prop_name, line_file),
        zorn_antisymmetric_fact(runtime, set, prop_name, line_file),
        zorn_chain_upper_bound_fact(runtime, set, prop_name, upper_bound_prop_name, line_file),
    ]
}

fn zorn_reflexive_fact(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = fresh_bound_name(runtime, "_zorn_rx");
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(normal_prop_fact(
            runtime,
            prop_name,
            vec![x_obj.clone(), x_obj],
            line_file,
        ))],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_transitive_fact(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = fresh_bound_name(runtime, "_zorn_tx");
    let y = fresh_bound_name(runtime, "_zorn_ty");
    let z = fresh_bound_name(runtime, "_zorn_tz");
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let y_obj = Obj::Identifier(IdentifierObj::from_bound_name(&y));
    let z_obj = Obj::Identifier(IdentifierObj::from_bound_name(&z));
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x, y, z],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![
            normal_prop_fact(
                runtime,
                prop_name,
                vec![x_obj.clone(), y_obj.clone()],
                line_file,
            )
            .into(),
            normal_prop_fact(
                runtime,
                prop_name,
                vec![y_obj, z_obj.clone()],
                line_file,
            )
            .into(),
        ],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(normal_prop_fact(
            runtime,
            prop_name,
            vec![x_obj, z_obj],
            line_file,
        ))],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_antisymmetric_fact(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = fresh_bound_name(runtime, "_zorn_ax");
    let y = fresh_bound_name(runtime, "_zorn_ay");
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let y_obj = Obj::Identifier(IdentifierObj::from_bound_name(&y));
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x, y],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![
            normal_prop_fact(
                runtime,
                prop_name,
                vec![x_obj.clone(), y_obj.clone()],
                line_file,
            )
            .into(),
            normal_prop_fact(
                runtime,
                prop_name,
                vec![y_obj.clone(), x_obj.clone()],
                line_file,
            )
            .into(),
        ],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(
            EqualFact {
                fact_id: runtime.ids.allocate_fact_id(),
                left: x_obj,
                right: y_obj,
                line_file: Some(line_file.clone()),
            }
            .into(),
        )],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_chain_upper_bound_fact(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    upper_bound_prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let c = fresh_bound_name(runtime, "_zorn_chain");
    let c_obj = Obj::Identifier(IdentifierObj::from_bound_name(&c));
    let chain_total = zorn_chain_total_fact(runtime, &c_obj, prop_name, line_file);
    let upper_bound = zorn_upper_bound_exist_fact(runtime, set, &c_obj, upper_bound_prop_name, line_file);
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![c],
                param_type: ParamType::Obj(Obj::PowerSet(PowerSet {
                    set: Box::new(set.clone()),
                })),
            }],
        },
        dom_facts: vec![chain_total],
        then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(upper_bound)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_chain_total_fact(
    runtime: &mut Runtime,
    chain: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = fresh_bound_name(runtime, "_zorn_cx");
    let y = fresh_bound_name(runtime, "_zorn_cy");
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let y_obj = Obj::Identifier(IdentifierObj::from_bound_name(&y));
    let left = AndChainAtomicFact::AtomicFact(normal_prop_fact(
        runtime,
        prop_name,
        vec![x_obj.clone(), y_obj.clone()],
        line_file,
    ));
    let right = AndChainAtomicFact::AtomicFact(normal_prop_fact(
        runtime,
        prop_name,
        vec![y_obj, x_obj],
        line_file,
    ));
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x, y],
                param_type: ParamType::Obj(chain.clone()),
            }],
        },
        dom_facts: vec![],
        then_facts: vec![ExistOrAndChainAtomicFact::OrFact(OrFact {
            fact_id: runtime.ids.allocate_fact_id(),
            facts: vec![left, right],
            line_file: Some(line_file.clone()),
        })],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_upper_bound_exist_fact(
    runtime: &mut Runtime,
    set: &Obj,
    chain: &Obj,
    upper_bound_prop_name: &AtomicName,
    line_file: &LineFile,
) -> PlainExistFact {
    let u = fresh_bound_name(runtime, "_zorn_ub");
    let u_obj = Obj::Identifier(IdentifierObj::from_bound_name(&u));
    PlainExistFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![u],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        facts: vec![QuantifierFreeFact::AtomicFact(normal_prop_fact(
            runtime,
            upper_bound_prop_name,
            vec![chain.clone(), u_obj],
            line_file,
        ))],
        line_file: Some(line_file.clone()),
    }
}

fn zorn_upper_bound_forall_fact(
    runtime: &mut Runtime,
    chain: &Obj,
    upper: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> ForallFact {
    let x = fresh_bound_name(runtime, "_zorn_ubx");
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x],
                param_type: ParamType::Obj(chain.clone()),
            }],
        },
        dom_facts: vec![],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(normal_prop_fact(
            runtime,
            prop_name,
            vec![x_obj, upper.clone()],
            line_file,
        ))],
        line_file: Some(line_file.clone()),
    }
}

fn zorn_lemma_maximal_fact(
    runtime: &mut Runtime,
    set: &Obj,
    maximal_prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let m = fresh_bound_name(runtime, "_zorn_max");
    let m_obj = Obj::Identifier(IdentifierObj::from_bound_name(&m));
    Fact::ExistFact(PlainExistFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![m],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        facts: vec![QuantifierFreeFact::AtomicFact(normal_prop_fact(
            runtime,
            maximal_prop_name,
            vec![m_obj],
            line_file,
        ))],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_maximal_forall_fact(
    runtime: &mut Runtime,
    set: &Obj,
    maximal: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> ForallFact {
    let x = fresh_bound_name(runtime, "_zorn_mx");
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![normal_prop_fact(
            runtime,
            prop_name,
            vec![maximal.clone(), x_obj.clone()],
            line_file,
        )
        .into()],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(
            EqualFact {
                fact_id: runtime.ids.allocate_fact_id(),
                left: x_obj,
                right: maximal.clone(),
                line_file: Some(line_file.clone()),
            }
            .into(),
        )],
        line_file: Some(line_file.clone()),
    }
}

fn normal_prop_fact(
    runtime: &mut Runtime,
    prop_name: &AtomicName,
    body: Vec<Obj>,
    line_file: &LineFile,
) -> AtomicFact {
    NormalAtomicFact {
        fact_id: runtime.ids.allocate_fact_id(),
        predicate: prop_name.clone(),
        body,
        line_file: Some(line_file.clone()),
    }
    .into()
}

fn user_defined_prop_arity(runtime: &Runtime, prop_name: &str) -> Option<usize> {
    if let Some(definition) = runtime.def_abstract_prop_visible_in_stack(prop_name) {
        return Some(definition.params.len());
    }
    if let Some(definition) = runtime.def_prop_visible_in_stack(prop_name) {
        return Some(typed_param_count(&definition.typed_parameters));
    }
    None
}

fn typed_param_count(list: &TypedParameterList) -> usize {
    list.groups.iter().map(|g| g.params.len()).sum()
}

fn typed_params_to_arg_map(
    list: &TypedParameterList,
    args: &[Obj],
) -> Result<HashMap<IdentifierId, Obj>, String> {
    let ids = list.ordered_param_ids();
    if ids.len() != args.len() {
        return Err(format!(
            "by zorn_lemma: expected {} prop argument(s), got {}",
            ids.len(),
            args.len()
        ));
    }
    let mut map = HashMap::new();
    for (id, arg) in ids.into_iter().zip(args.iter()) {
        map.insert(id, arg.clone());
    }
    Ok(map)
}

fn fresh_bound_name(runtime: &mut Runtime, prefix: &str) -> BoundName {
    let id = runtime.ids.allocate_identifier_id();
    BoundName::new(id, format!("{prefix}{}", id.value()))
}

fn fresh_bound_obj(runtime: &mut Runtime, prefix: &str) -> Obj {
    let bound = fresh_bound_name(runtime, prefix);
    Obj::Identifier(IdentifierObj::from_bound_name(&bound))
}
