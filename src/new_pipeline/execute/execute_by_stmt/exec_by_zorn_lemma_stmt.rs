use super::helper::{
    proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ExecByStmtResult, ExecByZornLemmaStmtFailed, ExecByZornLemmaStmtResult,
    ExecByZornLemmaStmtSuccess,
};
use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, IsNonemptySetFact,
    NormalAtomicFact, OrFact, PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj, PowerSet, SetOperator};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::ast::stmt::{ByZornLemmaStmt, DefPropStmt};
use crate::new_pipeline::parse::prop_registration_shape::plain_prop_name;
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

    if let Err(msg) = validate_zorn_props(runtime, stmt) {
        return Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Failed(
            ExecByZornLemmaStmtFailed::PropInterface(msg),
        )));
    }

    let obligations = zorn_obligations(
        runtime,
        &stmt.set,
        &stmt.prop_name,
        &stmt.upper_bound_prop_name,
        &stmt.line_file,
    );

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof_steps = match run_fact_only_proof_steps(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => return Ok(Err(ExecByZornLemmaStmtFailed::ProofBody(failed))),
        };
        let mut obligation_proofs = Vec::with_capacity(obligations.len());
        for (index, obligation) in obligations.iter().enumerate() {
            let proof = verify_goal_fact(rt, obligation)?;
            if proof.is_failed() {
                return Ok(Err(ExecByZornLemmaStmtFailed::Obligation {
                    index,
                    result: proof,
                }));
            }
            let _ = store_goal_fact(rt, obligation)?;
            obligation_proofs.push(proof);
        }
        Ok(Ok((proof_steps, obligation_proofs)))
    })?;

    let (proof_steps, obligation_proofs) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::ZornLemma(ExecByZornLemmaStmtResult::Failed(
                failed,
            )));
        }
    };

    // Trusted Zorn step: nonempty poset with chain upper bounds has a maximal element.
    // Example stores: exist m S st { $is_maximal(m) }.
    let maximal_fact =
        zorn_maximal_exist(runtime, &stmt.set, &stmt.maximal_prop_name, &stmt.line_file);
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
            obligations: obligation_proofs,
            local_env,
            stored,
        },
    )))
}

fn validate_zorn_props(runtime: &Runtime, stmt: &ByZornLemmaStmt) -> Result<(), String> {
    let relation = plain_prop_name(&stmt.prop_name);
    let Some(relation_def) = runtime.def_prop_visible_in_stack(relation) else {
        return Err(format!(
            "by zorn_lemma: relation `{relation}` must be a user-defined prop"
        ));
    };
    if prop_arity(relation_def) != 2 {
        return Err(format!(
            "by zorn_lemma: relation `{relation}` must be a binary user-defined prop"
        ));
    }

    let ub_name = plain_prop_name(&stmt.upper_bound_prop_name);
    let Some(ub_def) = runtime.def_prop_visible_in_stack(ub_name) else {
        return Err(format!(
            "by zorn_lemma: upper-bound `{ub_name}` must be a concrete named prop"
        ));
    };
    if prop_arity(ub_def) != 2 {
        return Err(format!(
            "by zorn_lemma: upper-bound `{ub_name}` must have two parameters `(c power_set(S), u S)`"
        ));
    }
    let expected_ub = [
        Obj::SetOperator(SetOperator::PowerSet(PowerSet {
            set: Box::new(stmt.set.clone()),
        })),
        stmt.set.clone(),
    ];
    if !prop_header_types_match(ub_def, &expected_ub) {
        return Err(format!(
            "by zorn_lemma: upper-bound `{ub_name}` must bind `(c power_set(S), u S)`"
        ));
    }
    if !matches!(ub_def.iff_facts.as_slice(), [Fact::ForallFact(_)]) {
        return Err(format!(
            "by zorn_lemma: upper-bound `{ub_name}` must have exactly a forall definition `forall x c: ${}(x, u)`",
            plain_prop_name(&stmt.prop_name)
        ));
    }

    let max_name = plain_prop_name(&stmt.maximal_prop_name);
    let Some(max_def) = runtime.def_prop_visible_in_stack(max_name) else {
        return Err(format!(
            "by zorn_lemma: maximality `{max_name}` must be a concrete named prop"
        ));
    };
    if prop_arity(max_def) != 1 {
        return Err(format!(
            "by zorn_lemma: maximality `{max_name}` must have one parameter `(m S)`"
        ));
    }
    if !prop_header_types_match(max_def, &[stmt.set.clone()]) {
        return Err(format!(
            "by zorn_lemma: maximality `{max_name}` must bind `(m S)`"
        ));
    }
    if !matches!(max_def.iff_facts.as_slice(), [Fact::ForallFact(_)]) {
        return Err(format!(
            "by zorn_lemma: maximality `{max_name}` must have exactly a forall definition `forall x S: ${}(m, x) => x = m`",
            plain_prop_name(&stmt.prop_name)
        ));
    }
    Ok(())
}

fn prop_arity(definition: &DefPropStmt) -> usize {
    definition
        .typed_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum()
}

fn prop_header_types_match(definition: &DefPropStmt, expected: &[Obj]) -> bool {
    let mut actual = Vec::new();
    for group in &definition.typed_parameters.groups {
        for _ in &group.params {
            match &group.param_type {
                ParamType::Obj(obj) => actual.push(obj.clone()),
                _ => return false,
            }
        }
    }
    actual == expected
}

fn zorn_obligations(
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
        zorn_reflexive(runtime, set, prop_name, line_file),
        zorn_transitive(runtime, set, prop_name, line_file),
        zorn_antisymmetric(runtime, set, prop_name, line_file),
        zorn_chain_upper_bound(runtime, set, prop_name, upper_bound_prop_name, line_file),
    ]
}

fn zorn_reflexive(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = runtime.fresh_internal_param();
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let atom = prop_atom(runtime, prop_name, vec![x_obj.clone(), x_obj], line_file);
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(atom)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_transitive(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = runtime.fresh_internal_param();
    let y = runtime.fresh_internal_param();
    let z = runtime.fresh_internal_param();
    let xo = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let yo = Obj::Identifier(IdentifierObj::from_bound_name(&y));
    let zo = Obj::Identifier(IdentifierObj::from_bound_name(&z));
    let xy = prop_atom(runtime, prop_name, vec![xo.clone(), yo.clone()], line_file);
    let yz = prop_atom(runtime, prop_name, vec![yo, zo.clone()], line_file);
    let xz = prop_atom(runtime, prop_name, vec![xo, zo], line_file);
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x, y, z],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![xy.into(), yz.into()],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(xz)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_antisymmetric(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = runtime.fresh_internal_param();
    let y = runtime.fresh_internal_param();
    let xo = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let yo = Obj::Identifier(IdentifierObj::from_bound_name(&y));
    let xy = prop_atom(runtime, prop_name, vec![xo.clone(), yo.clone()], line_file);
    let yx = prop_atom(runtime, prop_name, vec![yo.clone(), xo.clone()], line_file);
    let eq: AtomicFact = EqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left: xo,
        right: yo,
        line_file: Some(line_file.clone()),
    }
    .into();
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x, y],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        dom_facts: vec![xy.into(), yx.into()],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(eq)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_chain_upper_bound(
    runtime: &mut Runtime,
    set: &Obj,
    prop_name: &AtomicName,
    upper_bound_prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let c = runtime.fresh_internal_param();
    let c_obj = Obj::Identifier(IdentifierObj::from_bound_name(&c));
    let power = Obj::SetOperator(SetOperator::PowerSet(PowerSet {
        set: Box::new(set.clone()),
    }));
    let chain_total = zorn_chain_total(runtime, &c_obj, prop_name, line_file);
    let upper = zorn_upper_exist(runtime, set, &c_obj, upper_bound_prop_name, line_file);
    let Fact::ExistFact(plain) = upper else {
        unreachable!("upper bound witness is an exist fact");
    };
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![c],
                param_type: ParamType::Obj(power),
            }],
        },
        dom_facts: vec![chain_total],
        then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(plain)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_chain_total(
    runtime: &mut Runtime,
    chain: &Obj,
    prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let x = runtime.fresh_internal_param();
    let y = runtime.fresh_internal_param();
    let xo = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let yo = Obj::Identifier(IdentifierObj::from_bound_name(&y));
    let left = prop_atom(runtime, prop_name, vec![xo.clone(), yo.clone()], line_file);
    let right = prop_atom(runtime, prop_name, vec![yo, xo], line_file);
    let or_fact = OrFact {
        fact_id: runtime.ids.allocate_fact_id(),
        facts: vec![
            AndChainAtomicFact::AtomicFact(left),
            AndChainAtomicFact::AtomicFact(right),
        ],
        line_file: Some(line_file.clone()),
    };
    Fact::ForallFact(ForallFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x, y],
                param_type: ParamType::Obj(chain.clone()),
            }],
        },
        dom_facts: vec![],
        then_facts: vec![ExistOrAndChainAtomicFact::OrFact(or_fact)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_upper_exist(
    runtime: &mut Runtime,
    set: &Obj,
    chain: &Obj,
    upper_bound_prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let u = runtime.fresh_internal_param();
    let u_obj = Obj::Identifier(IdentifierObj::from_bound_name(&u));
    let atom = prop_atom(
        runtime,
        upper_bound_prop_name,
        vec![chain.clone(), u_obj],
        line_file,
    );
    Fact::ExistFact(PlainExistFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![u],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        facts: vec![QuantifierFreeFact::AtomicFact(atom)],
        line_file: Some(line_file.clone()),
    })
}

fn zorn_maximal_exist(
    runtime: &mut Runtime,
    set: &Obj,
    maximal_prop_name: &AtomicName,
    line_file: &LineFile,
) -> Fact {
    let m = runtime.fresh_internal_param();
    let m_obj = Obj::Identifier(IdentifierObj::from_bound_name(&m));
    let atom = prop_atom(runtime, maximal_prop_name, vec![m_obj], line_file);
    Fact::ExistFact(PlainExistFact {
        fact_id: runtime.ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![m],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        facts: vec![QuantifierFreeFact::AtomicFact(atom)],
        line_file: Some(line_file.clone()),
    })
}

fn prop_atom(
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
