//! Remap GlobalIds deltas + `global_mod_id` path table on a `DefinitionMemory`.

use super::def_prop_codec::KbCodecError;
use super::manifest::{GlobalIdsDeltas, GlobalIdsSnapshot};
use crate::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, QuantifierFreeFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{
    AnonymousFn, ArithmeticOperator, FnSet, FunctionSpace, IdentifierObj, Obj,
};
use crate::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::ast::stmt::{
    AxiomStmt, DefAbstractPropStmt, DefPropStmt, DefStructStmt, DefThmStmt, HaveFnEqualStmt,
    HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt, LetObjStmt, StructFieldDef,
};
use crate::exec_env::exec_env::DefinitionMemory;
use crate::exec_env::StoredIdentifierDefinition;
use crate::runtime::runtime_ids::{FactId, IdentifierId};
use std::collections::HashMap;
use std::rc::Rc;

/// Remap plan for one mounted module product.
pub struct RemapPlan {
    pub deltas: GlobalIdsDeltas,
    /// old `global_mod_id` → new `global_mod_id` for this session.
    pub old_mod_id_to_new: HashMap<u64, u64>,
}

impl RemapPlan {
    pub fn new(deltas: GlobalIdsDeltas, old_mod_id_to_new: HashMap<u64, u64>) -> Self {
        Self {
            deltas,
            old_mod_id_to_new,
        }
    }

    /// Build deltas from cached enter watermark vs caller's current counters.
    pub fn from_enter_and_now(
        enter: &GlobalIdsSnapshot,
        now: &GlobalIdsSnapshot,
        old_mod_id_to_new: HashMap<u64, u64>,
    ) -> Self {
        Self::new(
            GlobalIdsDeltas::from_enter_and_now(enter, now),
            old_mod_id_to_new,
        )
    }
}

pub fn remap_definition_memory(
    defs: &mut DefinitionMemory,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    for entry in defs.identifiers.values_mut() {
        remap_stored_identifier(entry, plan)?;
    }
    for stmt in defs.predicate_definitions.values_mut() {
        remap_def_prop(stmt, plan)?;
    }
    for stmt in defs.abstract_predicate_definitions.values_mut() {
        remap_def_abstract_prop(stmt, plan)?;
    }
    for stmt in defs.structure_definitions.values_mut() {
        remap_def_struct(stmt, plan)?;
    }
    for stmt in defs.theorem_definitions.values_mut() {
        remap_def_thm(stmt, plan)?;
    }
    for stmt in defs.axiom_definitions.values_mut() {
        remap_axiom(stmt, plan)?;
    }
    Ok(())
}

fn remap_stored_identifier(
    entry: &mut StoredIdentifierDefinition,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    match entry {
        StoredIdentifierDefinition::LetObj((_, stmt)) => {
            let mut owned = (**stmt).clone();
            remap_let_obj(&mut owned, plan)?;
            *stmt = Rc::new(owned);
        }
        StoredIdentifierDefinition::HaveObjEqual((_, stmt)) => {
            let mut owned = (**stmt).clone();
            remap_have_obj_equal(&mut owned, plan)?;
            *stmt = Rc::new(owned);
        }
        StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((_, stmt)) => {
            let mut owned = (**stmt).clone();
            remap_have_obj_in(&mut owned, plan)?;
            *stmt = Rc::new(owned);
        }
        StoredIdentifierDefinition::HaveFnEqual((_, stmt)) => {
            let mut owned = (**stmt).clone();
            remap_have_fn_equal(&mut owned, plan)?;
            *stmt = Rc::new(owned);
        }
        other => {
            return Err(KbCodecError::Unsupported(format!(
                "remap StoredIdentifierDefinition `{other:?}`"
            )));
        }
    }
    Ok(())
}

fn remap_let_obj(stmt: &mut LetObjStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_bound_name(&mut stmt.name, plan);
    remap_obj(&mut stmt.value, plan)?;
    Ok(())
}

fn remap_have_obj_equal(stmt: &mut HaveObjEqualStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_typed_parameter_list(&mut stmt.param_def, plan)?;
    for obj in &mut stmt.objs_equal_to {
        remap_obj(obj, plan)?;
    }
    Ok(())
}

fn remap_have_obj_in(
    stmt: &mut HaveObjInNonemptySetOrParamTypeStmt,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    remap_typed_parameter_list(&mut stmt.param_def, plan)?;
    Ok(())
}

fn remap_have_fn_equal(stmt: &mut HaveFnEqualStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_bound_name(&mut stmt.name, plan);
    remap_anonymous_fn(&mut stmt.equal_to_anonymous_fn, plan)?;
    Ok(())
}

fn remap_def_prop(stmt: &mut DefPropStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_typed_parameter_list(&mut stmt.typed_parameters, plan)?;
    for fact in &mut stmt.iff_facts {
        remap_fact(fact, plan)?;
    }
    Ok(())
}

fn remap_def_abstract_prop(
    _stmt: &mut DefAbstractPropStmt,
    _plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    Ok(())
}

fn remap_def_struct(stmt: &mut DefStructStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    if let Some((params, dom)) = &mut stmt.param_def_with_dom {
        remap_typed_parameter_list(params, plan)?;
        for fact in dom {
            remap_quantifier_free_fact(fact, plan)?;
        }
    }
    for field in &mut stmt.fields {
        remap_struct_field(field, plan)?;
    }
    for fact in &mut stmt.equivalent_facts {
        remap_fact(fact, plan)?;
    }
    Ok(())
}

fn remap_struct_field(field: &mut StructFieldDef, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_bound_name(&mut field.binding, plan);
    remap_obj(&mut field.field_type, plan)?;
    Ok(())
}

fn remap_def_thm(stmt: &mut DefThmStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    if !stmt.prove_process.is_empty() {
        return Err(KbCodecError::Unsupported(
            "remap def_thm with non-empty prove_process".into(),
        ));
    }
    remap_fact(&mut stmt.fact, plan)?;
    Ok(())
}

fn remap_axiom(stmt: &mut AxiomStmt, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_forall_fact(&mut stmt.forall_fact, plan)?;
    Ok(())
}

fn remap_typed_parameter_list(
    list: &mut TypedParameterList,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    for group in &mut list.groups {
        remap_typed_parameter_group(group, plan)?;
    }
    Ok(())
}

fn remap_typed_parameter_group(
    group: &mut TypedParameterGroup,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    for p in &mut group.params {
        remap_bound_name(p, plan);
    }
    match &mut group.param_type {
        ParamType::Obj(obj) => remap_obj(obj, plan)?,
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {}
    }
    Ok(())
}

fn remap_set_bound_parameter_list(
    list: &mut SetBoundParameterList,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    for group in &mut list.groups {
        remap_set_bound_parameter_group(group, plan)?;
    }
    Ok(())
}

fn remap_set_bound_parameter_group(
    group: &mut SetBoundParameterGroup,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    for p in &mut group.params {
        remap_bound_name(p, plan);
    }
    remap_obj(group.param_type.as_mut(), plan)?;
    Ok(())
}

fn remap_bound_name(name: &mut BoundName, plan: &RemapPlan) {
    name.id = IdentifierId::new(name.id.value() + plan.deltas.identifier_delta);
}

fn remap_fact_id(id: FactId, plan: &RemapPlan) -> FactId {
    FactId::new(id.value() + plan.deltas.fact_delta)
}

fn remap_mod_id(old: usize, plan: &RemapPlan) -> Result<usize, KbCodecError> {
    match plan.old_mod_id_to_new.get(&(old as u64)) {
        Some(new_id) => Ok(*new_id as usize),
        None => Err(KbCodecError::Shape(format!(
            "remap: unknown old global_mod_id `{old}`"
        ))),
    }
}

fn remap_obj(obj: &mut Obj, plan: &RemapPlan) -> Result<(), KbCodecError> {
    match obj {
        Obj::Identifier(id) => remap_identifier_obj(id, plan),
        Obj::Literal(_) | Obj::StandardSet(_) => Ok(()),
        Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) => remap_fn_set(fn_set, plan),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => remap_anonymous_fn(anon, plan),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) => {
            remap_obj(add.left.as_mut(), plan)?;
            remap_obj(add.right.as_mut(), plan)?;
            Ok(())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) => {
            remap_obj(sub.left.as_mut(), plan)?;
            remap_obj(sub.right.as_mut(), plan)?;
            Ok(())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) => {
            remap_obj(mul.left.as_mut(), plan)?;
            remap_obj(mul.right.as_mut(), plan)?;
            Ok(())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => {
            remap_obj(div.left.as_mut(), plan)?;
            remap_obj(div.right.as_mut(), plan)?;
            Ok(())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => {
            remap_obj(neg.arg.as_mut(), plan)?;
            Ok(())
        }
        other => Err(KbCodecError::Unsupported(format!(
            "remap Obj `{other:?}` (kb remap subset)"
        ))),
    }
}

fn remap_identifier_obj(id: &mut IdentifierObj, plan: &RemapPlan) -> Result<(), KbCodecError> {
    match id {
        IdentifierObj::Plain { id, .. } => {
            *id = IdentifierId::new(id.value() + plan.deltas.identifier_delta);
            Ok(())
        }
        IdentifierObj::WithExportFileId { .. } => Ok(()),
        IdentifierObj::WithModAndExportFileId {
            global_mod_id, ..
        } => {
            *global_mod_id = remap_mod_id(*global_mod_id, plan)?;
            Ok(())
        }
    }
}

fn remap_fn_set(fn_set: &mut FnSet, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_set_bound_parameter_list(&mut fn_set.set_bound_parameters, plan)?;
    for fact in &mut fn_set.dom_facts {
        remap_quantifier_free_fact(fact, plan)?;
    }
    remap_obj(fn_set.ret_set.as_mut(), plan)?;
    Ok(())
}

fn remap_anonymous_fn(anon: &mut AnonymousFn, plan: &RemapPlan) -> Result<(), KbCodecError> {
    remap_fn_set(&mut anon.body, plan)?;
    remap_obj(anon.equal_to.as_mut(), plan)?;
    Ok(())
}

fn remap_fact(fact: &mut Fact, plan: &RemapPlan) -> Result<(), KbCodecError> {
    match fact {
        Fact::AtomicFact(atomic) => remap_atomic_fact(atomic, plan),
        Fact::ForallFact(forall) => remap_forall_fact(forall, plan),
        other => Err(KbCodecError::Unsupported(format!(
            "remap Fact `{other:?}`"
        ))),
    }
}

fn remap_quantifier_free_fact(
    fact: &mut QuantifierFreeFact,
    plan: &RemapPlan,
) -> Result<(), KbCodecError> {
    match fact {
        QuantifierFreeFact::AtomicFact(atomic) => remap_atomic_fact(atomic, plan),
        other => Err(KbCodecError::Unsupported(format!(
            "remap QuantifierFreeFact `{other:?}`"
        ))),
    }
}

fn remap_forall_fact(forall: &mut ForallFact, plan: &RemapPlan) -> Result<(), KbCodecError> {
    forall.fact_id = remap_fact_id(forall.fact_id, plan);
    remap_typed_parameter_list(&mut forall.typed_parameters, plan)?;
    for fact in &mut forall.dom_facts {
        remap_fact(fact, plan)?;
    }
    for then in &mut forall.then_facts {
        match then {
            ExistOrAndChainAtomicFact::AtomicFact(atomic) => remap_atomic_fact(atomic, plan)?,
            other => {
                return Err(KbCodecError::Unsupported(format!(
                    "remap ExistOrAndChainAtomicFact `{other:?}`"
                )));
            }
        }
    }
    Ok(())
}

fn remap_atomic_fact(atomic: &mut AtomicFact, plan: &RemapPlan) -> Result<(), KbCodecError> {
    match atomic {
        AtomicFact::GreaterFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::LessFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::GreaterEqualFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::LessEqualFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::EqualFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::NotGreaterFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::NotLessFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::NotGreaterEqualFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::NotLessEqualFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::NotEqualFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.left, plan)?;
            remap_obj(&mut f.right, plan)?;
        }
        AtomicFact::InFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.element, plan)?;
            remap_obj(&mut f.set, plan)?;
        }
        AtomicFact::NotInFact(f) => {
            f.fact_id = remap_fact_id(f.fact_id, plan);
            remap_obj(&mut f.element, plan)?;
            remap_obj(&mut f.set, plan)?;
        }
        other => {
            return Err(KbCodecError::Unsupported(format!(
                "remap AtomicFact `{other:?}`"
            )));
        }
    }
    Ok(())
}
