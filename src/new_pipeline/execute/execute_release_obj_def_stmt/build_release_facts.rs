//! Build the facts that `release obj def I` stores for one StoredIdentifierDefinition.

use crate::new_pipeline::ast::fact::{
    and_chain_as_fact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact,
    IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, IdentifierObj, Obj, StructObj};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::{
    HaveFnByForallExistUniqueStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt,
    HaveObjByExistFactsStmt, HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt, LetObjStmt,
    TrustHaveStmt,
};
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::execute::execute_have_fn_by_induc_stmt::flatten_induc_to_case_by_case;
use crate::new_pipeline::execute::execute_have_fn_equal_case_by_case_stmt::set_bound_to_typed;
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;
use std::collections::HashMap;
use std::rc::Rc;

use super::exec_release_obj_def_stmt::ReleaseObjDefByKind;

pub(super) enum BuildReleaseFactsFailed {
    NameNotInDefinition,
    ParamTypeNotReleasable,
    FlattenInduc(String),
    Instantiate(String),
}

pub(super) struct BuiltReleaseFacts {
    pub kind: ReleaseObjDefByKind,
    pub facts: Vec<Fact>,
    pub defined_as_struct: Option<(Obj, StructObj)>,
}

impl Runtime {
    pub(super) fn build_release_obj_def_facts(
        &mut self,
        surface: &IdentifierObj,
        def: &StoredIdentifierDefinition,
    ) -> RuntimeResult<Result<BuiltReleaseFacts, BuildReleaseFactsFailed>> {
        let plain = plain_name(surface);
        match def {
            StoredIdentifierDefinition::ParamType(_) => Ok(Err(
                BuildReleaseFactsFailed::ParamTypeNotReleasable,
            )),
            StoredIdentifierDefinition::LetObj((_, stmt)) => {
                Ok(Ok(build_let_obj(self, surface, stmt)))
            }
            StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((_, stmt)) => {
                Ok(build_have_in_nonempty(self, surface, plain, stmt))
            }
            StoredIdentifierDefinition::HaveObjEqual((_, stmt)) => {
                Ok(build_have_obj_equal(self, surface, plain, stmt))
            }
            StoredIdentifierDefinition::HaveObjByExistFacts((_, stmt)) => {
                build_have_by_exist(self, surface, plain, stmt)
            }
            StoredIdentifierDefinition::TrustHave((_, stmt)) => {
                build_trust_have(self, surface, plain, stmt)
            }
            StoredIdentifierDefinition::HaveFnEqual((_, stmt)) => {
                Ok(Ok(build_have_fn_equal(self, surface, stmt)))
            }
            StoredIdentifierDefinition::HaveFnEqualCaseByCase((_, stmt)) => {
                Ok(Ok(build_have_fn_case_by_case(self, surface, stmt.as_ref())))
            }
            StoredIdentifierDefinition::HaveFnByForallExistUnique((_, stmt)) => {
                build_have_fn_by_forall_exist_unique(self, surface, stmt.as_ref())
            }
            StoredIdentifierDefinition::HaveFnByInduc((_, stmt)) => {
                match flatten_induc_to_case_by_case(self, stmt) {
                    Ok(flat) => Ok(Ok(build_have_fn_case_by_case(self, surface, &flat))),
                    Err(msg) => Ok(Err(BuildReleaseFactsFailed::FlattenInduc(msg))),
                }
            }
        }
    }

    pub(super) fn store_built_release_facts(
        &mut self,
        built: &BuiltReleaseFacts,
    ) -> RuntimeResult<Vec<StoreFactAndInferResult>> {
        let mut out = Vec::with_capacity(built.facts.len());
        for fact in &built.facts {
            if let Some((element, struct_obj)) = &built.defined_as_struct {
                if let Fact::AtomicFact(AtomicFact::InFact(in_fact)) = fact {
                    if &in_fact.element == element {
                        self.record_defined_as_struct(element, struct_obj.clone(), in_fact.fact_id);
                    }
                }
            }
            out.push(self.store_fact_and_infer(fact)?);
        }
        Ok(out)
    }
}

fn build_let_obj(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    stmt: &Rc<LetObjStmt>,
) -> BuiltReleaseFacts {
    let equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left: Obj::Identifier(surface.clone()),
        right: stmt.value.clone(),
        line_file: Some(stmt.line_file.clone()),
    }));
    BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::LetObj { equal: equal.clone() },
        facts: vec![equal],
        defined_as_struct: None,
    }
}

fn build_have_in_nonempty(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    plain: &str,
    stmt: &Rc<HaveObjInNonemptySetOrParamTypeStmt>,
) -> Result<BuiltReleaseFacts, BuildReleaseFactsFailed> {
    let Some(param_type) = param_type_for_name(&stmt.param_def, plain) else {
        return Err(BuildReleaseFactsFailed::NameNotInDefinition);
    };
    let (type_fact, defined_as_struct) =
        type_fact_for_surface(runtime, surface, param_type, &stmt.line_file);
    Ok(BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::HaveObjInNonemptySetOrParamType {
            type_fact: type_fact.clone(),
        },
        facts: vec![type_fact],
        defined_as_struct,
    })
}

fn build_have_obj_equal(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    plain: &str,
    stmt: &Rc<HaveObjEqualStmt>,
) -> Result<BuiltReleaseFacts, BuildReleaseFactsFailed> {
    let Some((param_type, rhs)) = param_type_and_rhs_for_name(stmt, plain) else {
        return Err(BuildReleaseFactsFailed::NameNotInDefinition);
    };
    let (type_fact, defined_as_struct) =
        type_fact_for_surface(runtime, surface, param_type, &stmt.line_file);
    let equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left: Obj::Identifier(surface.clone()),
        right: rhs.clone(),
        line_file: Some(stmt.line_file.clone()),
    }));
    Ok(BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::HaveObjEqual {
            type_fact: type_fact.clone(),
            equal: equal.clone(),
        },
        facts: vec![type_fact, equal],
        defined_as_struct,
    })
}

fn build_have_by_exist(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    plain: &str,
    stmt: &Rc<HaveObjByExistFactsStmt>,
) -> RuntimeResult<Result<BuiltReleaseFacts, BuildReleaseFactsFailed>> {
    let Some(param_type) = param_type_for_name(&stmt.param_def, plain) else {
        return Ok(Err(BuildReleaseFactsFailed::NameNotInDefinition));
    };
    let (type_fact, defined_as_struct) =
        type_fact_for_surface(runtime, surface, param_type, &stmt.line_file);
    let subst = surface_subst_for_param_list(surface, &stmt.param_def);
    let mut body_facts = Vec::new();
    for qf in &stmt.facts {
        match runtime.inst_quantifier_free_fact(qf, &subst) {
            Ok(inst) => body_facts.push(quantifier_free_fact_to_fact(inst)),
            Err(e) => {
                return Ok(Err(BuildReleaseFactsFailed::Instantiate(format!("{e}"))));
            }
        }
    }
    let mut facts = vec![type_fact.clone()];
    facts.extend(body_facts.iter().cloned());
    Ok(Ok(BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::HaveObjByExistFacts {
            type_fact,
            body_facts,
        },
        facts,
        defined_as_struct,
    }))
}

fn build_trust_have(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    plain: &str,
    stmt: &Rc<TrustHaveStmt>,
) -> RuntimeResult<Result<BuiltReleaseFacts, BuildReleaseFactsFailed>> {
    let Some(param_type) = param_type_for_name(&stmt.param_def, plain) else {
        return Ok(Err(BuildReleaseFactsFailed::NameNotInDefinition));
    };
    let (type_fact, defined_as_struct) =
        type_fact_for_surface(runtime, surface, param_type, &stmt.line_file);
    let subst = surface_subst_for_param_list(surface, &stmt.param_def);
    let mut body_facts = Vec::new();
    for fact in &stmt.facts {
        match runtime.inst_fact(fact, &subst) {
            Ok(inst) => body_facts.push(inst),
            Err(e) => {
                return Ok(Err(BuildReleaseFactsFailed::Instantiate(format!("{e}"))));
            }
        }
    }
    let mut facts = vec![type_fact.clone()];
    facts.extend(body_facts.iter().cloned());
    Ok(Ok(BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::TrustHave {
            type_fact,
            body_facts,
        },
        facts,
        defined_as_struct,
    }))
}

fn build_have_fn_equal(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    stmt: &Rc<HaveFnEqualStmt>,
) -> BuiltReleaseFacts {
    let fn_set = Obj::FnSet(stmt.equal_to_anonymous_fn.body.clone());
    let anon = Obj::AnonymousFn(stmt.equal_to_anonymous_fn.clone());
    let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
        fact_id: runtime.ids.allocate_fact_id(),
        element: Obj::Identifier(surface.clone()),
        set: fn_set,
        line_file: Some(stmt.line_file.clone()),
    }));
    let equal_to_anon = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left: Obj::Identifier(surface.clone()),
        right: anon,
        line_file: Some(stmt.line_file.clone()),
    }));
    BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::HaveFnEqual {
            membership: membership.clone(),
            equal_to_anon: equal_to_anon.clone(),
        },
        facts: vec![membership, equal_to_anon],
        defined_as_struct: None,
    }
}

fn build_have_fn_case_by_case(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    stmt: &HaveFnEqualCaseByCaseStmt,
) -> BuiltReleaseFacts {
    let fn_set = Obj::FnSet(crate::new_pipeline::ast::obj::FnSet {
        set_bound_parameters: stmt.fn_set_clause.set_bound_parameters.clone(),
        dom_facts: stmt.fn_set_clause.dom_facts.clone(),
        ret_set: Box::new(stmt.fn_set_clause.ret_set.clone()),
    });
    let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
        fact_id: runtime.ids.allocate_fact_id(),
        element: Obj::Identifier(surface.clone()),
        set: fn_set,
        line_file: Some(stmt.line_file.clone()),
    }));

    let typed = set_bound_to_typed(&stmt.fn_set_clause.set_bound_parameters);
    let mut args = Vec::new();
    for group in &typed.groups {
        for param in &group.params {
            args.push(Box::new(Obj::Identifier(IdentifierObj::from_bound_name(
                param,
            ))));
        }
    }
    let applied = Obj::FnObj(FnObj {
        head: Box::new(FnObjHead::Identifier(surface.clone())),
        body: vec![args],
    });
    let base_dom: Vec<Fact> = stmt
        .fn_set_clause
        .dom_facts
        .iter()
        .map(|d| quantifier_free_fact_to_fact(d.clone()))
        .collect();

    let mut case_foralls = Vec::new();
    for (case_fact, equal_to) in stmt.cases.iter().zip(stmt.equal_tos.iter()) {
        let mut dom_facts = base_dom.clone();
        dom_facts.push(and_chain_as_fact(case_fact));
        let equal_atomic = AtomicFact::EqualFact(EqualFact {
            fact_id: runtime.ids.allocate_fact_id(),
            left: applied.clone(),
            right: equal_to.clone(),
            line_file: Some(stmt.line_file.clone()),
        });
        case_foralls.push(Fact::ForallFact(ForallFact {
            fact_id: runtime.ids.allocate_fact_id(),
            typed_parameters: typed.clone(),
            dom_facts,
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(equal_atomic)],
            line_file: Some(stmt.line_file.clone()),
        }));
    }

    let mut facts = vec![membership.clone()];
    facts.extend(case_foralls.iter().cloned());
    BuiltReleaseFacts {
        kind: ReleaseObjDefByKind::HaveFnEqualCaseByCase {
            membership,
            case_foralls,
        },
        facts,
        defined_as_struct: None,
    }
}

fn build_have_fn_by_forall_exist_unique(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    stmt: &HaveFnByForallExistUniqueStmt,
) -> RuntimeResult<Result<BuiltReleaseFacts, BuildReleaseFactsFailed>> {
    match runtime.build_have_fn_by_forall_exist_unique_facts_for_surface(surface, stmt)? {
        Ok((membership, property_forall, uniqueness_forall)) => {
            let facts = vec![
                membership.clone(),
                property_forall.clone(),
                uniqueness_forall.clone(),
            ];
            Ok(Ok(BuiltReleaseFacts {
                kind: ReleaseObjDefByKind::HaveFnByForallExistUnique {
                    membership,
                    property_forall,
                    uniqueness_forall,
                },
                facts,
                defined_as_struct: None,
            }))
        }
        Err(msg) => Ok(Err(BuildReleaseFactsFailed::Instantiate(msg))),
    }
}

fn type_fact_for_surface(
    runtime: &mut Runtime,
    surface: &IdentifierObj,
    param_type: &ParamType,
    line_file: &crate::new_pipeline::ast::line_file::LineFile,
) -> (Fact, Option<(Obj, StructObj)>) {
    let element = Obj::Identifier(surface.clone());
    match param_type {
        ParamType::Obj(param_set) => {
            let fact_id = runtime.ids.allocate_fact_id();
            let defined_as_struct = match param_set {
                Obj::StructObj(struct_obj) => Some((element.clone(), struct_obj.clone())),
                _ => None,
            };
            (
                Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id,
                    element,
                    set: param_set.clone(),
                    line_file: Some(line_file.clone()),
                })),
                defined_as_struct,
            )
        }
        ParamType::Set(_) => (
            Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                fact_id: runtime.ids.allocate_fact_id(),
                set: element,
                line_file: Some(line_file.clone()),
            })),
            None,
        ),
        ParamType::NonemptySet(_) => (
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                fact_id: runtime.ids.allocate_fact_id(),
                set: element,
                line_file: Some(line_file.clone()),
            })),
            None,
        ),
        ParamType::FiniteSet(_) => (
            Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                fact_id: runtime.ids.allocate_fact_id(),
                set: element,
                line_file: Some(line_file.clone()),
            })),
            None,
        ),
    }
}

fn param_type_for_name<'a>(
    param_def: &'a TypedParameterList,
    plain: &str,
) -> Option<&'a ParamType> {
    for group in &param_def.groups {
        for param in &group.params {
            if param.name == plain {
                return Some(&group.param_type);
            }
        }
    }
    None
}

fn param_type_and_rhs_for_name<'a>(
    stmt: &'a HaveObjEqualStmt,
    plain: &str,
) -> Option<(&'a ParamType, &'a Obj)> {
    let mut index = 0;
    for group in &stmt.param_def.groups {
        for param in &group.params {
            if param.name == plain {
                return stmt
                    .objs_equal_to
                    .get(index)
                    .map(|rhs| (&group.param_type, rhs));
            }
            index += 1;
        }
    }
    None
}

fn surface_subst_for_param_list(
    released: &IdentifierObj,
    param_def: &TypedParameterList,
) -> HashMap<IdentifierId, Obj> {
    let released_plain = plain_name(released);
    let mut subst = HashMap::new();
    for group in &param_def.groups {
        for param in &group.params {
            let surface = if param.name == released_plain {
                released.clone()
            } else {
                match released {
                    IdentifierObj::Plain { .. } => IdentifierObj::from_bound_name(param),
                    IdentifierObj::WithExportFileId { export_file_id, .. } => {
                        IdentifierObj::with_export_file_id(*export_file_id, param.name.clone())
                    }
                    IdentifierObj::WithModAndExportFileId {
                        global_mod_id,
                        export_file_id,
                        ..
                    } => IdentifierObj::with_mod_and_export_file_id(
                        *global_mod_id,
                        *export_file_id,
                        param.name.clone(),
                    ),
                }
            };
            subst.insert(param.id, Obj::Identifier(surface));
        }
    }
    subst
}

fn plain_name(name: &IdentifierObj) -> &str {
    match name {
        IdentifierObj::Plain { name, .. }
        | IdentifierObj::WithExportFileId { name, .. }
        | IdentifierObj::WithModAndExportFileId { name, .. } => name.as_str(),
    }
}
