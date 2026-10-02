//! Struct / template / field-access object WD.

use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use super::fail_to_verify_obj_well_defined::*;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::wrap_obj_well_defined_by_def::finish_by_def;
use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::ast::obj::{
    FieldAccess, FunctionSpace, InstantiatedTemplateObj, Obj, StructAndFieldAccessObj, StructObj,
};
use crate::ast::param::ParamType;
use crate::ast::stmt::TemplateDefEnum;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // `&Name` / `&Name<args>`: known structure definition, matching arity, param WD.
    // Does not prove membership `$in &Struct`.
    // Example: after `struct Point: x R; y R`, WD of `&Point` succeeds.
    pub(super) fn verify_struct_obj_well_definedness(
        &mut self,
        value: &StructObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let plain = value.name.local_name();
        let expected_arity = {
            let Some(def) = self.def_struct_visible(&value.name) else {
                let root =
                    Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(value.clone()));
                return Ok(VerifyObjWellDefinedResult::Failed {
                    obj: root,
                    reason: FailToVerifyObjWellDefinedResult::Structish(
                        FailToVerifyStructishObjWellDefinedResult::StructObj(
                            FailToVerifyStructObjObjWellDefined(
                                FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                                    "struct `{plain}` is not defined"
                                )),
                            ),
                        ),
                    ),
                });
            };
            match &def.param_def_with_dom {
                None => 0,
                Some((params, _)) => params.ordered_param_ids().len(),
            }
        };
        if value.params.len() != expected_arity {
            let root =
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(value.clone()));
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::Structish(
                    FailToVerifyStructishObjWellDefinedResult::StructObj(
                        FailToVerifyStructObjObjWellDefined(
                            FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                                "struct `{plain}` expects {expected_arity} parameter(s), got {}",
                                value.params.len()
                            )),
                        ),
                    ),
                ),
            });
        }

        let refs: Vec<&Obj> = value.params.iter().collect();
        let stages = self.verify_objs_as_children(&refs, verify_state.clone())?;
        let root = Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(value.clone()));
        match finish_by_def(&root, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.global_ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(root.clone(), wd_id);
                }
                Ok(VerifyObjWellDefinedResult::Success(
                    ObjWellDefinedProof::ByDef {
                        obj: root,
                        proof: by_def,
                    },
                ))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: fail,
            }),
        }
    }

    // `x.y` / `x.y.z`: receiver WD, then walk `fields` on the definition-time carrier.
    // Intermediate fields (all but the last) must themselves have `&Struct` type.
    // Example: after `forall p &Point:`, WD of `p.x` succeeds.
    pub(super) fn verify_field_access_obj_well_definedness(
        &mut self,
        value: &FieldAccess,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let root =
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(value.clone()));
        if value.fields.is_empty() {
            return Ok(field_access_fail(
                root,
                "field access expects at least one field name".to_string(),
            ));
        }

        let receiver_wd =
            self.verify_obj_well_definedness(value.obj.as_ref(), verify_state.clone())?;
        if receiver_wd.is_failed() {
            return Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: FailToVerifyObjWellDefinedResult::Structish(
                    FailToVerifyStructishObjWellDefinedResult::FieldAccess(
                        FailToVerifyFieldAccessObjWellDefined(
                            FailToVerifyObjWellDefinedByDefCommon::Child {
                                obj: value.obj.as_ref().clone(),
                                child: Box::new(match receiver_wd {
                                    VerifyObjWellDefinedResult::Failed { reason, .. } => reason,
                                    VerifyObjWellDefinedResult::Success(_) => unreachable!(),
                                }),
                            },
                        ),
                    ),
                ),
            });
        }

        let Some(mut carrier) = self.resolve_definition_struct_carrier(value.obj.as_ref()) else {
            return Ok(field_access_fail(
                root,
                format!(
                    "object has no definition-time struct carrier for field `{}`",
                    value.fields.join(".")
                ),
            ));
        };

        for (index, field_name) in value.fields.iter().enumerate() {
            let plain = carrier.name.local_name().to_string();
            let Some(def) = self.def_struct_visible(&carrier.name) else {
                return Ok(field_access_fail(
                    root,
                    format!("struct `{plain}` is not defined"),
                ));
            };
            let Some(field_def) = def.fields.iter().find(|f| f.binding.name == *field_name) else {
                return Ok(field_access_fail(
                    root,
                    format!("struct `{plain}` has no field `{field_name}`"),
                ));
            };
            let is_last = index + 1 == value.fields.len();
            if is_last {
                break;
            }
            match &field_def.field_type {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(next)) => {
                    carrier = next.clone()
                }
                _ => {
                    return Ok(field_access_fail(
                        root,
                        format!("field `{field_name}` of struct `{plain}` is not a struct carrier"),
                    ));
                }
            }
        }

        let stages = ObjWellDefinedByDefCommonStages::from_children(vec![receiver_wd]);
        match finish_by_def(&root, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.global_ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(root.clone(), wd_id);
                }
                Ok(VerifyObjWellDefinedResult::Success(
                    ObjWellDefinedProof::ByDef {
                        obj: root,
                        proof: by_def,
                    },
                ))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: fail,
            }),
        }
    }

    // Definition-selected `DefaultStructView` only (exact ObjIR; not equality class).
    // Nested field access: walk all fields; result carrier is the last field's
    // type when that type is `&Struct`.
    pub(in crate::execute) fn resolve_definition_struct_carrier(
        &self,
        obj: &Obj,
    ) -> Option<StructObj> {
        if let Some(carrier) = self.defined_as_struct_visible_in_stack(obj) {
            return Some(carrier);
        }
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) = obj else {
            return None;
        };
        if access.fields.is_empty() {
            return None;
        }
        let mut carrier = self.resolve_definition_struct_carrier(access.obj.as_ref())?;
        for (index, field_name) in access.fields.iter().enumerate() {
            let def = self.def_struct_visible(&carrier.name)?;
            let field = def.fields.iter().find(|f| f.binding.name == *field_name)?;
            let is_last = index + 1 == access.fields.len();
            match &field.field_type {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(next)) => {
                    if is_last {
                        return Some(next.clone());
                    }
                    carrier = next.clone();
                }
                _ => {
                    if is_last {
                        return None;
                    }
                    return None;
                }
            }
        }
        None
    }

    pub(super) fn defined_as_struct_visible_in_stack(&self, obj: &Obj) -> Option<StructObj> {
        let key = obj.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(props) = env.special_properties.get(&key) else {
                continue;
            };
            for prop in props {
                if let SpecialProperty::DefaultStructView(fact) = prop {
                    if let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) = &fact.set {
                        return Some(carrier.clone());
                    }
                }
            }
        }
        None
    }

    // `\Name<args>`: known template, matching arity, args WD, param-type + domain obligations.
    // Surface stays InstantiatedTemplateObj (no materialization).
    // Example: after `template<S set>: have carrier_copy set = S`, WD of `\carrier_copy<R>`.
    pub(super) fn verify_instantiated_template_obj_well_definedness(
        &mut self,
        value: &InstantiatedTemplateObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let plain = value.template_name.local_name();
        let (expected_arity, param_groups, dom_facts) = {
            let Some(def) = self.def_template_visible(&value.template_name) else {
                return Ok(template_fail(
                    Obj::InstantiatedTemplateObj(value.clone()),
                    FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                        "template `{plain}` is not defined"
                    )),
                ));
            };
            (
                def.template_arg_def.ordered_param_ids().len(),
                def.template_arg_def.groups.clone(),
                def.template_arg_dom.clone(),
            )
        };
        if value.args.len() != expected_arity {
            return Ok(template_fail(
                Obj::InstantiatedTemplateObj(value.clone()),
                FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                    "template `{plain}` expects {expected_arity} argument(s), got {}",
                    value.args.len()
                )),
            ));
        }

        let mut stages = ObjWellDefinedByDefCommonStages::leaf();
        for arg in &value.args {
            let child = self.verify_obj_well_definedness(arg, verify_state.clone())?;
            let failed = child.is_failed();
            stages.child_obj_well_defined.push(child);
            if failed {
                let root = Obj::InstantiatedTemplateObj(value.clone());
                return Ok(match finish_by_def(&root, stages) {
                    Ok(_) => unreachable!(),
                    Err(fail) => VerifyObjWellDefinedResult::Failed {
                        obj: root,
                        reason: fail,
                    },
                });
            }
        }

        let param_ids = {
            let mut ids = Vec::with_capacity(expected_arity);
            for group in &param_groups {
                for param in &group.params {
                    ids.push(param.id);
                }
            }
            ids
        };
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in param_ids.iter().zip(value.args.iter()) {
            subst.insert(*id, arg.clone());
        }

        let mut arg_index = 0;
        for group in &param_groups {
            let param_type = match self.inst_param_type(&group.param_type, &subst) {
                Ok(param_type) => param_type,
                Err(_) => {
                    return Ok(template_fail(
                        Obj::InstantiatedTemplateObj(value.clone()),
                        FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                            "template `{plain}`: failed to instantiate parameter type"
                        )),
                    ));
                }
            };
            for _param in &group.params {
                let arg = &value.args[arg_index];
                let type_fact = type_fact_for_instantiated_template_arg(
                    arg.clone(),
                    &param_type,
                    self.global_ids.allocate_fact_id(),
                );
                let req = self.verify_fact(&type_fact, verify_state.clone())?;
                let failed = req.is_failed();
                stages.requirement_fact_verified.push(req);
                if failed {
                    let root = Obj::InstantiatedTemplateObj(value.clone());
                    return Ok(match finish_by_def(&root, stages) {
                        Ok(_) => unreachable!(),
                        Err(fail) => VerifyObjWellDefinedResult::Failed {
                            obj: root,
                            reason: fail,
                        },
                    });
                }
                arg_index += 1;
            }
        }

        for dom in &dom_facts {
            let instantiated = match self.inst_quantifier_free_fact(dom, &subst) {
                Ok(f) => f,
                Err(_) => {
                    return Ok(template_fail(
                        Obj::InstantiatedTemplateObj(value.clone()),
                        FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                            "template `{plain}`: failed to instantiate domain fact"
                        )),
                    ));
                }
            };
            let req =
                self.verify_required_quantifier_free_fact(instantiated, verify_state.clone())?;
            let failed = req.is_failed();
            stages.requirement_fact_verified.push(req);
            if failed {
                let root = Obj::InstantiatedTemplateObj(value.clone());
                return Ok(match finish_by_def(&root, stages) {
                    Ok(_) => unreachable!(),
                    Err(fail) => VerifyObjWellDefinedResult::Failed {
                        obj: root,
                        reason: fail,
                    },
                });
            }
        }

        let root = Obj::InstantiatedTemplateObj(value.clone());
        match finish_by_def(&root, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.global_ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(root.clone(), wd_id);
                    // Have-fn template bodies: register the surface as callable so
                    // `\T<a>(x)` reuses ordinary InFunctionSet application WD.
                    // Have-obj bodies: store `\T<a> = subst(rhs)` for definitional use.
                    self.maybe_register_instantiated_template_definitional_facts(value)?;
                }
                Ok(VerifyObjWellDefinedResult::Success(
                    ObjWellDefinedProof::ByDef {
                        obj: root,
                        proof: by_def,
                    },
                ))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed {
                obj: root,
                reason: fail,
            }),
        }
    }

    // After WD of `\Name<args>`, store definitional facts for supported bodies:
    // - have fn =: `\Name<args> $in inst(FnSet)` and `\Name<args> = inst(anon)`
    // - have fn by cases / by induc: `\Name<args> $in inst(FnSet)` (no anon equality)
    // - have =: `\Name<args> = subst(rhs)`
    // - have by replacement_axiom: `$is_set(\Name<args>)` plus intro/elim foralls
    fn maybe_register_instantiated_template_definitional_facts(
        &mut self,
        value: &InstantiatedTemplateObj,
    ) -> RuntimeResult<()> {
        let Some(def) = self.def_template_visible(&value.template_name).cloned() else {
            return Ok(());
        };
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in def
            .template_arg_def
            .ordered_param_ids()
            .into_iter()
            .zip(value.args.iter())
        {
            subst.insert(id, arg.clone());
        }
        match &def.template_def_stmt {
            TemplateDefEnum::HaveFnEqualStmt(have_fn) => {
                let Ok(anon) = self.inst_obj(
                    &Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                        have_fn.equal_to_anonymous_fn.clone(),
                    )),
                    &subst,
                ) else {
                    return Ok(());
                };
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = anon else {
                    return Ok(());
                };
                let surface = Obj::InstantiatedTemplateObj(value.clone());
                let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: surface.clone(),
                    set: Obj::FunctionSpace(FunctionSpace::FnSet(anon.body.clone())),
                    line_file: None,
                }));
                self.store_fact_and_infer(&membership)?;
                let defining_equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: surface,
                    right: Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)),
                    line_file: None,
                }));
                self.store_fact_and_infer(&defining_equal)?;
            }
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(have_fn) => {
                self.store_instantiated_template_fn_set_membership(
                    value,
                    &have_fn.fn_set_clause,
                    &subst,
                )?;
            }
            TemplateDefEnum::HaveFnByInducStmt(have_fn) => {
                self.store_instantiated_template_fn_set_membership(
                    value,
                    &have_fn.fn_set_clause,
                    &subst,
                )?;
            }
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => {
                // Same three facts as plain `have fn by exist!` / `release obj def`,
                // with subjects = `\Name<args>` and template params substituted.
                let surface = Obj::InstantiatedTemplateObj(value.clone());
                match self.build_have_fn_by_forall_exist_unique_facts_for_surface(&surface, stmt)? {
                    Ok((membership, property, uniqueness)) => {
                        for fact in [membership, property, uniqueness] {
                            let Ok(inst) = self.inst_fact(&fact, &subst) else {
                                return Ok(());
                            };
                            self.store_fact_and_infer(&inst)?;
                        }
                    }
                    Err(_) => {}
                }
            }
            TemplateDefEnum::HaveObjEqualStmt(_) => {
                let Some(expanded_rhs) =
                    self.expanded_have_obj_equal_rhs_of_instantiated_template(value)?
                else {
                    return Ok(());
                };
                let surface = Obj::InstantiatedTemplateObj(value.clone());
                let defining_equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: surface,
                    right: expanded_rhs,
                    line_file: None,
                }));
                self.store_fact_and_infer(&defining_equal)?;
            }
            TemplateDefEnum::HaveByReplacementAxiomStmt(stmt) => {
                // Same three facts as plain `have … by replacement_axiom` / release:
                // `$is_set`, intro forall, elim forall — with `\Name<args>` as Img
                // and template params substituted into the source set.
                let Ok(source_set) = self.inst_obj(&stmt.source_set, &subst) else {
                    return Ok(());
                };
                let mut stmt_inst = stmt.clone();
                stmt_inst.source_set = source_set;
                let img = Obj::InstantiatedTemplateObj(value.clone());
                let type_fact = Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: img.clone(),
                    line_file: None,
                }));
                let intro = Fact::ForallFact(self.replacement_intro_forall(&stmt_inst, &img));
                let elim = Fact::ForallFact(self.replacement_elim_forall(&stmt_inst, &img));
                for fact in [type_fact, intro, elim] {
                    self.store_fact_and_infer(&fact)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn store_instantiated_template_fn_set_membership(
        &mut self,
        value: &InstantiatedTemplateObj,
        clause: &crate::ast::stmt::FnSetClause,
        subst: &HashMap<IdentifierId, Obj>,
    ) -> RuntimeResult<()> {
        let fn_set = crate::ast::obj::FnSet {
            set_bound_parameters: clause.set_bound_parameters.clone(),
            dom_facts: clause.dom_facts.clone(),
            ret_set: Box::new(clause.ret_set.clone()),
        };
        let Ok(inst_set) = self.inst_obj(&Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)), subst)
        else {
            return Ok(());
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(_)) = &inst_set else {
            return Ok(());
        };
        let surface = Obj::InstantiatedTemplateObj(value.clone());
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: surface,
            set: inst_set,
            line_file: None,
        }));
        self.store_fact_and_infer(&membership)?;
        Ok(())
    }
}

fn template_fail(
    obj: Obj,
    common: FailToVerifyObjWellDefinedByDefCommon,
) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj,
        reason: FailToVerifyObjWellDefinedResult::InstantiatedTemplateObj(
            FailToVerifyInstantiatedTemplateObjObjWellDefined(common),
        ),
    }
}

fn field_access_fail(obj: Obj, message: String) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj,
        reason: FailToVerifyObjWellDefinedResult::Structish(
            FailToVerifyStructishObjWellDefinedResult::FieldAccess(
                FailToVerifyFieldAccessObjWellDefined(
                    FailToVerifyObjWellDefinedByDefCommon::Others(message),
                ),
            ),
        ),
    }
}

// Same shapes as forall instantiation param-type obligations.
fn type_fact_for_instantiated_template_arg(
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
