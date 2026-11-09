//! Read a declaration's carrier without selecting a view from later facts.

use crate::ast::stmt::{FnSetClause, TemplateDefEnum};
use crate::exec_env::StoredIdentifierDefinition;
use crate::prelude::*;

impl Runtime {
    // This is a structural reader, not a WD proof. Callers must check the
    // actual object, including function arguments and template guards.
    pub(in crate::execute) fn definition_owned_type(&mut self, obj: &Obj) -> Option<Obj> {
        match obj {
            Obj::Identifier(identifier) => {
                let definition = self
                    .stored_identifier_definition_visible(identifier)?
                    .clone();
                let name = match identifier {
                    IdentifierObj::Plain { name, .. }
                    | IdentifierObj::WithExportFileId { name, .. }
                    | IdentifierObj::WithModAndExportFileId { name, .. } => name,
                };
                let parameters = match definition {
                    StoredIdentifierDefinition::HaveFnEqual((_, stmt)) => {
                        return Some(fn_type(stmt.equal_to_anonymous_fn.body.clone()))
                    }
                    StoredIdentifierDefinition::HaveFnEqualCaseByCase((_, stmt)) => {
                        return Some(clause_type(&stmt.fn_set_clause))
                    }
                    StoredIdentifierDefinition::HaveFnByInduc((_, stmt)) => {
                        return Some(clause_type(&stmt.fn_set_clause))
                    }
                    StoredIdentifierDefinition::HaveFnByForallExistUnique((_, stmt)) => {
                        return self.have_fn_by_exist_signature(&stmt).map(fn_type)
                    }
                    StoredIdentifierDefinition::ParamType((_, ty)) => return obj_type(&ty),
                    StoredIdentifierDefinition::HaveObjEqual((_, stmt)) => stmt.param_def.clone(),
                    StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((_, stmt)) => {
                        stmt.param_def.clone()
                    }
                    StoredIdentifierDefinition::HaveObjByExistFacts((_, stmt)) => {
                        stmt.param_def.clone()
                    }
                    StoredIdentifierDefinition::TrustHave((_, stmt)) => stmt.param_def.clone(),
                    StoredIdentifierDefinition::LetObj(_)
                    | StoredIdentifierDefinition::HaveByReplacementAxiom(_) => return None,
                };
                let carrier = parameters
                    .groups
                    .iter()
                    .find(|group| group.params.iter().any(|p| &p.name == name))
                    .and_then(|group| obj_type(&group.param_type))?;
                let substitution = crate::execute::helper::parameter_substitution_for_surface(
                    identifier,
                    &parameters,
                );
                self.inst_obj(&carrier, &substitution).ok()
            }
            Obj::FnObj(application) => {
                let head = super::helper::fn_obj_head_as_obj(&application.head);
                let carrier = self.definition_owned_type(&head)?;
                let signature = self.function_space_signature(&carrier)?;
                self.applied_fn_set_return_set(application, &signature)
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                Some(fn_type(function.body.clone()))
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field)) => {
                self.resolve_field_access_field_type(field)
            }
            Obj::InstantiatedTemplateObj(instance) => {
                if let Some(signature) = self.instantiated_template_function_signature(instance) {
                    return Some(fn_type(signature));
                }
                let definition = self.def_template_visible(&instance.template_name)?.clone();
                let mut substitution =
                    self.template_instance_substitution(&definition, instance)?;
                let outputs = definition.template_def_stmt.defined_bindings();
                let index = outputs
                    .iter()
                    .position(|p| p.name == instance.template_name.local_name())?;
                let family = match &definition.template_def_stmt {
                    TemplateDefEnum::ObtainObjFromExistFact(stmt) => Some(stmt.fact.clone()),
                    TemplateDefEnum::ObtainObjFromAtomicFact(stmt) => {
                        let prop = self.def_prop_visible(&stmt.fact.predicate)?.clone();
                        let ids = prop.typed_parameters.ordered_param_ids();
                        if ids.len() != stmt.fact.body.len() {
                            return None;
                        }
                        let params = ids
                            .into_iter()
                            .zip(stmt.fact.body.iter().cloned())
                            .collect();
                        let family = crate::execute::execute_obtain_obj_from_atomic_fact_stmt::project_sole_positive_exist_clause(&prop.iff_facts).ok()?;
                        let source = match family {
                            ExistShapedFact::Exist(p) => Fact::ExistFact(p),
                            ExistShapedFact::ExistUnique(p) => Fact::ExistUniqueFact(p),
                            _ => return None,
                        };
                        let fact = self.inst_fact(&source, &params).ok()?;
                        Some(match fact {
                            Fact::ExistFact(p) => ExistShapedFact::Exist(p),
                            Fact::ExistUniqueFact(p) => ExistShapedFact::ExistUnique(p),
                            _ => return None,
                        })
                    }
                    _ => None,
                };
                if let Some(family) = family {
                    let carrier = super::structs::existential_template_carrier(
                        &family,
                        index,
                        &outputs,
                        &mut substitution,
                    )?;
                    return self.inst_obj(&carrier, &substitution).ok();
                }
                let parameters = match &definition.template_def_stmt {
                    TemplateDefEnum::HaveObjEqualStmt(stmt) => &stmt.param_def,
                    TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => &stmt.param_def,
                    TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => &stmt.param_def,
                    TemplateDefEnum::TrustHaveStmt(stmt) => &stmt.param_def,
                    _ => return None,
                };
                let group = parameters.groups.iter().find(|g| {
                    g.params
                        .iter()
                        .any(|p| p.name == instance.template_name.local_name())
                })?;
                let carrier = obj_type(&group.param_type)?;
                self.inst_obj(&carrier, &substitution).ok()
            }
            _ => None,
        }
    }
}

fn obj_type(ty: &ParamType) -> Option<Obj> {
    match ty {
        ParamType::Obj(obj) => Some(obj.clone()),
        _ => None,
    }
}

fn fn_type(signature: FnSet) -> Obj {
    Obj::FunctionSpace(FunctionSpace::FnSet(signature))
}

fn clause_type(clause: &FnSetClause) -> Obj {
    fn_type(FnSet {
        set_bound_parameters: clause.set_bound_parameters.clone(),
        dom_facts: clause.dom_facts.clone(),
        ret_set: Box::new(clause.ret_set.clone()),
    })
}
