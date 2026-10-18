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
                parameters
                    .groups
                    .iter()
                    .find(|group| group.params.iter().any(|p| &p.name == name))
                    .and_then(|group| obj_type(&group.param_type))
            }
            Obj::FnObj(application) => {
                let head = super::helper::fn_obj_head_as_obj(&application.head);
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) =
                    self.definition_owned_type(&head)?
                else {
                    return None;
                };
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
                let ids = definition.template_arg_def.ordered_param_ids();
                if ids.len() != instance.args.len() {
                    return None;
                }
                let parameters = match &definition.template_def_stmt {
                    TemplateDefEnum::HaveObjEqualStmt(stmt) => &stmt.param_def,
                    TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => &stmt.param_def,
                    TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => &stmt.param_def,
                    TemplateDefEnum::TrustHaveStmt(stmt) => &stmt.param_def,
                    _ => return None,
                };
                let carrier = obj_type(&parameters.groups.first()?.param_type)?;
                let substitution = ids.into_iter().zip(instance.args.iter().cloned()).collect();
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
