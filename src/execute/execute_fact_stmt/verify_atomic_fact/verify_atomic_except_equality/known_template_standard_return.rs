use super::known_fn_standard_return::SignatureStandardReturnProof;
use super::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::known_tuple::tuple_function_head;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::prelude::*;

pub struct TemplateApplicationInStandardSupersetProof {
    pub target_set: StandardSet,
    pub declared_returns: Vec<DeclaredStandardReturnProof>,
    pub signature_returns: Vec<SignatureStandardReturnProof>,
}

pub struct DeclaredStandardReturnProof {
    pub function: Obj,
    pub function_equal: KnownEqualityPathProof,
    pub declared_signature: FnSet,
    pub source_set: StandardSet,
}

impl Runtime {
    // Checked application WD supplies the actual arguments and template guards.
    // R-valued template calls, for example, also belong to C. Read declarations
    // and stored signatures only; every applicable return must fit the target.
    pub(super) fn known_template_application_standard_superset(
        &mut self,
        fact: &InFact,
    ) -> Option<TemplateApplicationInStandardSupersetProof> {
        let Obj::StandardSet(target) = &fact.set else {
            return None;
        };
        let Obj::FnObj(application) = &fact.element else {
            return None;
        };
        if application.body.is_empty()
            || matches!(application.head.as_ref(), FnObjHead::AnonymousFnLiteral(_))
        {
            return None;
        }
        let head = tuple_function_head(application);
        let peers = self.exact_property_object_values_of_shapes(
            &head,
            &[
                EqualToObjShape::InstantiatedTemplateObj,
                EqualToObjShape::FieldAccess,
                EqualToObjShape::Other,
            ],
        );
        if !peers
            .iter()
            .any(|(peer, _)| matches!(peer, Obj::InstantiatedTemplateObj(_)))
        {
            return None;
        }
        // Finite-function WD has its own intrinsic source. Do not ignore it or
        // reopen its domain proof inside this known-property leaf.
        if !self.finite_function_signatures(&head).is_empty() {
            return None;
        }
        let mut declared_returns = Vec::new();
        let mut has_template = false;
        let mut strict_inclusion = false;
        for (peer, path) in peers {
            let signature = match &peer {
                Obj::Identifier(_) => continue,
                Obj::InstantiatedTemplateObj(instance) => {
                    self.instantiated_template_function_signature(instance)?
                }
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) => {
                    let field_type = self.resolve_field_access_field_type(access)?;
                    self.function_space_signature(&field_type)?
                }
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => function.body.clone(),
                // Composition, matrix, returned-call and other intrinsic
                // sources are not covered by this declaration-only evidence.
                _ => return None,
            };
            let Some(ret) = self.applied_fn_set_return_set(application, &signature) else {
                continue;
            };
            let Obj::StandardSet(source) = ret else {
                return None;
            };
            if !standard_set_is_subset_eq(&source, target) {
                return None;
            }
            has_template |= matches!(peer, Obj::InstantiatedTemplateObj(_));
            strict_inclusion |= source != *target;
            declared_returns.push(DeclaredStandardReturnProof {
                function: peer,
                function_equal: KnownEqualityPathProof::new(path),
                declared_signature: signature,
                source_set: source,
            });
        }
        if !has_template {
            return None;
        }
        let mut signature_returns = Vec::new();
        for (signature, id) in self.collect_in_function_set_candidates(&head) {
            let Some(ret) = self.applied_fn_set_return_set(application, &signature) else {
                continue;
            };
            let Obj::StandardSet(source) = ret else {
                return None;
            };
            if !standard_set_is_subset_eq(&source, target) {
                return None;
            }
            let property = match self.fact_by_id_in_stack(id) {
                Some(Fact::AtomicFact(AtomicFact::InFact(f))) => {
                    SpecialProperty::Membership(f.clone())
                }
                Some(Fact::AtomicFact(AtomicFact::EqualFact(f))) => {
                    SpecialProperty::Equality(f.clone())
                }
                _ => return None,
            };
            let path = self.exact_property_equality_path(&head, property.function_subject()?)?;
            strict_inclusion |= source != *target;
            signature_returns.push(SignatureStandardReturnProof {
                cite_signature_fact_id: id,
                source_set: source,
                function_equal: KnownEqualityPathProof::new(path),
            });
        }
        if !strict_inclusion {
            return None;
        }
        Some(TemplateApplicationInStandardSupersetProof {
            target_set: target.clone(),
            declared_returns,
            signature_returns,
        })
    }
}
