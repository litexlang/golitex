use super::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq;
use crate::ast::fact::{AtomicFact, Fact, InFact};
use crate::ast::obj::{FnObjHead, Obj, StandardSet, StructAndFieldAccessObj};
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::{FactId, Runtime};

pub struct FnApplicationInStandardSupersetProof {
    pub target_set: StandardSet,
    pub signature_returns: Vec<SignatureStandardReturnProof>,
}

pub struct SignatureStandardReturnProof {
    pub cite_signature_fact_id: FactId,
    pub source_set: StandardSet,
    pub function_equal: KnownEqualityPathProof,
}

impl Runtime {
    // Application WD has already checked the actual arguments and domain.
    // Every signature that could have supplied cached WD must return values
    // inside the target standard set: R-returning f(x) is in C, for example.
    // This is a pure carrier comparison, not equality or new premise search.
    pub(super) fn known_fn_application_standard_superset(
        &mut self,
        fact: &InFact,
    ) -> Option<FnApplicationInStandardSupersetProof> {
        let Obj::StandardSet(target) = &fact.set else {
            return None;
        };
        let Obj::FnObj(application) = &fact.element else {
            return None;
        };
        let head = match application.head.as_ref() {
            FnObjHead::Object(obj) => obj.as_ref().clone(),
            FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
            FnObjHead::InstantiatedTemplateObj(instance) => {
                Obj::InstantiatedTemplateObj(instance.clone())
            }
            FnObjHead::FieldAccess(access) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()))
            }
            // Intrinsic signatures have their own existing proof route.
            FnObjHead::AnonymousFnLiteral(_) => return None,
        };
        // Native template/field declarations can supply WD without a stored
        // membership. Their existing producers retain that declaration evidence;
        // this stored-signature leaf must not ignore such an alternative.
        for (peer, _) in self.exact_property_object_values(&head) {
            if matches!(
                peer,
                Obj::InstantiatedTemplateObj(_) | Obj::StructAndFieldAccessObj(_)
            ) {
                return None;
            }
        }
        let mut signature_returns = Vec::new();
        let mut strict_inclusion = false;
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
            let source_fact = match self.fact_by_id_in_stack(id) {
                Some(Fact::AtomicFact(AtomicFact::InFact(f))) => {
                    SpecialProperty::Membership(f.clone())
                }
                Some(Fact::AtomicFact(AtomicFact::EqualFact(f))) => {
                    SpecialProperty::Equality(f.clone())
                }
                _ => return None,
            };
            let subject = source_fact.function_subject()?;
            let path = self.exact_property_equality_path(&head, subject)?;
            strict_inclusion |= source != *target;
            signature_returns.push(SignatureStandardReturnProof {
                cite_signature_fact_id: id,
                source_set: source,
                function_equal: KnownEqualityPathProof::new(path),
            });
        }
        if signature_returns.is_empty() || !strict_inclusion {
            return None;
        }
        Some(FnApplicationInStandardSupersetProof {
            target_set: target.clone(),
            signature_returns,
        })
    }
}
