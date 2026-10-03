//! The unique preimage leaf consumes a stored bijection, never a guessed map law.
use std::collections::HashSet;

use crate::ast::fact::{AtomicFact, ExistShapedFact, Fact, InFact, QuantifierFreeFact};
use crate::ast::obj::{FnObjHead, FunctionSpace, IdentifierObj, Obj, StructAndFieldAccessObj};
use crate::ast::param::ParamType;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::instantiate::collect_free_plain_ids;
use crate::runtime::{Runtime, RuntimeResult};

use super::result::ExistShapedBuiltinBijectivePreimage;

impl Runtime {
    pub(super) fn search_exist_builtin_bijective_preimage(
        &mut self,
        fact: &ExistShapedFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ExistShapedBuiltinBijectivePreimage>> {
        let ExistShapedFact::ExistUnique(plain) = fact else {
            return Ok(None);
        };
        let groups = &plain.typed_parameters.groups;
        if groups.len() != 1 || groups[0].params.len() != 1 || plain.facts.len() != 1 {
            return Ok(None);
        }
        let ParamType::Obj(domain) = &groups[0].param_type else {
            return Ok(None);
        };
        let witness_id = groups[0].params[0].id;
        let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal)) = &plain.facts[0] else {
            return Ok(None);
        };
        for (application, target) in [(&equal.left, &equal.right), (&equal.right, &equal.left)] {
            let Obj::FnObj(application) = application else {
                continue;
            };
            if application.body.len() != 1 || application.body[0].len() != 1 {
                continue;
            }
            if !matches!(application.body[0][0].as_ref(),
                Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id == witness_id)
            {
                continue;
            }
            let function = match application.head.as_ref() {
                FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
                FnObjHead::AnonymousFnLiteral(f) => {
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
                }
                FnObjHead::FieldAccess(field) => Obj::StructAndFieldAccessObj(
                    StructAndFieldAccessObj::FieldAccess(field.clone()),
                ),
                FnObjHead::InstantiatedTemplateObj(template) => {
                    Obj::InstantiatedTemplateObj(template.clone())
                }
            };
            // Both the map and target must be independent of the chosen witness.
            // In particular, a bijection does not prove `exist! x A st {f(x)=f(x)}`.
            let mut free = HashSet::new();
            collect_free_plain_ids(&function, &HashSet::new(), &mut free);
            collect_free_plain_ids(target, &HashSet::new(), &mut free);
            collect_free_plain_ids(domain, &HashSet::new(), &mut free);
            if free.contains(&witness_id) {
                continue;
            }
            let certificates: Vec<_> = self
                .execution_environments_stack
                .iter()
                .rev()
                .flat_map(|env| env.facts.facts_by_id.values())
                .filter_map(|known| match known {
                    Fact::AtomicFact(AtomicFact::BijectiveFact(b))
                        if b.domain.ir() == domain.ir() && b.function.ir() == function.ir() =>
                    {
                        Some(b.clone())
                    }
                    _ => None,
                })
                .collect();
            for bijection in certificates {
                let codomain = bijection.codomain.clone();
                let Some(certificate) =
                    self.lookup_known_atomic_premise(AtomicFact::BijectiveFact(bijection))
                else {
                    continue;
                };
                let membership: Fact = InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: target.clone(),
                    set: codomain,
                    line_file: plain.line_file.clone(),
                }
                .into();
                let target_membership =
                    self.verify_builtin_rule_premise(&membership, state.clone())?;
                if !target_membership.is_failed() {
                    return Ok(Some(ExistShapedBuiltinBijectivePreimage {
                        certificate,
                        target_membership,
                    }));
                }
            }
        }
        Ok(None)
    }
}
