use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact, NormalAtomicFact,
};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    AtomicExceptEqualityFactSearchProofByDefinition, UserDefinedPropDefinitionProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{GlobalIds, Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // Ambient definition expansion: builtin predicate defs, then user `prop` defs.
    // Soft miss → Ok(None). Does not handle abstract_prop or statement `by def`.
    // Example (user prop):
    //   prop above_zero(x R):
    //       x > 0
    //   $above_zero(1)
    // Example (builtin):
    //   by def N $subset R
    // Finite list-set inclusions like `{1} $subset {1, 2}` belong to
    // `by enumerate finite_set`, not this forall-definition route.
    pub fn search_atomic_except_equality_fact_proof_by_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByDefinition>> {
        if let Some(proof) =
            self.search_builtin_prop_definition_proof(fact, verify_state.clone())?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(proof),
            ));
        }

        let AtomicFact::NormalAtomicFact(normal) = fact else {
            return Ok(None);
        };
        // Plain / file-root / cross-mod: store keys stay unqualified local names.
        if self
            .def_abstract_prop_visible(&normal.predicate)
            .is_some()
        {
            return Ok(None);
        }
        let Some(definition) = self.def_prop_visible(&normal.predicate) else {
            return Ok(None);
        };
        if definition.iff_facts.is_empty() {
            return Ok(None);
        }
        let definition = definition.clone();
        self.prove_normal_atomic_by_user_prop_definition(normal, &definition, verify_state)
    }

    fn prove_normal_atomic_by_user_prop_definition(
        &mut self,
        normal: &NormalAtomicFact,
        definition: &DefPropStmt,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByDefinition>> {
        let flat = flatten_typed_parameters(&definition.typed_parameters);
        if flat.len() != normal.body.len() {
            return Ok(None);
        }
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        let mut requirement_facts = Vec::new();
        for ((param, param_type), arg) in flat.iter().zip(normal.body.iter()) {
            subst.insert(param.id, arg.clone());
            let Some(type_fact) = type_obligation_fact(arg, param_type, &mut self.global_ids) else {
                return Ok(None);
            };
            requirement_facts.push(type_fact);
        }
        for iff_fact in &definition.iff_facts {
            let instantiated = match self.inst_fact(iff_fact, &subst) {
                Ok(f) => f,
                Err(_) => return Ok(None),
            };
            requirement_facts.push(instantiated);
        }
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for requirement in &requirement_facts {
            let proof = self.verify_fact(requirement, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some(
            AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(
                UserDefinedPropDefinitionProof {
                    requirement_facts,
                    proof_of_requirement_facts,
                },
            ),
        ))
    }
}

fn flatten_typed_parameters(
    list: &TypedParameterList,
) -> Vec<(crate::new_pipeline::ast::names::BoundName, ParamType)> {
    let mut out = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            out.push((param.clone(), group.param_type.clone()));
        }
    }
    out
}

fn type_obligation_fact(arg: &Obj, param_type: &ParamType, global_ids: &mut GlobalIds) -> Option<Fact> {
    let fact_id = global_ids.allocate_fact_id();
    match param_type {
        ParamType::Obj(set) => Some(Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id,
            element: arg.clone(),
            set: set.clone(),
            line_file: None,
        }))),
        ParamType::Set(_) => Some(Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: arg.clone(),
            line_file: None,
        }))),
        ParamType::NonemptySet(_) => Some(Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
            IsNonemptySetFact {
                fact_id,
                set: arg.clone(),
                line_file: None,
            },
        ))),
        ParamType::FiniteSet(_) => Some(Fact::AtomicFact(AtomicFact::IsFiniteSetFact(
            IsFiniteSetFact {
                fact_id,
                set: arg.clone(),
                line_file: None,
            },
        ))),
    }
}
