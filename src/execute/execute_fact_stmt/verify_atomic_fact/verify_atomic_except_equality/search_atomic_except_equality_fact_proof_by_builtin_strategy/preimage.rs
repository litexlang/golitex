//! Preimage membership reduces to its certified bounded input subset.
use crate::ast::fact::{AtomicFact, Fact, InFact};
use crate::ast::obj::{FunctionSpace, Obj, ProductShape, Tuple};
use crate::execute::execute_fact_stmt::function_domain::function_application;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct PreimageMembershipStrategySingleStep {
    pub construction: FunctionPreimageConstructionProof,
    pub input_view: FunctionPreimageInputView,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct PreimageSetMembershipStrategySingleStep {
    pub construction: FunctionPreimageConstructionProof,
    pub input_view: FunctionPreimageInputView,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum FunctionPreimageInputView {
    BoundedAssignment,
    LiteralTuple { tuple: Tuple, input_equal: KnownEqualityPathProof },
}

struct FunctionPreimageMembershipRequirements {
    input_view: FunctionPreimageInputView,
    requirement_facts: Vec<Fact>,
}

impl Runtime {
    // x in preimage(f,y) iff x is legal and f(x)=y; no root solving.
    pub(super) fn search_preimage_membership_strategy(
        &mut self, fact: &AtomicFact, state: VerifyState,
    ) -> RuntimeResult<Option<PreimageMembershipStrategySingleStep>> {
        let AtomicFact::InFact(member) = fact else { return Ok(None); };
        if !matches!(&member.set, Obj::FunctionSpace(FunctionSpace::Preimage(_))) { return Ok(None); }
        let Ok(construction) = self.verify_function_preimage_construction(&member.set, state)? else { return Ok(None); };
        let requirements = self.preimage_membership_requirements(member, &construction)?;
        let Some((requirement_facts, proof_of_requirement_facts)) = self.verify_strategy_requirements(requirements.requirement_facts, state)? else { return Ok(None); };
        Ok(Some(PreimageMembershipStrategySingleStep { construction, input_view: requirements.input_view, requirement_facts, proof_of_requirement_facts }))
    }

    // x in preimage_set(f,Y) iff x is legal and f(x) in Y.
    pub(super) fn search_preimage_set_membership_strategy(
        &mut self, fact: &AtomicFact, state: VerifyState,
    ) -> RuntimeResult<Option<PreimageSetMembershipStrategySingleStep>> {
        let AtomicFact::InFact(member) = fact else { return Ok(None); };
        if !matches!(&member.set, Obj::FunctionSpace(FunctionSpace::PreimageSet(_))) { return Ok(None); }
        let Ok(construction) = self.verify_function_preimage_construction(&member.set, state)? else { return Ok(None); };
        let requirements = self.preimage_membership_requirements(member, &construction)?;
        let Some((requirement_facts, proof_of_requirement_facts)) = self.verify_strategy_requirements(requirements.requirement_facts, state)? else { return Ok(None); };
        Ok(Some(PreimageSetMembershipStrategySingleStep { construction, input_view: requirements.input_view, requirement_facts, proof_of_requirement_facts }))
    }

    fn preimage_membership_requirements(
        &mut self, member: &InFact, construction: &FunctionPreimageConstructionProof,
    ) -> RuntimeResult<FunctionPreimageMembershipRequirements> {
        let signature = &construction.source.signature;
        let parameters: Vec<_> = signature.set_bound_parameters.groups.iter().flat_map(|group| group.params.iter().map(move |param| (param, group.param_type.as_ref()))).collect();
        if parameters.len() != 1 {
            for (value, path) in self.exact_property_object_values(&member.element) {
                let Obj::ProductShape(ProductShape::Tuple(tuple)) = value else { continue; };
                if tuple.args.len() != parameters.len() { continue; }
                let mut substitution = std::collections::HashMap::new();
                let mut requirements = Vec::new();
                for ((param, carrier), argument) in parameters.iter().zip(&tuple.args) {
                    substitution.insert(param.id, argument.as_ref().clone());
                    requirements.push(InFact { fact_id: self.global_ids.allocate_fact_id(), element: argument.as_ref().clone(), set: (*carrier).clone(), line_file: member.line_file.clone() }.into());
                }
                for guard in &signature.dom_facts {
                    let guard = self.inst_quantifier_free_fact(guard, &substitution).map_err(|error| crate::runtime::RuntimeError::InternalBug(format!("preimage tuple guard: {error}")))?;
                    requirements.push(crate::instantiate::quantifier_free_fact_to_fact(guard));
                }
                let condition: Fact = match &member.set {
                    Obj::FunctionSpace(FunctionSpace::Preimage(value)) => crate::ast::fact::EqualFact { fact_id: self.global_ids.allocate_fact_id(), left: function_application(&value.function, tuple.args.clone()).map_err(crate::runtime::RuntimeError::InternalBug)?, right: value.value.as_ref().clone(), line_file: member.line_file.clone() }.into(),
                    Obj::FunctionSpace(FunctionSpace::PreimageSet(value)) => InFact { fact_id: self.global_ids.allocate_fact_id(), element: function_application(&value.function, tuple.args.clone()).map_err(crate::runtime::RuntimeError::InternalBug)?, set: value.target_set.as_ref().clone(), line_file: member.line_file.clone() }.into(),
                    _ => unreachable!("preimage membership root"),
                };
                requirements.push(condition);
                return Ok(FunctionPreimageMembershipRequirements { input_view: FunctionPreimageInputView::LiteralTuple { tuple, input_equal: KnownEqualityPathProof::new(path) }, requirement_facts: requirements });
            }
        }
        let builder = &construction.builder;
        let mut requirements = vec![InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: member.element.clone(),
            set: builder.param_set.as_ref().clone(), line_file: member.line_file.clone(),
        }.into()];
        let mut substitution = std::collections::HashMap::new();
        substitution.insert(builder.param_binding.id, member.element.clone());
        for condition in &builder.facts {
            let condition = self.inst_quantifier_free_fact(condition, &substitution)
                .map_err(|error| crate::runtime::RuntimeError::InternalBug(format!("preimage membership substitution: {error}")))?;
            requirements.push(crate::instantiate::quantifier_free_fact_to_fact(condition));
        }
        Ok(FunctionPreimageMembershipRequirements { input_view: FunctionPreimageInputView::BoundedAssignment, requirement_facts: requirements })
    }
}
