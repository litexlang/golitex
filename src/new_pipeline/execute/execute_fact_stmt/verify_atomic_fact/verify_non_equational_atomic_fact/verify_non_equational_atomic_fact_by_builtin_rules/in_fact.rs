use crate::new_pipeline::ast::fact::{Fact, InFact};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum InFactSearchProofByBuiltinRule {
    // Closed numeric membership by evaluation, e.g. prove `2 $in N`.
    ClosedNumericMembership(ClosedNumericMembershipBuiltinRuleProof),
    // Set-builder membership from base membership plus defining facts.
    // Example: prove `x $in {t R: t > 0}` from `x $in R` and `x > 0`.
    SetBuilderMembership(SetBuilderMembershipBuiltinRuleProof),
    // Native mathematical constants inhabit fixed carriers.
    // Example: prove `e $in R+`, `pi $in R`, `i $in C`.
    NativeConstantMembership(NativeConstantMembershipBuiltinRuleProof),
}

pub struct ClosedNumericMembershipBuiltinRuleProof {}

pub struct SetBuilderMembershipBuiltinRuleProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum NativeConstantMembershipKind {
    ImaginaryUnitInComplex,
    EulerNumberInPositiveReal,
    EulerNumberInReal,
    EulerNumberInComplex,
    PiInPositiveReal,
    PiInReal,
    PiInComplex,
}

pub struct NativeConstantMembershipBuiltinRuleProof {
    pub kind: NativeConstantMembershipKind,
}

impl Runtime {
    // Builtin: zero-premise native-constant membership.
    // Example: prove `e $in R+`, `pi $in R`, `i $in C`.
    pub fn search_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let _ = verify_state;
        if let Some(kind) = native_constant_membership_kind(&fact.element, &fact.set) {
            return Ok(Some(
                InFactSearchProofByBuiltinRule::NativeConstantMembership(
                    NativeConstantMembershipBuiltinRuleProof { kind },
                ),
            ));
        }
        Ok(None)
    }
}

fn native_constant_membership_kind(
    element: &Obj,
    set: &Obj,
) -> Option<NativeConstantMembershipKind> {
    match (element, set) {
        (Obj::ImaginaryUnit(_), Obj::StandardSet(StandardSet::C)) => {
            Some(NativeConstantMembershipKind::ImaginaryUnitInComplex)
        }
        (Obj::EulerNumber(_), Obj::StandardSet(StandardSet::RPos)) => {
            Some(NativeConstantMembershipKind::EulerNumberInPositiveReal)
        }
        (Obj::EulerNumber(_), Obj::StandardSet(StandardSet::R)) => {
            Some(NativeConstantMembershipKind::EulerNumberInReal)
        }
        (Obj::EulerNumber(_), Obj::StandardSet(StandardSet::C)) => {
            Some(NativeConstantMembershipKind::EulerNumberInComplex)
        }
        (Obj::Pi(_), Obj::StandardSet(StandardSet::RPos)) => {
            Some(NativeConstantMembershipKind::PiInPositiveReal)
        }
        (Obj::Pi(_), Obj::StandardSet(StandardSet::R)) => {
            Some(NativeConstantMembershipKind::PiInReal)
        }
        (Obj::Pi(_), Obj::StandardSet(StandardSet::C)) => {
            Some(NativeConstantMembershipKind::PiInComplex)
        }
        _ => None,
    }
}
