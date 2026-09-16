use crate::new_pipeline::ast::fact::{AtomicFact, Fact, InFact};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

use super::subset::standard_set_is_subset_eq;

// Builtin rules for `$in` facts (zero-premise or known-cite routes).
pub enum InFactSearchProofByBuiltinRule {
    // Closed numeric membership by decimal evaluation.
    // Mathematical property: a closed expression that evaluates to a normalized
    // decimal inhabits the matching standard set (N/Z/Q/R/C families).
    // Examples: `2 $in N`, `1 + 1 $in C`, `-3 $in Z`.
    ClosedNumericMembership(ClosedNumericMembershipBuiltinRuleProof),
    // Well-defined complex arithmetic expressions inhabit C.
    // Mathematical property: after child WD, `+ - * / …` over C-carriers stay in C.
    // Example: prove `(x + 1) $in C` (used when Add/Mul WD asks for `$in C`).
    ComplexArithmeticClosure(ComplexArithmeticClosureBuiltinRuleProof),
    // Membership lifts along the standard-set inclusion chain.
    // Mathematical property: if `x $in S` and `S $subset T` among standard sets,
    // then `x $in T`.
    // Example: known `x $in R` proves `x $in C`.
    StandardSetSubsetMembership(StandardSetSubsetMembershipBuiltinRuleProof),
    // Set-builder membership from base membership plus defining facts.
    // Example: prove `x $in {t R: t > 0}` from `x $in R` and `x > 0`.
    SetBuilderMembership(SetBuilderMembershipBuiltinRuleProof),
    // Native mathematical constants inhabit fixed carriers.
    // Example: prove `e $in R+`, `pi $in R`, `i $in C`.
    NativeConstantMembership(NativeConstantMembershipBuiltinRuleProof),
}

// Closed decimal membership certificate (sides live on the InFact).
// Example: `2 $in N`.
pub struct ClosedNumericMembershipBuiltinRuleProof {}

// C-arithmetic closure certificate (sides live on the InFact).
// Example: `(x + 1) $in C`.
pub struct ComplexArithmeticClosureBuiltinRuleProof {}

// Subset-lift certificate: cite a known smaller-set membership.
// Example: source_set `R`, cite `x $in R`, goal `x $in C`.
pub struct StandardSetSubsetMembershipBuiltinRuleProof {
    pub source_set: StandardSet,
    pub cite_fact_id: FactId,
}

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
    // Builtin InFact search: closed decimal, C-arithmetic closure, subset lift,
    // then native constants.
    // Example: `1 $in C`, `(x + 1) $in C`, `x $in C` from `x $in R`, `e $in R+`.
    pub fn search_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        if let Some(proof) = closed_numeric_membership_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) = complex_arithmetic_in_c_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.standard_set_subset_membership_proof(fact, verify_state)? {
            return Ok(Some(proof));
        }
        if let Some(kind) = native_constant_membership_kind(&fact.element, &fact.set) {
            return Ok(Some(
                InFactSearchProofByBuiltinRule::NativeConstantMembership(
                    NativeConstantMembershipBuiltinRuleProof { kind },
                ),
            ));
        }
        Ok(None)
    }

    // Prove `element $in target` from a known `element $in source` with source ⊂ target.
    // Example: known `x $in R` proves `x $in C`.
    fn standard_set_subset_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::StandardSet(target) = &fact.set else {
            return Ok(None);
        };
        for source in proper_subsets_in_membership_proof_order(target) {
            let probe = AtomicFact::InFact(InFact {
                fact_id: self.ids.allocate_fact_id(),
                element: fact.element.clone(),
                set: Obj::StandardSet(source.clone()),
                line_file: None,
            });
            if let Some(known) = self
                .search_atomic_except_equality_fact_proof_by_known_atomic_fact(
                    &probe,
                    verify_state.clone(),
                )?
            {
                return Ok(Some(
                    InFactSearchProofByBuiltinRule::StandardSetSubsetMembership(
                        StandardSetSubsetMembershipBuiltinRuleProof {
                            source_set: source,
                            cite_fact_id: known.cite_fact_id,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }
}

// Prove `element $in set` when element evaluates to a closed decimal that
// inhabits the StandardSet. Example: `1 + 1 $in C`.
fn closed_numeric_membership_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let number = evaluate_obj_to_normalized_decimal_number(&fact.element)?;
    let Obj::StandardSet(set) = &fact.set else {
        return None;
    };
    if !normalized_decimal_inhabits_standard_set(&number.normalized_value, set) {
        return None;
    }
    Some(InFactSearchProofByBuiltinRule::ClosedNumericMembership(
        ClosedNumericMembershipBuiltinRuleProof {},
    ))
}

fn normalized_decimal_inhabits_standard_set(v: &str, set: &StandardSet) -> bool {
    let v = v.trim();
    let is_integer = !v.contains('.');
    let is_negative = v.starts_with('-');
    let is_zero = v == "0";
    let is_positive = !is_negative && !is_zero;
    let is_nonzero = !is_zero;
    match set {
        StandardSet::N => is_integer && !is_negative,
        StandardSet::NPos => is_integer && is_positive,
        StandardSet::Z => is_integer,
        StandardSet::ZStar => is_integer && is_nonzero,
        StandardSet::ZNeg => is_integer && is_negative,
        StandardSet::Q | StandardSet::R | StandardSet::C => true,
        StandardSet::QPos | StandardSet::RPos => is_positive,
        StandardSet::QNeg | StandardSet::RNeg => is_negative,
        StandardSet::QStar | StandardSet::RStar | StandardSet::CStar => is_nonzero,
    }
}

// WD already forces complex operand domains; Add/Sub/Mul/... are closed in C.
// Example: prove `(x + 1) * (x - 1) $in C`.
fn complex_arithmetic_in_c_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::C) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::Add(_)
        | Obj::Sub(_)
        | Obj::Mul(_)
        | Obj::Div(_)
        | Obj::Mod(_)
        | Obj::Quot(_)
        | Obj::Pow(_)
        | Obj::Abs(_)
        | Obj::Sqrt(_)
        | Obj::Log(_) => Some(InFactSearchProofByBuiltinRule::ComplexArithmeticClosure(
            ComplexArithmeticClosureBuiltinRuleProof {},
        )),
        _ => None,
    }
}

fn proper_subsets_in_membership_proof_order(target: &StandardSet) -> Vec<StandardSet> {
    [
        StandardSet::N,
        StandardSet::Z,
        StandardSet::Q,
        StandardSet::R,
        StandardSet::NPos,
        StandardSet::ZNeg,
        StandardSet::ZStar,
        StandardSet::QPos,
        StandardSet::QNeg,
        StandardSet::QStar,
        StandardSet::RPos,
        StandardSet::RNeg,
        StandardSet::RStar,
        StandardSet::CStar,
    ]
    .into_iter()
    .filter(|source| source != target && standard_set_is_subset_eq(source, target))
    .collect()
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
