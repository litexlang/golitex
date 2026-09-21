use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, InFact, SubsetFact};
use crate::new_pipeline::ast::obj::{FnObjHead, Number, Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::match_sub_one;
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
    // Explicit finite list-set membership by equality to one listed element.
    // Mathematical property: if `x = a_i` for some `a_i` in `{a_1, …, a_n}`,
    // then `x $in {a_1, …, a_n}`.
    // Example: `1 $in {1, 2}`.
    ListSetElementMembership(ListSetElementMembershipBuiltinRuleProof),
    // Power-set membership from subset.
    // Mathematical property: if `A $subset B`, then `A $in power_set(B)`.
    // Example: `{x R: x > 0} $subset R` proves `{x R: x > 0} $in power_set(R)`.
    PowerSetMembership(PowerSetMembershipBuiltinRuleProof),
    // Natural predecessor stays in N under a known lower bound of one.
    // Mathematical property: `x $in N` and `x >= 1` ⇒ `x - 1 $in N`.
    // Example: known `n $in N` and `n >= 1` prove `n - 1 $in N`.
    PredecessorInNatural(PredecessorInNaturalBuiltinRuleProof),
    // Well-typed function application lands in the declared return set.
    // Mathematical property: if `f $in fn(params) R` and `f(args)` matches that
    // signature's domain, then `f(args) $in subst(R)`.
    // Example: after restricted `countdown $in fn(_n N: …) N`, prove
    // `countdown(n - 1) $in N`.
    FnApplicationInCodomain(FnApplicationInCodomainBuiltinRuleProof),
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

pub struct ListSetElementMembershipBuiltinRuleProof {
    pub selected_index: usize,
    pub equality_proof: VerifyFactResult,
}

pub struct PowerSetMembershipBuiltinRuleProof {
    pub subset_proof: VerifyFactResult,
}

pub struct PredecessorInNaturalBuiltinRuleProof {
    pub cite_in_n_fact_id: FactId,
    pub cite_at_least_one_fact_id: FactId,
}

pub struct FnApplicationInCodomainBuiltinRuleProof {
    pub cite_in_function_set_fact_id: FactId,
}

impl Runtime {
    // Builtin InFact search: closed decimal, C-arithmetic closure, subset lift,
    // set-builder membership, then native constants.
    // Example: `1 $in C`, `(x + 1) $in C`, `x $in C` from `x $in R`,
    // `a $in {x R: x > 0}` from `a $in R` and `a > 0`.
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
        if let Some(proof) = self.predecessor_in_natural_proof(fact)? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.fn_application_in_codomain_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.standard_set_subset_membership_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.set_builder_membership_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.power_set_membership_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(kind) = native_constant_membership_kind(&fact.element, &fact.set) {
            return Ok(Some(
                InFactSearchProofByBuiltinRule::NativeConstantMembership(
                    NativeConstantMembershipBuiltinRuleProof { kind },
                ),
            ));
        }
        if let Some(proof) = self.list_set_element_membership_proof(fact, verify_state)? {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    // Prove `x - 1 $in N` from known `x $in N` and `x >= 1`.
    // Example: after assuming `n $in N` and `n >= 1`, prove `n - 1 $in N`.
    fn predecessor_in_natural_proof(
        &mut self,
        fact: &InFact,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::StandardSet(StandardSet::N) = &fact.set else {
            return Ok(None);
        };
        let Some(base) = match_sub_one(&fact.element) else {
            return Ok(None);
        };
        let Some(cite_in_n_fact_id) = self.known_in_natural_fact_id(base) else {
            return Ok(None);
        };
        let one = Obj::Number(Number {
            normalized_value: "1".to_string(),
        });
        let Some(cite_at_least_one_fact_id) = self.known_greater_equal_fact_id(base, &one) else {
            return Ok(None);
        };
        Ok(Some(InFactSearchProofByBuiltinRule::PredecessorInNatural(
            PredecessorInNaturalBuiltinRuleProof {
                cite_in_n_fact_id,
                cite_at_least_one_fact_id,
            },
        )))
    }

    // Prove `f(args) $in R` from a matching InFunctionSet whose applied return is `R`.
    // Example: restricted `countdown $in fn(_n N: …) N` proves `countdown(n - 1) $in N`.
    fn fn_application_in_codomain_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::FnObj(fn_obj) = &fact.element else {
            return Ok(None);
        };
        let FnObjHead::Identifier(head) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        let head_obj = Obj::Identifier(head.clone());
        let candidates = self.collect_in_function_set_candidates(&head_obj);
        for (fn_set, cite_in_function_set_fact_id) in candidates {
            match self.try_verify_fn_obj_against_fn_set(fn_obj, &fn_set, verify_state.clone())? {
                Ok(_) => {
                    let Some(applied_ret) = self.applied_fn_set_return_set(fn_obj, &fn_set) else {
                        continue;
                    };
                    if applied_ret.ir() != fact.set.ir() {
                        continue;
                    }
                    return Ok(Some(
                        InFactSearchProofByBuiltinRule::FnApplicationInCodomain(
                            FnApplicationInCodomainBuiltinRuleProof {
                                cite_in_function_set_fact_id,
                            },
                        ),
                    ));
                }
                Err(_) => continue,
            }
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

    // Prove `element $in {x T: P(x), …}` from `element $in T` and instantiated P.
    // Example: known `a > 0` proves `a $in {x R: x > 0}`.
    fn set_builder_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetBuilder(builder) = &fact.set else {
            return Ok(None);
        };
        let mut requirement_facts = Vec::new();
        let base_in_id = self.ids.allocate_fact_id();
        requirement_facts.push(Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: base_in_id,
            element: fact.element.clone(),
            set: builder.param_set.as_ref().clone(),
            line_file: None,
        })));
        let mut subst = std::collections::HashMap::new();
        subst.insert(builder.param_binding.id, fact.element.clone());
        for defining in &builder.facts {
            let instantiated = match self.inst_quantifier_free_fact(defining, &subst) {
                Ok(qf) => crate::new_pipeline::instantiate::quantifier_free_fact_to_fact(qf),
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
        Ok(Some(InFactSearchProofByBuiltinRule::SetBuilderMembership(
            SetBuilderMembershipBuiltinRuleProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // Prove `element $in {a, b, …}` when `element = a_i` for some listed element.
    // Example: `1 $in {1, 2}`.
    fn list_set_element_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::ListSet(list_set) = &fact.set else {
            return Ok(None);
        };
        for (selected_index, listed) in list_set.list.iter().enumerate() {
            let equality = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: listed.as_ref().clone(),
                line_file: None,
            }));
            let equality_proof = self.verify_fact(&equality, verify_state.clone())?;
            if equality_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                InFactSearchProofByBuiltinRule::ListSetElementMembership(
                    ListSetElementMembershipBuiltinRuleProof {
                        selected_index,
                        equality_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }

    // Prove `A $in power_set(B)` from `A $subset B`.
    // Example: `{x R: x > 0} $in power_set(R)` via `{x R: x > 0} $subset R`.
    fn power_set_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::PowerSet(power) = &fact.set else {
            return Ok(None);
        };
        let subset = Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
            fact_id: self.ids.allocate_fact_id(),
            left: fact.element.clone(),
            right: power.set.as_ref().clone(),
            line_file: fact.line_file.clone(),
        }));
        let subset_proof = self.verify_fact(&subset, verify_state)?;
        if subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::PowerSetMembership(
            PowerSetMembershipBuiltinRuleProof { subset_proof },
        )))
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
