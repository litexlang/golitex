use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, IsTupleFact, LessEqualFact, LessFact, NotInFact, SubsetFact,
};
use crate::ast::names::AtomicName;
use crate::ast::obj::{
    Add, ArithmeticOperator, Cart, ComplexOperator, ExpLogOperator, FnObj, FnObjHead, FnSet,
    FunctionSpace, IntegerOperator, IntervalObj, IteratedOperator, Literal, Mul, Number, Obj,
    ObjAtIndex, OneSideInfinityIntervalObj, ProductShape, SetFormer, SetOperator, StandardSet,
    StructAndFieldAccessObj, StructObj, TrigOperator, TupleDim,
};
use crate::ast::param::SetBoundParameterList;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::match_sub_one;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::parse::keywords::IN;
use crate::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

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
    // Well-defined real trigonometry / inverse trigonometry inhabits R.
    // Mathematical property: after child WD, `sin`/`cos`/`tan`/`cot` and their
    // principal inverses land in R.
    // Example: prove `arcsin(x) $in R`, `tan(x) $in R`.
    RealTrigClosure(RealTrigClosureBuiltinRuleProof),
    // Real trig values also inhabit C via R ⊂ C.
    // Mathematical property: sin/cos/... : R → R ⊂ C.
    // Example: prove `sin(x) $in C` so Add/Pow WD over C can see trig terms.
    RealTrigInComplex(RealTrigInComplexBuiltinRuleProof),
    // Complex modulus / coordinates inhabit R.
    // Mathematical property: `C_abs(z)`, `re(z)`, `img(z)` are real after WD.
    // Example: prove `C_abs(z) $in R`, `re(z) $in R`.
    ComplexCoordinateInReal(ComplexCoordinateInRealBuiltinRuleProof),
    // Complex modulus / coordinates also inhabit C via R ⊂ C.
    // Example: prove `re(z) $in C` for Add WD of coordinate formulas.
    ComplexCoordinateInComplex(ComplexCoordinateInComplexBuiltinRuleProof),
    // Well-defined real arithmetic expressions inhabit R.
    // Mathematical property: after child WD, `+ - * / abs …` over R-carriers stay in R.
    // Example: prove `(x + y) $in R`, `abs(x) $in R`.
    RealArithmeticClosure(RealArithmeticClosureBuiltinRuleProof),
    // Native scalar codomains, after the enclosing fact's object WD succeeds:
    // sign: R → Z; gcd: (Z × Z) \ {(0, 0)} → N+; lcm: Z × Z → N;
    // exp: R → R+; factorial: N → N+. Standard-set supertypes also follow.
    NativeScalarCodomain(NativeScalarCodomainBuiltinRuleProof),
    // Membership lifts along the standard-set inclusion chain.
    // Mathematical property: if `x $in S` and `S $subset T` among standard sets,
    // then `x $in T`.
    // Example: prove `f(a) $in R` then lift to `f(a) $in C`.
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
    // Cartesian-product membership.
    // Mathematical property: `e $in cart(A1,…,An)` (n≥2) from coordinate
    // memberships (literal tuple directly; otherwise after `$is_tuple` and
    // `tuple_dim(e)=n`).
    // Example: `(1, 2) $in cart(R, Z)`.
    CartMembership(CartMembershipBuiltinRuleProof),
    // Power-set membership from subset.
    // Mathematical property: if `A $subset B`, then `A $in power_set(B)`.
    // Example: `{x R: x > 0} $subset R` proves `{x R: x > 0} $in power_set(R)`.
    PowerSetMembership(PowerSetMembershipBuiltinRuleProof),
    // Opaque struct-set membership from Cartesian/tuple carrier + `<=>:` laws.
    // Mathematical property: `e` inhabits `&Struct` when it meets the field
    // carriers (as `cart` / literal tuple components) and all instantiated
    // equivalent facts. Does not store bridges or laws.
    // Example: `(1, 2) $in &Point` after `struct Point: x R; y R`.
    StructObjMembership(StructObjMembershipBuiltinRuleProof),
    // Natural predecessor stays in N under a known lower bound of one.
    // Mathematical property: `x $in N` and `x >= 1` ⇒ `x - 1 $in N`.
    // Example: known `n $in N` and `n >= 1` prove `n - 1 $in N`.
    PredecessorInNatural(PredecessorInNaturalBuiltinRuleProof),
    // Well-defined function application lands in the function's range.
    // Mathematical property: if `f(args)` is well-defined for a function with a
    // known FnSet body, then `f(args) $in fn_range(f)`.
    // Example: a literal anonymous application belongs to that literal's range.
    AnonymousFnApplicationInFnRange(AnonymousFnApplicationInFnRangeBuiltinRuleProof),
    // Union membership from the left factor.
    // Mathematical property: `x $in A` ⇒ `x $in union(A, B)`.
    // Example: `1 $in {1}` proves `1 $in union({1}, {2})`.
    UnionMembershipFromLeft(UnionMembershipFromLeftBuiltinRuleProof),
    // Union membership from the right factor.
    // Mathematical property: `x $in B` ⇒ `x $in union(A, B)`.
    // Example: `2 $in {2}` proves `2 $in union({1}, {2})`.
    UnionMembershipFromRight(UnionMembershipFromRightBuiltinRuleProof),
    // Intersection membership from both factors.
    // Mathematical property: `x $in A` and `x $in B` ⇒ `x $in intersect(A, B)`.
    // Example: `2 $in {1, 2}` and `2 $in {2, 3}` prove `2 $in intersect({1, 2}, {2, 3})`.
    IntersectMembership(IntersectMembershipBuiltinRuleProof),
    // Set-minus membership from membership and non-membership.
    // Mathematical property: `x $in A` and `not x $in B` ⇒ `x $in set_minus(A, B)`.
    // Example: `2 $in {1, 2}` and `not 2 $in {1}` prove `2 $in set_minus({1, 2}, {1})`.
    SetMinusMembership(SetMinusMembershipBuiltinRuleProof),
    // Family-union membership from a member-set witness.
    // Mathematical property: `A $in F` and `x $in A` ⇒ `x $in family_union(F)`.
    // Example: known `{1} $in {{1}}` and `1 $in {1}` prove `1 $in family_union({{1}})`.
    FamilyUnionMembershipFromMember(FamilyUnionMembershipFromMemberBuiltinRuleProof),
    // Indexed-union membership from an index-fiber witness.
    // Mathematical property: `i $in I` and `x $in A(i)` ⇒ `x $in index_union(I, X, A)`.
    // Example: known `1 $in {1}` and `3 $in A(1)` prove `3 $in index_union({1}, N, A)`.
    IndexUnionMembershipFromIndex(IndexUnionMembershipFromIndexBuiltinRuleProof),
    // Real interval membership from carrier and endpoint bounds.
    // Mathematical property: `x $in R` plus the matching open/closed endpoint inequalities
    // prove `x $in '(a,b)` / `'[a,b]` / mixed variants.
    // Example: known `x $in R`, `0 <= x`, `x < 1` prove `x $in '[0, 1)`.
    IntervalMembership(IntervalMembershipBuiltinRuleProof),
    // One-sided real ray membership from carrier and the finite endpoint bound.
    // Example: known `x $in R` and `0 <= x` prove `x $in '[0,)`.
    OneSideInfinityIntervalMembership(OneSideInfinityIntervalMembershipBuiltinRuleProof),
    // Natural addition closure: `a $in N` and `b $in N` ⇒ `a + b $in N`.
    // Example: known `m $in N`, `n $in N` prove `m + n $in N`.
    AddInNatural(AddInNaturalBuiltinRuleProof),
    // Natural multiplication closure: `a $in N` and `b $in N` ⇒ `a * b $in N`.
    // Example: known `m $in N`, `n $in N` prove `m * n $in N`.
    MulInNatural(MulInNaturalBuiltinRuleProof),
}

// Closed decimal membership certificate (sides live on the InFact).
// Example: `2 $in N`.
pub struct ClosedNumericMembershipBuiltinRuleProof {}

// C-arithmetic closure certificate (sides live on the InFact).
// Example: `(x + 1) $in C`.
pub struct ComplexArithmeticClosureBuiltinRuleProof {}

// Real trig closure certificate (sides live on the InFact).
// Example: `arcsin(x) $in R`.
pub struct RealTrigClosureBuiltinRuleProof {}

// Real trig as complex values (sides live on the InFact).
// Example: `sin(x) $in C`.
pub struct RealTrigInComplexBuiltinRuleProof {}

// Complex modulus / re / img inhabit R.
// Example: `C_abs(z) $in R`.
pub struct ComplexCoordinateInRealBuiltinRuleProof {}

// Complex modulus / re / img inhabit C.
// Example: `re(z) $in C`.
pub struct ComplexCoordinateInComplexBuiltinRuleProof {}

pub struct RealArithmeticClosureBuiltinRuleProof {}

// Input-domain evidence lives in the enclosing atomic fact's WD proof.
// Record the native codomain even when the requested set is a proper superset.
pub struct NativeScalarCodomainBuiltinRuleProof {
    pub codomain: StandardSet,
}

// Subset-lift certificate: verify membership in a proper subset, then lift.
// Example: source_set `R`, prove `f(a) $in R` (e.g. by FnApplicationInCodomain), goal `f(a) $in C`.
pub struct StandardSetSubsetMembershipBuiltinRuleProof {
    pub source_set: StandardSet,
    pub source_membership_proof: VerifyFactResult,
}

pub struct SetBuilderMembershipBuiltinRuleProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum NativeConstantMembershipKind {
    ImaginaryUnitInComplex,
    ImaginaryUnitInNonzeroComplex,
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

// Coordinate `$in` factor proofs; optional shape/dim for non-literal elements.
pub struct CartMembershipBuiltinRuleProof {
    pub shape_and_dimension: Option<CartMembershipShapeProof>,
    pub coordinate_memberships: Vec<VerifyFactResult>,
}

pub struct CartMembershipShapeProof {
    pub is_tuple: VerifyFactResult,
    pub dimension: VerifyFactResult,
}

pub struct PowerSetMembershipBuiltinRuleProof {
    pub subset_proof: VerifyFactResult,
}

// Carrier obligations + each instantiated `<=>:` law (order matches search).
pub struct StructObjMembershipBuiltinRuleProof {
    pub carrier_obligations: Vec<VerifyFactResult>,
    pub equivalent_fact_proofs: Vec<VerifyFactResult>,
}

pub struct PredecessorInNaturalBuiltinRuleProof {
    pub in_natural_proof: AtomicExceptEqualityFactKnownProof,
    pub at_least_one_proof: AtomicExceptEqualityFactKnownProof,
}

// Zero-premise certificate: sides live on the InFact; WD already checked.
// Example: `g(1) $in fn_range(g)`.
pub struct AnonymousFnApplicationInFnRangeBuiltinRuleProof {}

pub struct UnionMembershipFromLeftBuiltinRuleProof {
    pub left_membership_proof: VerifyFactResult,
}

pub struct UnionMembershipFromRightBuiltinRuleProof {
    pub right_membership_proof: VerifyFactResult,
}

pub struct IntersectMembershipBuiltinRuleProof {
    pub left_membership_proof: VerifyFactResult,
    pub right_membership_proof: VerifyFactResult,
}

pub struct SetMinusMembershipBuiltinRuleProof {
    pub left_membership_proof: VerifyFactResult,
    pub right_non_membership_proof: VerifyFactResult,
}

pub struct FamilyUnionMembershipFromMemberBuiltinRuleProof {
    pub cite_member_set_in_family_fact_id: FactId,
    pub element_in_member_set_proof: VerifyFactResult,
}

pub struct IndexUnionMembershipFromIndexBuiltinRuleProof {
    pub cite_index_in_index_set_fact_id: FactId,
    pub element_in_fiber_proof: VerifyFactResult,
}

pub struct IntervalMembershipBuiltinRuleProof {
    pub in_real_proof: VerifyFactResult,
    pub lower_bound_proof: VerifyFactResult,
    pub upper_bound_proof: VerifyFactResult,
}

pub struct OneSideInfinityIntervalMembershipBuiltinRuleProof {
    pub in_real_proof: VerifyFactResult,
    pub endpoint_bound_proof: VerifyFactResult,
}

pub struct AddInNaturalBuiltinRuleProof {
    pub left_in_n_proof: VerifyFactResult,
    pub right_in_n_proof: VerifyFactResult,
}

pub struct MulInNaturalBuiltinRuleProof {
    pub left_in_n_proof: VerifyFactResult,
    pub right_in_n_proof: VerifyFactResult,
}


impl Runtime {
    // Builtin InFact search: dispatch by set shape first, then only try rules
    // that can apply to that shape (and element shape when needed).
    // Relative first-hit order among overlapping rules is preserved.
    // Example: `1 $in C`, `(x + 1) $in C`, `x $in C` from `x $in R`,
    // `a $in {x R: x > 0}` from `a $in R` and `a > 0`.
    pub fn search_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::StandardSet(set) => {
                self.search_in_fact_standard_set_builtin_rule(fact, set, verify_state)
            }
            Obj::SetFormer(SetFormer::SetBuilder(_)) => {
                self.set_builder_membership_proof(fact, verify_state)
            }
            Obj::ProductShape(ProductShape::Cart(_)) => {
                self.cart_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::PowerSet(_)) => {
                self.power_set_membership_proof(fact, verify_state)
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_)) => {
                self.struct_obj_membership_proof(fact, verify_state)
            }
            Obj::SetFormer(SetFormer::ListSet(_)) => {
                self.list_set_element_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::Union(_)) => {
                self.union_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::Intersect(_)) => {
                self.intersect_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::SetMinus(_)) => {
                self.set_minus_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::FamilyUnion(_)) => {
                self.family_union_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::IndexUnion(_)) => {
                self.index_union_membership_proof(fact, verify_state)
            }
            Obj::FunctionSpace(FunctionSpace::FnRange(_)) => {
                self.fn_application_in_fn_range_proof(fact)
            }
            Obj::SetFormer(SetFormer::IntervalObj(_)) => {
                self.interval_membership_proof(fact, verify_state)
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => {
                self.one_side_infinity_interval_membership_proof(fact, verify_state)
            }
            _ => Ok(None)
        }
    }

    // Standard-set `$in`: closed numeric → C-arithmetic / N-predecessor by set
    // → fn-codomain by element → subset lift → native constants by element.
    // StandardSet membership: B0 closed numeric → A match element shape → B1 cite/fn.
    // Example: prove `(x + y) $in R`, `sin(x) $in R`, `n - 1 $in N`, `i $in C`.
    fn search_in_fact_standard_set_builtin_rule(
        &mut self,
        fact: &InFact,
        set: &StandardSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        // B0 — non-shape closed evaluation
        if let Some(proof) = closed_numeric_membership_proof(fact) {
            return Ok(Some(proof));
        }

        // A — match element constructor (set gates stay as arm guards)
        match &fact.element {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(_))
            | Obj::ArithmeticOperator(ArithmeticOperator::Sub(_))
            | Obj::ArithmeticOperator(ArithmeticOperator::Neg(_))
            | Obj::ArithmeticOperator(ArithmeticOperator::Mul(_))
            | Obj::ArithmeticOperator(ArithmeticOperator::Div(_))
            | Obj::ArithmeticOperator(ArithmeticOperator::Pow(_))
            | Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
            | Obj::IntegerOperator(IntegerOperator::Mod(_))
            | Obj::IntegerOperator(IntegerOperator::Quot(_))
            | Obj::ExpLogOperator(ExpLogOperator::Sqrt(_))
            | Obj::ExpLogOperator(ExpLogOperator::Log(_))
            | Obj::ExpLogOperator(ExpLogOperator::Ln(_)) => {
                if matches!(set, StandardSet::C) {
                    if let Some(proof) = complex_arithmetic_in_c_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
                if matches!(set, StandardSet::R) {
                    if let Some(proof) = real_arithmetic_in_r_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
                // `x - 1 $in N` from `x $in N` and `x >= 1`
                if matches!(set, StandardSet::N) {
                    if let Some(proof) = self.predecessor_in_natural_proof(fact)? {
                        return Ok(Some(proof));
                    }
                    if let Some(proof) = self.add_in_natural_proof(fact, verify_state.clone())? {
                        return Ok(Some(proof));
                    }
                    if let Some(proof) = self.mul_in_natural_proof(fact, verify_state.clone())? {
                        return Ok(Some(proof));
                    }
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(_))
            | Obj::IntegerOperator(IntegerOperator::Gcd(_))
            | Obj::IntegerOperator(IntegerOperator::Lcm(_))
            | Obj::IntegerOperator(IntegerOperator::Factorial(_))
            | Obj::ExpLogOperator(ExpLogOperator::Exp(_)) => {
                if let Some(proof) = native_scalar_codomain_proof(&fact.element, set) {
                    return Ok(Some(proof));
                }
            }
            Obj::TrigOperator(TrigOperator::Sin(_))
            | Obj::TrigOperator(TrigOperator::Cos(_))
            | Obj::TrigOperator(TrigOperator::Tan(_))
            | Obj::TrigOperator(TrigOperator::Cot(_))
            | Obj::TrigOperator(TrigOperator::Arcsin(_))
            | Obj::TrigOperator(TrigOperator::Arccos(_))
            | Obj::TrigOperator(TrigOperator::Arctan(_))
            | Obj::TrigOperator(TrigOperator::Arccot(_)) => {
                if matches!(set, StandardSet::R) {
                    if let Some(proof) = real_trig_in_r_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
                if matches!(set, StandardSet::C) {
                    if let Some(proof) = real_trig_in_c_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
            }
            Obj::IteratedOperator(IteratedOperator::Sum(_))
            | Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_))
            | Obj::IteratedOperator(IteratedOperator::Product(_))
            | Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => {
                if matches!(set, StandardSet::C) {
                    if let Some(proof) = complex_arithmetic_in_c_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
                if matches!(set, StandardSet::R) {
                    if let Some(proof) = real_arithmetic_in_r_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
            }
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(_))
            | Obj::ComplexOperator(ComplexOperator::RealPart(_))
            | Obj::ComplexOperator(ComplexOperator::ImaginaryPart(_)) => {
                if matches!(set, StandardSet::R) {
                    if let Some(proof) = complex_coordinate_in_r_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
                if matches!(set, StandardSet::C) {
                    if let Some(proof) = complex_coordinate_in_c_proof(fact) {
                        return Ok(Some(proof));
                    }
                }
            }
            Obj::Literal(Literal::ImaginaryUnit(_))
            | Obj::Literal(Literal::EulerNumber(_))
            | Obj::Literal(Literal::Pi(_)) => {
                if let Some(kind) = native_constant_membership_kind(&fact.element, &fact.set) {
                    return Ok(Some(
                        InFactSearchProofByBuiltinRule::NativeConstantMembership(
                            NativeConstantMembershipBuiltinRuleProof { kind },
                        ),
                    ));
                }
            }
            _ => {}
        }

        // B1 — verify membership in a proper subset, then lift along inclusion
        if let Some(proof) = self.standard_set_subset_membership_proof(fact, verify_state)? {
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
        let Some(in_natural_proof) = self.known_in_natural_proof(base) else {
            return Ok(None);
        };
        let one = Obj::Literal(Literal::Number(Number {
            normalized_value: "1".to_string(),
        }));
        let Some(at_least_one_proof) = self.known_greater_equal_proof(base, &one) else {
            return Ok(None);
        };
        Ok(Some(InFactSearchProofByBuiltinRule::PredecessorInNatural(
            PredecessorInNaturalBuiltinRuleProof {
                in_natural_proof,
                at_least_one_proof,
            },
        )))
    }

    // Prove `x $in '(a,b)` / `'[a,b]` / mixed from `x $in R` and endpoint bounds.
    // Example: known `x $in R`, `a <= x`, `x < b` prove `x $in '[a, b)`.
    fn interval_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::IntervalObj(interval)) = &fact.set else {
            return Ok(None);
        };
        let (lower_closed, upper_closed, start, end) = match interval {
            IntervalObj::LeftOpenRightOpen(s) => (false, false, s.start.as_ref(), s.end.as_ref()),
            IntervalObj::LeftOpenRightClosed(s) => (false, true, s.start.as_ref(), s.end.as_ref()),
            IntervalObj::LeftClosedRightOpen(s) => (true, false, s.start.as_ref(), s.end.as_ref()),
            IntervalObj::LeftClosedRightClosed(s) => (true, true, s.start.as_ref(), s.end.as_ref()),
        };

        let in_real = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: Obj::StandardSet(StandardSet::R),
            line_file: None,
        }));
        let in_real_proof = self.verify_fact(&in_real, verify_state.clone())?;
        if in_real_proof.is_failed() {
            return Ok(None);
        }

        let lower = if lower_closed {
            Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: start.clone(),
                right: fact.element.clone(),
                line_file: None,
            }))
        } else {
            Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: start.clone(),
                right: fact.element.clone(),
                line_file: None,
            }))
        };
        let lower_bound_proof = self.verify_fact(&lower, verify_state.clone())?;
        if lower_bound_proof.is_failed() {
            return Ok(None);
        }

        let upper = if upper_closed {
            Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: end.clone(),
                line_file: None,
            }))
        } else {
            Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: end.clone(),
                line_file: None,
            }))
        };
        let upper_bound_proof = self.verify_fact(&upper, verify_state)?;
        if upper_bound_proof.is_failed() {
            return Ok(None);
        }

        Ok(Some(InFactSearchProofByBuiltinRule::IntervalMembership(
            IntervalMembershipBuiltinRuleProof {
                in_real_proof,
                lower_bound_proof,
                upper_bound_proof,
            },
        )))
    }

    // Prove `x $in '[a,)` / `'(a,)` / `'(,b]` / `'(,b)` from `x $in R` and one bound.
    // Example: known `x $in R` and `a <= x` prove `x $in '[a,)`.
    fn one_side_infinity_interval_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(interval)) = &fact.set else {
            return Ok(None);
        };
        // Lower* = (a,+∞)/[a,+∞); Upper* = (−∞,a)/(−∞,a].
        let (is_lower_bound, closed, endpoint) = match interval {
            OneSideInfinityIntervalObj::LowerOpen(s) => (true, false, s.start.as_ref()),
            OneSideInfinityIntervalObj::LowerClosed(s) => (true, true, s.start.as_ref()),
            OneSideInfinityIntervalObj::UpperOpen(s) => (false, false, s.start.as_ref()),
            OneSideInfinityIntervalObj::UpperClosed(s) => (false, true, s.start.as_ref()),
        };

        let in_real = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: Obj::StandardSet(StandardSet::R),
            line_file: None,
        }));
        let in_real_proof = self.verify_fact(&in_real, verify_state.clone())?;
        if in_real_proof.is_failed() {
            return Ok(None);
        }

        let bound = match (is_lower_bound, closed) {
            (true, true) => Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: endpoint.clone(),
                right: fact.element.clone(),
                line_file: None,
            })),
            (true, false) => Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: endpoint.clone(),
                right: fact.element.clone(),
                line_file: None,
            })),
            (false, true) => Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: endpoint.clone(),
                line_file: None,
            })),
            (false, false) => Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: endpoint.clone(),
                line_file: None,
            })),
        };
        let endpoint_bound_proof = self.verify_fact(&bound, verify_state)?;
        if endpoint_bound_proof.is_failed() {
            return Ok(None);
        }

        Ok(Some(
            InFactSearchProofByBuiltinRule::OneSideInfinityIntervalMembership(
                OneSideInfinityIntervalMembershipBuiltinRuleProof {
                    in_real_proof,
                    endpoint_bound_proof,
                },
            ),
        ))
    }

    // Prove `a + b $in N` from `a $in N` and `b $in N`.
    // Example: known `m $in N`, `n $in N` prove `m + n $in N`.
    fn add_in_natural_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = &fact.element
        else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: left.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        }));
        let left_in_n_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if left_in_n_proof.is_failed() {
            return Ok(None);
        }
        let right_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: right.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        }));
        let right_in_n_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_in_n_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::AddInNatural(
            AddInNaturalBuiltinRuleProof {
                left_in_n_proof,
                right_in_n_proof,
            },
        )))
    }

    // Prove `a * b $in N` from `a $in N` and `b $in N`.
    // Example: known `m $in N`, `n $in N` prove `m * n $in N`.
    fn mul_in_natural_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = &fact.element
        else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: left.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        }));
        let left_in_n_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if left_in_n_proof.is_failed() {
            return Ok(None);
        }
        let right_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: right.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        }));
        let right_in_n_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_in_n_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::MulInNatural(
            MulInNaturalBuiltinRuleProof {
                left_in_n_proof,
                right_in_n_proof,
            },
        )))
    }


    // Prove `f(args) $in fn_range(f)` when the application is already WD.
    // Mathematical property: a well-defined application of `f` is a point of the image.
    // Example: a literal anonymous application belongs to that literal's range.
    fn fn_application_in_fn_range_proof(
        &mut self,
        fact: &InFact,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::FnObj(fn_obj) = &fact.element else {
            return Ok(None);
        };
        let Obj::FunctionSpace(FunctionSpace::FnRange(fn_range)) = &fact.set else {
            return Ok(None);
        };
        let head_obj = fn_obj_head_as_obj(fn_obj.head.as_ref());
        if head_obj.ir() != fn_range.function.ir() {
            return Ok(None);
        }
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = fn_range.function.as_ref() else {
            return Ok(None);
        };
        let body = &anon.body;
        if fn_obj.body.len() != 1 {
            return Ok(None);
        }
        let arg_count = fn_obj.body[0].len();
        let expected = set_bound_parameter_count(&body.set_bound_parameters);
        if arg_count != expected {
            return Ok(None);
        }
        Ok(Some(
            InFactSearchProofByBuiltinRule::AnonymousFnApplicationInFnRange(
                AnonymousFnApplicationInFnRangeBuiltinRuleProof {},
            ),
        ))
    }

    // Prove `element $in target` from `element $in source` with source ⊂ target.
    // Source membership is verified under the same builtin / known flags as
    // `verify_state` (so by_known can prove the declared `$in R` when lifting
    // to `$in C`). Deep forall / rewrite / WD-store stay off to avoid search
    // blow-up across every proper subset.
    // Example: `distance_sq(q, p) $in C` via proving `distance_sq(q, p) $in R`.
    fn standard_set_subset_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::StandardSet(target) = &fact.set else {
            return Ok(None);
        };
        let mut source_state = verify_state.clone();
        source_state.can_use_def_and_known_forall_and_known_strategy = false;
        source_state.can_use_rewrite = false;
        source_state.store_well_defined_fact = false;
        for source in proper_subsets_in_membership_proof_order(target) {
            let probe = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: fact.element.clone(),
                set: Obj::StandardSet(source.clone()),
                line_file: None,
            }));
            let source_membership_proof = self.verify_fact(&probe, source_state.clone())?;
            if source_membership_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                InFactSearchProofByBuiltinRule::StandardSetSubsetMembership(
                    StandardSetSubsetMembershipBuiltinRuleProof {
                        source_set: source,
                        source_membership_proof,
                    },
                ),
            ));
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
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &fact.set else {
            return Ok(None);
        };
        let mut requirement_facts = Vec::new();
        let base_in_id = self.global_ids.allocate_fact_id();
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
                Ok(qf) => crate::instantiate::quantifier_free_fact_to_fact(qf),
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
        let Obj::SetFormer(SetFormer::ListSet(list_set)) = &fact.set else {
            return Ok(None);
        };
        for (selected_index, listed) in list_set.list.iter().enumerate() {
            let equality = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
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
        let Obj::SetOperator(SetOperator::PowerSet(power)) = &fact.set else {
            return Ok(None);
        };
        let subset = Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
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

    // Prove `e $in cart(A1,…,An)` (n≥2).
    // Literal tuple: each `ai $in Ai`.
    // Otherwise: `$is_tuple(e)`, `tuple_dim(e)=n`, and each `e[i] $in Ai`.
    // Example: `(1, 2) $in cart(R, Z)`.
    fn cart_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::ProductShape(ProductShape::Cart(cart)) = &fact.set else {
            return Ok(None);
        };
        if cart.args.len() < 2 {
            return Ok(None);
        }

        let (shape_and_dimension, coordinates): (Option<CartMembershipShapeProof>, Vec<Obj>) =
            match &fact.element {
                Obj::ProductShape(ProductShape::Tuple(tuple)) if tuple.args.len() == cart.args.len() => (
                    None,
                    tuple.args.iter().map(|a| a.as_ref().clone()).collect(),
                ),
                Obj::ProductShape(ProductShape::Tuple(_)) => return Ok(None),
                _ => {
                    let is_tuple_fact = Fact::AtomicFact(AtomicFact::IsTupleFact(IsTupleFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        set: fact.element.clone(),
                        line_file: fact.line_file.clone(),
                    }));
                    let is_tuple = self.verify_fact(&is_tuple_fact, verify_state.clone())?;
                    if is_tuple.is_failed() {
                        return Ok(None);
                    }
                    let dimension_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: Obj::ProductShape(ProductShape::TupleDim(TupleDim {
                            arg: Box::new(fact.element.clone()),
                        })),
                        right: Obj::Literal(Literal::Number(Number {
                            normalized_value: cart.args.len().to_string(),
                        })),
                        line_file: fact.line_file.clone(),
                    }));
                    let dimension = self.verify_fact(&dimension_fact, verify_state.clone())?;
                    if dimension.is_failed() {
                        return Ok(None);
                    }
                    let coordinates = (0..cart.args.len())
                        .map(|index| {
                            Obj::ProductShape(ProductShape::ObjAtIndex(ObjAtIndex {
                                obj: Box::new(fact.element.clone()),
                                index: Box::new(Obj::Literal(Literal::Number(Number {
                                    normalized_value: (index + 1).to_string(),
                                }))),
                            }))
                        })
                        .collect();
                    (
                        Some(CartMembershipShapeProof {
                            is_tuple,
                            dimension,
                        }),
                        coordinates,
                    )
                }
            };

        let mut coordinate_memberships = Vec::with_capacity(cart.args.len());
        for (coordinate, factor) in coordinates.iter().zip(cart.args.iter()) {
            let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: coordinate.clone(),
                set: factor.as_ref().clone(),
                line_file: fact.line_file.clone(),
            }));
            let proof = self.verify_fact(&membership, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            coordinate_memberships.push(proof);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::CartMembership(
            CartMembershipBuiltinRuleProof {
                shape_and_dimension,
                coordinate_memberships,
            },
        )))
    }

    // Prove `e $in &Struct` from field carriers + instantiated `<=>:` laws.
    // Literal tuple: each component `$in Ti`. Otherwise: `e $in cart(T1,…,Tn)`.
    // Example: `(1, 2) $in &Point` after `struct Point: x R; y R`.
    fn struct_obj_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(struct_obj)) = &fact.set else {
            return Ok(None);
        };
        let Some((def, mut subst)) = self.struct_def_and_header_subst(struct_obj) else {
            return Ok(None);
        };
        if def.fields.len() < 2 {
            return Ok(None);
        }

        let field_values: Vec<Obj> = match &fact.element {
            Obj::ProductShape(ProductShape::Tuple(tuple)) if tuple.args.len() == def.fields.len() => {
                tuple.args.iter().map(|a| a.as_ref().clone()).collect()
            }
            Obj::ProductShape(ProductShape::Tuple(_)) => return Ok(None),
            _ => (0..def.fields.len())
                .map(|index| {
                    Obj::ProductShape(ProductShape::ObjAtIndex(ObjAtIndex {
                        obj: Box::new(fact.element.clone()),
                        index: Box::new(Obj::Literal(Literal::Number(Number {
                            normalized_value: (index + 1).to_string(),
                        }))),
                    }))
                })
                .collect(),
        };
        for (field, value) in def.fields.iter().zip(field_values.iter()) {
            subst.insert(field.binding.id, value.clone());
        }

        let mut field_types = Vec::with_capacity(def.fields.len());
        for field in &def.fields {
            let Ok(ty) = self.inst_obj(&field.field_type, &subst) else {
                return Ok(None);
            };
            field_types.push(ty);
        }

        let mut carrier_obligations = Vec::new();
        match &fact.element {
            Obj::ProductShape(ProductShape::Tuple(_)) => {
                for (value, field_type) in field_values.iter().zip(field_types.iter()) {
                    let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: value.clone(),
                        set: field_type.clone(),
                        line_file: fact.line_file.clone(),
                    }));
                    let proof = self.verify_fact(&membership, verify_state.clone())?;
                    if proof.is_failed() {
                        return Ok(None);
                    }
                    carrier_obligations.push(proof);
                }
            }
            _ => {
                let cart = Obj::ProductShape(ProductShape::Cart(Cart {
                    args: field_types.iter().cloned().map(Box::new).collect(),
                }));
                let cart_membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: fact.element.clone(),
                    set: cart,
                    line_file: fact.line_file.clone(),
                }));
                let proof = self.verify_fact(&cart_membership, verify_state.clone())?;
                if proof.is_failed() {
                    return Ok(None);
                }
                carrier_obligations.push(proof);
            }
        }

        let mut equivalent_fact_proofs = Vec::with_capacity(def.equivalent_facts.len());
        for law in &def.equivalent_facts {
            let Ok(instantiated) = self.inst_fact(law, &subst) else {
                return Ok(None);
            };
            let proof = self.verify_fact(&instantiated, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            equivalent_fact_proofs.push(proof);
        }

        Ok(Some(InFactSearchProofByBuiltinRule::StructObjMembership(
            StructObjMembershipBuiltinRuleProof {
                carrier_obligations,
                equivalent_fact_proofs,
            },
        )))
    }

    fn struct_def_and_header_subst(
        &self,
        struct_obj: &StructObj,
    ) -> Option<(crate::ast::stmt::DefStructStmt, HashMap<IdentifierId, Obj>)> {
        let def = self.def_struct_visible(&struct_obj.name)?.clone();
        let expected = def
            .param_def_with_dom
            .as_ref()
            .map(|(p, _)| p.groups.iter().map(|g| g.params.len()).sum::<usize>())
            .unwrap_or(0);
        if expected != struct_obj.params.len() || def.fields.len() < 2 {
            return None;
        }
        let mut subst = HashMap::new();
        if let Some((params, _)) = &def.param_def_with_dom {
            let mut arg_index = 0;
            for group in &params.groups {
                for binding in &group.params {
                    let arg = struct_obj.params.get(arg_index)?;
                    subst.insert(binding.id, arg.clone());
                    arg_index += 1;
                }
            }
        }
        Some((def, subst))
    }

    // Prove `x $in union(A, B)` from `x $in A` or `x $in B` (separate rules).
    fn union_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Union(union)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: union.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if !left_proof.is_failed() {
            return Ok(Some(InFactSearchProofByBuiltinRule::UnionMembershipFromLeft(
                UnionMembershipFromLeftBuiltinRuleProof {
                    left_membership_proof: left_proof,
                },
            )));
        }
        let right_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: union.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::UnionMembershipFromRight(
            UnionMembershipFromRightBuiltinRuleProof {
                right_membership_proof: right_proof,
            },
        )))
    }

    // Prove `x $in intersect(A, B)` from both memberships.
    fn intersect_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Intersect(intersect)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: intersect.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if left_proof.is_failed() {
            return Ok(None);
        }
        let right_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: intersect.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::IntersectMembership(
            IntersectMembershipBuiltinRuleProof {
                left_membership_proof: left_proof,
                right_membership_proof: right_proof,
            },
        )))
    }

    // Prove `x $in set_minus(A, B)` from `x $in A` and `not x $in B`.
    fn set_minus_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::SetMinus(set_minus)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: set_minus.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if left_proof.is_failed() {
            return Ok(None);
        }
        let right_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: set_minus.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(InFactSearchProofByBuiltinRule::SetMinusMembership(
            SetMinusMembershipBuiltinRuleProof {
                left_membership_proof: left_proof,
                right_non_membership_proof: right_proof,
            },
        )))
    }

    // Prove `x $in family_union(F)` from a known `A $in F` and a proved `x $in A`.
    fn family_union_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::FamilyUnion(family_union)) = &fact.set else {
            return Ok(None);
        };
        let family = family_union.left.as_ref();
        let family_ir = family.ir();
        let key = (AtomicName::Plain { name: IN.into() }, true);
        let mut candidates: Vec<(FactId, Obj)> = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::InFact(known_in) = known {
                    if known_in.set.ir() == family_ir {
                        candidates.push((known_in.fact_id, known_in.element.clone()));
                    }
                }
            }
        }
        for (cite_member_set_in_family_fact_id, member_set) in candidates {
            let element_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: fact.element.clone(),
                set: member_set,
                line_file: None,
            }));
            let element_in_member_set_proof =
                self.verify_fact(&element_goal, verify_state.clone())?;
            if element_in_member_set_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                InFactSearchProofByBuiltinRule::FamilyUnionMembershipFromMember(
                    FamilyUnionMembershipFromMemberBuiltinRuleProof {
                        cite_member_set_in_family_fact_id,
                        element_in_member_set_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }

    // Prove `x $in index_union(I, X, A)` from a known `i $in I` and a proved `x $in A(i)`.
    fn index_union_membership_proof(
        &mut self,
        fact: &InFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::IndexUnion(index_union)) = &fact.set else {
            return Ok(None);
        };
        let index_set_ir = index_union.index_set.as_ref().ir();
        let key = (AtomicName::Plain { name: IN.into() }, true);
        let mut candidates: Vec<(FactId, Obj)> = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::InFact(known_in) = known {
                    if known_in.set.ir() == index_set_ir {
                        candidates.push((known_in.fact_id, known_in.element.clone()));
                    }
                }
            }
        }
        for (cite_index_in_index_set_fact_id, index) in candidates {
            let Some(fiber) = apply_fn_one_arg(index_union.family_fn.as_ref(), index) else {
                continue;
            };
            let fiber_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: fact.element.clone(),
                set: fiber,
                line_file: None,
            }));
            let element_in_fiber_proof = self.verify_fact(&fiber_goal, verify_state.clone())?;
            if element_in_fiber_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                InFactSearchProofByBuiltinRule::IndexUnionMembershipFromIndex(
                    IndexUnionMembershipFromIndexBuiltinRuleProof {
                        cite_index_in_index_set_fact_id,
                        element_in_fiber_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }
}

fn fn_obj_head_as_obj(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(a) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(a.as_ref().clone()))
        }
        FnObjHead::FieldAccess(v) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(v.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(v) => Obj::InstantiatedTemplateObj(v.clone()),
    }
}

fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

fn apply_fn_one_arg(f: &Obj, arg: Obj) -> Option<Obj> {
    match f {
        Obj::Identifier(id) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(id.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::FnObj(existing) => {
            let mut body = existing.body.clone();
            body.push(vec![Box::new(arg)]);
            Some(Obj::FnObj(FnObj {
                head: existing.head.clone(),
                body,
            }))
        }
        Obj::FunctionSpace(crate::ast::obj::FunctionSpace::AnonymousFn(af)) => {
            Some(Obj::FnObj(FnObj {
                head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(af.clone()))),
                body: vec![vec![Box::new(arg)]],
            }))
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(fa)) => {
            Some(Obj::FnObj(FnObj {
                head: Box::new(FnObjHead::FieldAccess(fa.clone())),
                body: vec![vec![Box::new(arg)]],
            }))
        }
        Obj::InstantiatedTemplateObj(t) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::InstantiatedTemplateObj(t.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        _ => None,
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

pub(super) fn normalized_decimal_inhabits_standard_set(v: &str, set: &StandardSet) -> bool {
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

// The normal verify pipeline has already checked the constructor's domain.
// This leaf uses only that WD evidence and standard-set inclusion, never a
// speculative membership search (which would cycle back to the same goal).
fn native_scalar_codomain_proof(
    element: &Obj,
    target: &StandardSet,
) -> Option<InFactSearchProofByBuiltinRule> {
    let codomain = match element {
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(_)) => StandardSet::Z,
        Obj::IntegerOperator(IntegerOperator::Gcd(_))
        | Obj::IntegerOperator(IntegerOperator::Factorial(_)) => StandardSet::NPos,
        Obj::IntegerOperator(IntegerOperator::Lcm(_)) => StandardSet::N,
        Obj::ExpLogOperator(ExpLogOperator::Exp(_)) => StandardSet::RPos,
        _ => return None,
    };
    standard_set_is_subset_eq(&codomain, target).then_some(
        InFactSearchProofByBuiltinRule::NativeScalarCodomain(
            NativeScalarCodomainBuiltinRuleProof { codomain },
        ),
    )
}

// WD already forces complex operand domains; Add/Sub/Mul/... are closed in C.
// Example: prove `(x + 1) * (x - 1) $in C`.
fn complex_arithmetic_in_c_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::C) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Sub(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Neg(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Mul(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Div(_))
        | Obj::IntegerOperator(IntegerOperator::Mod(_))
        | Obj::IntegerOperator(IntegerOperator::Quot(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Pow(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
        | Obj::ExpLogOperator(ExpLogOperator::Sqrt(_))
        | Obj::ExpLogOperator(ExpLogOperator::Log(_))
        | Obj::ExpLogOperator(ExpLogOperator::Ln(_))
        | Obj::IteratedOperator(IteratedOperator::Sum(_))
        | Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_))
        | Obj::IteratedOperator(IteratedOperator::Product(_))
        | Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => Some(
            InFactSearchProofByBuiltinRule::ComplexArithmeticClosure(
                ComplexArithmeticClosureBuiltinRuleProof {},
            ),
        ),
        _ => None,
    }
}

// WD already forces real operand domains; Add/Sub/Mul/Abs/... are closed in R.
// Example: prove `(x + y) $in R`, `abs(x) $in R`.
fn real_arithmetic_in_r_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::R) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Sub(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Neg(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Mul(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Div(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Pow(_))
        | Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
        | Obj::ExpLogOperator(ExpLogOperator::Sqrt(_))
        | Obj::ExpLogOperator(ExpLogOperator::Log(_))
        | Obj::ExpLogOperator(ExpLogOperator::Ln(_))
        | Obj::IteratedOperator(IteratedOperator::Sum(_))
        | Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_))
        | Obj::IteratedOperator(IteratedOperator::Product(_))
        | Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => Some(
            InFactSearchProofByBuiltinRule::RealArithmeticClosure(
                RealArithmeticClosureBuiltinRuleProof {},
            ),
        ),
        _ => None,
    }
}

// WD already forces real domains for these forms; they inhabit R.
// Example: prove `sin(x) $in R`, `arccos(x) $in R`.
fn real_trig_in_r_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::R) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::TrigOperator(TrigOperator::Sin(_))
        | Obj::TrigOperator(TrigOperator::Cos(_))
        | Obj::TrigOperator(TrigOperator::Tan(_))
        | Obj::TrigOperator(TrigOperator::Cot(_))
        | Obj::TrigOperator(TrigOperator::Arcsin(_))
        | Obj::TrigOperator(TrigOperator::Arccos(_))
        | Obj::TrigOperator(TrigOperator::Arctan(_))
        | Obj::TrigOperator(TrigOperator::Arccot(_)) => Some(InFactSearchProofByBuiltinRule::RealTrigClosure(
            RealTrigClosureBuiltinRuleProof {},
        )),
        _ => None,
    }
}

// Real trig values inhabit C (R ⊂ C). Example: prove `sin(x) $in C`.
fn real_trig_in_c_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::C) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::TrigOperator(TrigOperator::Sin(_))
        | Obj::TrigOperator(TrigOperator::Cos(_))
        | Obj::TrigOperator(TrigOperator::Tan(_))
        | Obj::TrigOperator(TrigOperator::Cot(_))
        | Obj::TrigOperator(TrigOperator::Arcsin(_))
        | Obj::TrigOperator(TrigOperator::Arccos(_))
        | Obj::TrigOperator(TrigOperator::Arctan(_))
        | Obj::TrigOperator(TrigOperator::Arccot(_)) => {
            Some(InFactSearchProofByBuiltinRule::RealTrigInComplex(
                RealTrigInComplexBuiltinRuleProof {},
            ))
        }
        _ => None,
    }
}

// C_abs / re / img inhabit R after their complex-arg WD.
// Example: prove `C_abs(z) $in R`, `re(z) $in R`.
fn complex_coordinate_in_r_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::R) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(_))
        | Obj::ComplexOperator(ComplexOperator::RealPart(_))
        | Obj::ComplexOperator(ComplexOperator::ImaginaryPart(_)) => {
            Some(InFactSearchProofByBuiltinRule::ComplexCoordinateInReal(
                ComplexCoordinateInRealBuiltinRuleProof {},
            ))
        }
        _ => None,
    }
}

// Same coordinates also inhabit C via R ⊂ C.
fn complex_coordinate_in_c_proof(fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
    let Obj::StandardSet(StandardSet::C) = &fact.set else {
        return None;
    };
    match &fact.element {
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(_))
        | Obj::ComplexOperator(ComplexOperator::RealPart(_))
        | Obj::ComplexOperator(ComplexOperator::ImaginaryPart(_)) => {
            Some(InFactSearchProofByBuiltinRule::ComplexCoordinateInComplex(
                ComplexCoordinateInComplexBuiltinRuleProof {},
            ))
        }
        _ => None,
    }
}

fn proper_subsets_in_membership_proof_order(target: &StandardSet) -> Vec<StandardSet> {
    // Larger / nearer carriers first so verify-based lift hits soon (e.g. R before N for C).
    [
        StandardSet::R,
        StandardSet::Q,
        StandardSet::Z,
        StandardSet::N,
        StandardSet::RStar,
        StandardSet::RPos,
        StandardSet::RNeg,
        StandardSet::QStar,
        StandardSet::QPos,
        StandardSet::QNeg,
        StandardSet::ZStar,
        StandardSet::ZNeg,
        StandardSet::NPos,
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
        (Obj::Literal(Literal::ImaginaryUnit(_)), Obj::StandardSet(StandardSet::C)) => {
            Some(NativeConstantMembershipKind::ImaginaryUnitInComplex)
        }
        (Obj::Literal(Literal::ImaginaryUnit(_)), Obj::StandardSet(StandardSet::CStar)) => {
            Some(NativeConstantMembershipKind::ImaginaryUnitInNonzeroComplex)
        }
        (Obj::Literal(Literal::EulerNumber(_)), Obj::StandardSet(StandardSet::RPos)) => {
            Some(NativeConstantMembershipKind::EulerNumberInPositiveReal)
        }
        (Obj::Literal(Literal::EulerNumber(_)), Obj::StandardSet(StandardSet::R)) => {
            Some(NativeConstantMembershipKind::EulerNumberInReal)
        }
        (Obj::Literal(Literal::EulerNumber(_)), Obj::StandardSet(StandardSet::C)) => {
            Some(NativeConstantMembershipKind::EulerNumberInComplex)
        }
        (Obj::Literal(Literal::Pi(_)), Obj::StandardSet(StandardSet::RPos)) => {
            Some(NativeConstantMembershipKind::PiInPositiveReal)
        }
        (Obj::Literal(Literal::Pi(_)), Obj::StandardSet(StandardSet::R)) => {
            Some(NativeConstantMembershipKind::PiInReal)
        }
        (Obj::Literal(Literal::Pi(_)), Obj::StandardSet(StandardSet::C)) => {
            Some(NativeConstantMembershipKind::PiInComplex)
        }
        _ => None,
    }
}
