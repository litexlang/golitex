use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, InFact, IsNonemptySetFact, LessEqualFact, LessFact, NotEqualFact, NotInFact,
};
use crate::new_pipeline::ast::obj::{
    Abs, Add, ArithmeticOperator, Cos, Div, ExpLogOperator, Literal, Mul, Number, Obj, Pow,
    SetFormer, Sin, Sqrt, StandardSet, Sub, TrigOperator,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::parse::keywords::{EQUAL, IN};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{
    half_pi, negative_half_pi, pi_obj, zero_obj,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    evaluate_obj_to_normalized_decimal_number, objs_equal_by_rational_expression_evaluation,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `!=` facts (zero-premise routes).
pub enum NotEqualFactSearchProofByBuiltinRule {
    // Closed decimal evaluation yields unequal normals.
    // Mathematical property: if both sides evaluate to normalized decimals
    // `L` and `R` with `L != R`, then the objects are unequal.
    // Examples: `1 != 0`, `1 + 1 != 3`.
    ClosedDecimal(ClosedDecimalNotEqualBuiltinRuleProof),
    // Not-equal symmetry: prove `a != b` from a proved `b != a`.
    // Example: known `0 != x` proves `x != 0`.
    NotEqualSymmetry(NotEqualSymmetryBuiltinRuleProof),
    // List sets of different lengths are unequal.
    // Example: prove `{1} != {1, 2}`.
    ListSetDifferentLength(ListSetDifferentLengthBuiltinRuleProof),
    // Strict order implies inequality.
    // Mathematical property: `a > b` or `a < b` ⇒ `a != b`.
    // Example: known `x > 0` proves `x != 0`.
    FromKnownStrictOrder(FromKnownStrictOrderBuiltinRuleProof),
    // Nonzero standard-set membership implies `x != 0`.
    // Example: after `have a R*`, prove `a != 0`.
    FromKnownInNonzeroStandardSet(
        crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::from_known_in_signed_standard_set::FromKnownInNonzeroStandardSetBuiltinRuleProof,
    ),
    // Cosine is nonzero on the open principal tangent interval.
    // Mathematical property: `-pi/2 < y < pi/2` ⇒ `cos(y) != 0`.
    // Example: after those bounds, prove `cos(y) != 0` for `tan(y)` WD.
    CosNonzeroOnOpenHalfPi(CosNonzeroOnOpenHalfPiBuiltinRuleProof),
    // Cosine at 0 is nonzero: cos(0) = 1 ≠ 0.
    // Mathematical property: cos(0) != 0 (used by `tan(0)` WD).
    // Example: prove `cos(0) != 0`.
    CosNonzeroAtZero(CosNonzeroAtZeroBuiltinRuleProof),
    // Sine is nonzero on the open principal cotangent interval.
    // Mathematical property: `0 < y < pi` ⇒ `sin(y) != 0`.
    // Example: after those bounds, prove `sin(y) != 0` for `cot(y)` WD.
    SinNonzeroOnOpenPi(SinNonzeroOnOpenPiBuiltinRuleProof),
    // Sine at pi/2 is nonzero: sin(pi/2) = 1 ≠ 0.
    // Example: prove `sin(pi/2) != 0` for `cot(pi/2)` WD.
    SinNonzeroAtHalfPi(SinNonzeroAtHalfPiBuiltinRuleProof),
    // Absolute value is nonzero when the argument is nonzero.
    // Mathematical property: `x != 0` ⇒ `abs(x) != 0`.
    // Example: known `x != 0` proves `abs(x) != 0`.
    AbsNonzeroFromArg(AbsNonzeroFromArgBuiltinRuleProof),
    // Difference is nonzero when the operands are unequal.
    // Mathematical property: `a != b` ⇒ `a - b != 0`.
    // Example: known `x != y` proves `x - y != 0`.
    DiffNonzeroFromInequality(DiffNonzeroFromInequalityBuiltinRuleProof),
    // Empty list-set differs from a nonempty set.
    // Mathematical property: `$is_nonempty_set(A)` ⇒ `A != {}`.
    // Example: trust `$is_nonempty_set(A)`; prove `A != {}`.
    EmptySetFromNonempty(EmptySetFromNonemptyBuiltinRuleProof),
    // Positive naturals are nonzero.
    // Mathematical property: `n $in N` and `1 <= n` ⇒ `n != 0`.
    // Example: have `n N`; trust `1 <= n`; prove `n != 0`.
    ZeroFromNatAndOneLe(ZeroFromNatAndOneLeBuiltinRuleProof),
    // Nonzero base with integer exponent stays nonzero.
    // Mathematical property: `a != 0`, `n $in Z` ⇒ `a^n != 0`.
    // Example: trust `a != 0`; have `n N+`; prove `a^n != 0`.
    PowNonzeroFromBase(PowNonzeroFromBaseBuiltinRuleProof),
    // Quotient is nonzero when both factors are.
    // Mathematical property: `a != 0`, `b != 0` ⇒ `a / b != 0`.
    // Example: trust `a != 0`; trust `b != 0`; prove `a / b != 0`.
    DivNonzeroFromFactors(DivNonzeroFromFactorsBuiltinRuleProof),
    // A nonzero product has nonzero factors.
    // Mathematical property: `a * b != 0` ⇒ `a != 0` (and symmetrically).
    // Example: trust `a * b != 0`; prove `a != 0`.
    ProductComponentNonzero(ProductComponentNonzeroBuiltinRuleProof),
    // Principal square root is nonzero when the argument is strictly positive.
    // Mathematical property: `0 < x` ⇒ `sqrt(x) != 0`.
    // Example: have `a R+`; prove `sqrt(a) != 0`.
    SqrtNonzeroFromPositiveArg(SqrtNonzeroFromPositiveArgBuiltinRuleProof),
    // Square sum is nonzero when a component is nonzero.
    // Mathematical property: `a != 0` ⇒ `a^2 + b^2 != 0` (also `a*a` squares).
    // Example: trust `a != 0`; prove `a^2 + b^2 != 0`.
    SquareSumNonzeroFromComponent(SquareSumNonzeroFromComponentBuiltinRuleProof),
    // Sum is nonzero when an addend is not the negation of the other.
    // Mathematical property: `a != -b` ⇒ `a + b != 0`.
    // Example: trust `a != 0 - b`; prove `a + b != 0`.
    AddNonzeroFromNotEqualNegation(AddNonzeroFromNotEqualNegationBuiltinRuleProof),
    // Distinct objects from contradictory membership.
    // Mathematical property: `x $in A` and `y $notin A` ⇒ `x != y`.
    // Example: trust `x $in A`; trust `y $notin A`; prove `x != y`.
    MembershipContradiction(MembershipContradictionBuiltinRuleProof),
}

pub struct ClosedDecimalNotEqualBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct NotEqualSymmetryBuiltinRuleProof {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

pub struct ListSetDifferentLengthBuiltinRuleProof {}

pub struct FromKnownStrictOrderBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct CosNonzeroOnOpenHalfPiBuiltinRuleProof {}
pub struct CosNonzeroAtZeroBuiltinRuleProof {}
pub struct SinNonzeroOnOpenPiBuiltinRuleProof {}
pub struct SinNonzeroAtHalfPiBuiltinRuleProof {}

pub struct AbsNonzeroFromArgBuiltinRuleProof {
    pub arg_nonzero_proof: VerifyFactResult,
}

pub struct DiffNonzeroFromInequalityBuiltinRuleProof {
    pub operands_unequal_proof: VerifyFactResult,
}

pub struct EmptySetFromNonemptyBuiltinRuleProof {
    pub nonempty_proof: VerifyFactResult,
}

pub struct ZeroFromNatAndOneLeBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct PowNonzeroFromBaseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct DivNonzeroFromFactorsBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct ProductComponentNonzeroBuiltinRuleProof {}

pub struct SqrtNonzeroFromPositiveArgBuiltinRuleProof {
    pub arg_positive_proof: VerifyFactResult,
}

pub struct SquareSumNonzeroFromComponentBuiltinRuleProof {
    pub component_nonzero_proof: VerifyFactResult,
}

pub struct AddNonzeroFromNotEqualNegationBuiltinRuleProof {
    pub not_equal_negation_proof: VerifyFactResult,
}

pub struct MembershipContradictionBuiltinRuleProof {
    pub in_proof: VerifyFactResult,
    pub not_in_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin search for `a != b`.
    // B0: closed decimal + known strict order. A: match Obj shapes. B1: none.
    // Example: prove `1 != 0`, `x != 0` from `x > 0`, `{1} != {1, 2}`, `cos(y) != 0`.
    pub fn search_not_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        // B0 — non-shape
        if let (Some(left), Some(right)) = (
            evaluate_obj_to_normalized_decimal_number(&fact.left),
            evaluate_obj_to_normalized_decimal_number(&fact.right),
        ) {
            if left.normalized_value != right.normalized_value {
                return Ok(Some(NotEqualFactSearchProofByBuiltinRule::ClosedDecimal(
                    ClosedDecimalNotEqualBuiltinRuleProof {
                        left_normal: left.normalized_value,
                        right_normal: right.normalized_value,
                    },
                )));
            }
        }
        if let Some(cite_fact_id) = self
            .known_greater_fact_id(&fact.left, &fact.right)
            .or_else(|| self.known_less_fact_id(&fact.left, &fact.right))
        {
            return Ok(Some(
                NotEqualFactSearchProofByBuiltinRule::FromKnownStrictOrder(
                    FromKnownStrictOrderBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }
        if let Some(proof) = self.try_from_known_in_nonzero_standard_set(fact) {
            return Ok(Some(
                NotEqualFactSearchProofByBuiltinRule::FromKnownInNonzeroStandardSet(proof),
            ));
        }

        // A — shape
        match (&fact.left, &fact.right) {
            (
                Obj::SetFormer(SetFormer::ListSet(left)),
                Obj::SetFormer(SetFormer::ListSet(right)),
            ) if left.list.len() != right.list.len() => {
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::ListSetDifferentLength(
                        ListSetDifferentLengthBuiltinRuleProof {},
                    ),
                ));
            }

            (Obj::TrigOperator(TrigOperator::Cos(Cos { arg })), right)
                if is_zero_obj(right) =>
            {
                if is_zero_obj(arg.as_ref()) {
                    return Ok(Some(NotEqualFactSearchProofByBuiltinRule::CosNonzeroAtZero(
                        CosNonzeroAtZeroBuiltinRuleProof {},
                    )));
                }
                if let Some(proof) = self.cos_nonzero_on_open_half_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::TrigOperator(TrigOperator::Cos(Cos { arg })))
                if is_zero_obj(left) =>
            {
                if is_zero_obj(arg.as_ref()) {
                    return Ok(Some(NotEqualFactSearchProofByBuiltinRule::CosNonzeroAtZero(
                        CosNonzeroAtZeroBuiltinRuleProof {},
                    )));
                }
                if let Some(proof) = self.cos_nonzero_on_open_half_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }

            (Obj::TrigOperator(TrigOperator::Sin(Sin { arg })), right)
                if is_zero_obj(right) =>
            {
                if is_half_pi_obj(arg.as_ref()) {
                    return Ok(Some(
                        NotEqualFactSearchProofByBuiltinRule::SinNonzeroAtHalfPi(
                            SinNonzeroAtHalfPiBuiltinRuleProof {},
                        ),
                    ));
                }
                if let Some(proof) = self.sin_nonzero_on_open_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::TrigOperator(TrigOperator::Sin(Sin { arg })))
                if is_zero_obj(left) =>
            {
                if is_half_pi_obj(arg.as_ref()) {
                    return Ok(Some(
                        NotEqualFactSearchProofByBuiltinRule::SinNonzeroAtHalfPi(
                            SinNonzeroAtHalfPiBuiltinRuleProof {},
                        ),
                    ));
                }
                if let Some(proof) = self.sin_nonzero_on_open_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }

            // `abs(x) != 0` from `x != 0`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })),
                right,
            ) if is_zero_obj(right) => {
                if let Some(proof) =
                    self.abs_nonzero_from_arg_proof(arg.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }
            (
                left,
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })),
            ) if is_zero_obj(left) => {
                if let Some(proof) =
                    self.abs_nonzero_from_arg_proof(arg.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }

            // `a - b != 0` from `a != b`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
                zero,
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.diff_nonzero_from_inequality_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }
            (
                zero,
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.diff_nonzero_from_inequality_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }

            // `a^n != 0` from `a != 0` (integer exponent)
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })),
                right,
            ) if is_zero_obj(right) => {
                if let Some(proof) = self.pow_nonzero_from_base_proof(
                    base.as_ref(),
                    exponent.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }
            (
                left,
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })),
            ) if is_zero_obj(left) => {
                if let Some(proof) = self.pow_nonzero_from_base_proof(
                    base.as_ref(),
                    exponent.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }

            // `a / b != 0` from `a != 0` and `b != 0`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })),
                zero,
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.div_nonzero_from_factors_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }
            (
                zero,
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })),
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.div_nonzero_from_factors_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }

            // `sqrt(x) != 0` from `0 < x`
            (Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })), right)
                if is_zero_obj(right) =>
            {
                if let Some(proof) =
                    self.sqrt_nonzero_from_positive_arg_proof(arg.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) =
                    self.sqrt_nonzero_from_positive_arg_proof(arg.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }

            // `a + b != 0` from `a != -b`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })),
                zero,
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.add_nonzero_from_not_equal_negation_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }
            (
                zero,
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })),
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.add_nonzero_from_not_equal_negation_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }

            _ => {}
        }

        if let Some(proof) = self.empty_set_from_nonempty_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.zero_from_nat_and_one_le_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.product_component_nonzero_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.square_sum_nonzero_from_component_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.membership_contradiction_proof(fact, verify_state)? {
            return Ok(Some(proof));
        }

        Ok(None)
    }

    fn abs_nonzero_from_arg_proof(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: arg.clone(),
            right: zero_obj(),
            line_file: None,
        }));
        let arg_nonzero_proof = self.verify_fact(&goal, verify_state)?;
        if arg_nonzero_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(NotEqualFactSearchProofByBuiltinRule::AbsNonzeroFromArg(
            AbsNonzeroFromArgBuiltinRuleProof { arg_nonzero_proof },
        )))
    }

    fn diff_nonzero_from_inequality_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        }));
        let operands_unequal_proof = self.verify_fact(&goal, verify_state)?;
        if operands_unequal_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::DiffNonzeroFromInequality(
                DiffNonzeroFromInequalityBuiltinRuleProof {
                    operands_unequal_proof,
                },
            ),
        ))
    }

    fn cos_nonzero_on_open_half_pi_for_arg(
        &self,
        arg: &Obj,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
        let lower = negative_half_pi();
        let upper = half_pi();
        if self.known_less_fact_id(&lower, arg).is_none() {
            return None;
        }
        if self.known_less_fact_id(arg, &upper).is_none() {
            return None;
        }
        Some(NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnOpenHalfPi(
            CosNonzeroOnOpenHalfPiBuiltinRuleProof {},
        ))
    }

    fn sin_nonzero_on_open_pi_for_arg(
        &self,
        arg: &Obj,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
        let lower = zero_obj();
        let upper = pi_obj();
        if self.known_less_fact_id(&lower, arg).is_none() {
            return None;
        }
        if self.known_less_fact_id(arg, &upper).is_none() {
            return None;
        }
        Some(NotEqualFactSearchProofByBuiltinRule::SinNonzeroOnOpenPi(
            SinNonzeroOnOpenPiBuiltinRuleProof {},
        ))
    }

    fn empty_set_from_nonempty_proof(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let set = match (&fact.left, &fact.right) {
            (Obj::SetFormer(SetFormer::ListSet(list)), set) if list.list.is_empty() => set,
            (set, Obj::SetFormer(SetFormer::ListSet(list))) if list.list.is_empty() => set,
            _ => return Ok(None),
        };
        let goal = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: set.clone(),
            line_file: None,
        }));
        let nonempty_proof = self.verify_fact(&goal, verify_state)?;
        if nonempty_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::EmptySetFromNonempty(
                EmptySetFromNonemptyBuiltinRuleProof { nonempty_proof },
            ),
        ))
    }

    fn zero_from_nat_and_one_le_proof(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let n = if is_zero_obj(&fact.right) {
            &fact.left
        } else if is_zero_obj(&fact.left) {
            &fact.right
        } else {
            return Ok(None);
        };
        let in_n = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: n.clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        }));
        let one_le = Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: one_obj(),
            right: n.clone(),
            line_file: None,
        }));
        let in_proof = self.verify_fact(&in_n, verify_state.clone())?;
        if in_proof.is_failed() {
            return Ok(None);
        }
        let le_proof = self.verify_fact(&one_le, verify_state)?;
        if le_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::ZeroFromNatAndOneLe(
                ZeroFromNatAndOneLeBuiltinRuleProof {
                    proof_of_requirement_facts: vec![in_proof, le_proof],
                },
            ),
        ))
    }

    fn pow_nonzero_from_base_proof(
        &mut self,
        base: &Obj,
        exponent: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let mut proofs = Vec::new();
        let mut exponent_ok = false;
        for carrier in [StandardSet::Z, StandardSet::N, StandardSet::NPos] {
            let goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: exponent.clone(),
                set: Obj::StandardSet(carrier),
                line_file: None,
            }));
            let proof = self.verify_fact(&goal, verify_state.clone())?;
            if !proof.is_failed() {
                proofs.push(proof);
                exponent_ok = true;
                break;
            }
        }
        if !exponent_ok {
            return Ok(None);
        }
        let base_nz = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: base.clone(),
            right: zero_obj(),
            line_file: None,
        }));
        let base_proof = self.verify_fact(&base_nz, verify_state)?;
        if base_proof.is_failed() {
            return Ok(None);
        }
        proofs.push(base_proof);
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::PowNonzeroFromBase(
                PowNonzeroFromBaseBuiltinRuleProof {
                    proof_of_requirement_facts: proofs,
                },
            ),
        ))
    }

    fn div_nonzero_from_factors_proof(
        &mut self,
        numerator: &Obj,
        denominator: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let mut proofs = Vec::new();
        for factor in [numerator, denominator] {
            let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: factor.clone(),
                right: zero_obj(),
                line_file: None,
            }));
            let proof = self.verify_fact(&goal, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::DivNonzeroFromFactors(
                DivNonzeroFromFactorsBuiltinRuleProof {
                    proof_of_requirement_facts: proofs,
                },
            ),
        ))
    }

    fn product_component_nonzero_proof(
        &self,
        fact: &NotEqualFact,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
        let target = if is_zero_obj(&fact.right) {
            &fact.left
        } else if is_zero_obj(&fact.left) {
            &fact.right
        } else {
            return None;
        };
        let key = (
            AtomicName::Plain {
                name: EQUAL.into(),
            },
            false,
        );
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env.facts.known_atomic_except_equality_facts.by_prop.get(&key)
            else {
                continue;
            };
            for known in knowns {
                let AtomicFact::NotEqualFact(known_ne) = known else {
                    continue;
                };
                for (prod, other) in [
                    (&known_ne.left, &known_ne.right),
                    (&known_ne.right, &known_ne.left),
                ] {
                    if !is_zero_obj(other) {
                        continue;
                    }
                    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                        left: f1,
                        right: f2,
                    })) = prod
                    else {
                        continue;
                    };
                    if f1.as_ref().ir() == target.ir() || f2.as_ref().ir() == target.ir() {
                        return Some(
                            NotEqualFactSearchProofByBuiltinRule::ProductComponentNonzero(
                                ProductComponentNonzeroBuiltinRuleProof {},
                            ),
                        );
                    }
                }
            }
        }
        None
    }

    fn sqrt_nonzero_from_positive_arg_proof(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let goal = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero_obj(),
            right: arg.clone(),
            line_file: None,
        }));
        let arg_positive_proof = self.verify_fact(&goal, verify_state)?;
        if arg_positive_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::SqrtNonzeroFromPositiveArg(
                SqrtNonzeroFromPositiveArgBuiltinRuleProof { arg_positive_proof },
            ),
        ))
    }

    fn square_sum_nonzero_from_component_proof(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let expression = if is_zero_obj(&fact.right) {
            &fact.left
        } else if is_zero_obj(&fact.left) {
            &fact.right
        } else {
            return Ok(None);
        };
        let Some((b1, b2)) = square_sum_bases_for_not_equal(expression) else {
            return Ok(None);
        };
        for base in [b1, b2] {
            let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: base.clone(),
                right: zero_obj(),
                line_file: None,
            }));
            let proof = self.verify_fact(&goal, verify_state.clone())?;
            if !proof.is_failed() {
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::SquareSumNonzeroFromComponent(
                        SquareSumNonzeroFromComponentBuiltinRuleProof {
                            component_nonzero_proof: proof,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }

    fn add_nonzero_from_not_equal_negation_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let neg_right = negate_obj(right);
        let neg_left = negate_obj(left);
        for (a, neg_b) in [(left, &neg_right), (right, &neg_left)] {
            let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: a.clone(),
                right: neg_b.clone(),
                line_file: None,
            }));
            let proof = self.verify_fact(&goal, verify_state.clone())?;
            if !proof.is_failed() {
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::AddNonzeroFromNotEqualNegation(
                        AddNonzeroFromNotEqualNegationBuiltinRuleProof {
                            not_equal_negation_proof: proof,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }

    fn membership_contradiction_proof(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let in_key = (AtomicName::Plain { name: IN.into() }, true);
        for (member, non_member) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let member_ir = member.ir();
            let mut candidate_sets = Vec::new();
            for env in self.execution_environments_stack.iter().rev() {
                let Some(knowns) = env.facts.known_atomic_except_equality_facts.by_prop.get(&in_key)
                else {
                    continue;
                };
                for known in knowns {
                    if let AtomicFact::InFact(known_in) = known {
                        if known_in.element.ir() == member_ir {
                            candidate_sets.push(known_in.set.clone());
                        }
                    }
                }
            }
            for set in candidate_sets {
                let in_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: member.clone(),
                    set: set.clone(),
                    line_file: None,
                }));
                let in_proof = self.verify_fact(&in_goal, verify_state.clone())?;
                if in_proof.is_failed() {
                    continue;
                }
                let not_in_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: non_member.clone(),
                    set,
                    line_file: None,
                }));
                let not_in_proof = self.verify_fact(&not_in_goal, verify_state.clone())?;
                if not_in_proof.is_failed() {
                    continue;
                }
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::MembershipContradiction(
                        MembershipContradictionBuiltinRuleProof {
                            in_proof,
                            not_in_proof,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }
}

fn negate_obj(obj: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(zero_obj()),
        right: Box::new(obj.clone()),
    }))
}

fn square_sum_bases_for_not_equal(obj: &Obj) -> Option<(&Obj, &Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = obj else {
        return None;
    };
    let b1 = square_base_for_not_equal(left.as_ref())?;
    let b2 = square_base_for_not_equal(right.as_ref())?;
    Some((b1, b2))
}

fn square_base_for_not_equal(obj: &Obj) -> Option<&Obj> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) = obj {
        if matches!(
            exponent.as_ref(),
            Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
        ) {
            return Some(base.as_ref());
        }
    }
    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj {
        if left.as_ref().ir() == right.as_ref().ir() {
            return Some(left.as_ref());
        }
    }
    None
}

fn one_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".into(),
    }))
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    ) || objs_equal_by_rational_expression_evaluation(obj, &zero_obj())
}

fn is_half_pi_obj(obj: &Obj) -> bool {
    objs_equal_by_rational_expression_evaluation(obj, &half_pi())
}
