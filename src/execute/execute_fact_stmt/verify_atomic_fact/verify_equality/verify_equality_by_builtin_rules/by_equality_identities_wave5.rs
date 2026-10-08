//! Stage B wave 5: quot / gcd / lcm / factorial equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Factorial, Gcd, IntegerOperator, Lcm, Literal, Mul, Number, Obj,
    Quot,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// --- quot ---

// Builtin QuotByOne: quot(a, 1) = a.
// Example: have a Z; quot(a, 1) = a.
pub struct QuotByOneBuiltinRuleProof {}

// Builtin QuotSelfOne: quot(a, a) = 1 when a in N+.
// Example: have a N+; quot(a, a) = 1.
pub struct QuotSelfOneBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- lcm ---

// Builtin LcmCommutative: lcm(a, b) = lcm(b, a).
// Example: have a Z; have b Z; lcm(a, b) = lcm(b, a).
pub struct LcmCommutativeBuiltinRuleProof {}

// Builtin LcmIdempotentAbs: lcm(a, a) = abs(a).
// Example: have a Z; lcm(a, a) = abs(a).
pub struct LcmIdempotentAbsBuiltinRuleProof {}

// Parent equality WD owns integer operands and the nonzero abs modulus.
// Example: a in Z*, b in Z implies lcm(a,b)%abs(a)=0.
pub struct LcmLeftAbsDivisibilityProof {}
impl LcmLeftAbsDivisibilityProof {
    pub fn new() -> Self {
        Self {}
    }
}

// Example: a in Z, b in Z* implies lcm(a,b)%abs(b)=0.
pub struct LcmRightAbsDivisibilityProof {}
impl LcmRightAbsDivisibilityProof {
    pub fn new() -> Self {
        Self {}
    }
}

// --- gcd ---

// Builtin GcdCommutative: gcd(a, b) = gcd(b, a).
// Example: have a Z; have b Z; trust a != 0; gcd(a, b) = gcd(b, a).
pub struct GcdCommutativeBuiltinRuleProof {}

// Builtin GcdIdempotentAbs: gcd(a, a) = abs(a).
// Example: have a Z; trust a != 0; gcd(a, a) = abs(a).
pub struct GcdIdempotentAbsBuiltinRuleProof {}

// Builtin GcdRightZeroAbs: gcd(a, 0) = abs(a) when a != 0.
// Example: have a Z; trust a != 0; gcd(a, 0) = abs(a).
pub struct GcdRightZeroAbsBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin GcdLeftZeroAbs: gcd(0, a) = abs(a) when a != 0.
// Example: have a Z; trust a != 0; gcd(0, a) = abs(a).
pub struct GcdLeftZeroAbsBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- factorial ---

// Builtin FactorialSuccessor: factorial(n+1) = (n+1) * factorial(n) for n in N.
// Example: have n N; trust n! $in N; (n+1)! = (n+1) * n!.
// (Narrow trust: symbolic n! currently lacks a carrier for mul WD.)
pub struct FactorialSuccessorBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave5BuiltinRuleProof {
    QuotByOne(QuotByOneBuiltinRuleProof),
    QuotSelfOne(QuotSelfOneBuiltinRuleProof),
    LcmCommutative(LcmCommutativeBuiltinRuleProof),
    LcmIdempotentAbs(LcmIdempotentAbsBuiltinRuleProof),
    LcmLeftAbsDivisibility(LcmLeftAbsDivisibilityProof),
    LcmRightAbsDivisibility(LcmRightAbsDivisibilityProof),
    GcdCommutative(GcdCommutativeBuiltinRuleProof),
    GcdIdempotentAbs(GcdIdempotentAbsBuiltinRuleProof),
    GcdRightZeroAbs(GcdRightZeroAbsBuiltinRuleProof),
    GcdLeftZeroAbs(GcdLeftZeroAbsBuiltinRuleProof),
    FactorialSuccessor(FactorialSuccessorBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave5(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave5BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(p) = self.try_quot_by_one(left, right)? {
                return Ok(Some(EqualityIdentitiesWave5BuiltinRuleProof::QuotByOne(p)));
            }
            if let Some(p) = self.try_quot_self_one(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave5BuiltinRuleProof::QuotSelfOne(
                    p,
                )));
            }
            if let Some(p) = self.try_lcm_commutative(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::LcmCommutative(p),
                ));
            }
            if let Some(p) = self.try_lcm_idempotent_abs(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::LcmIdempotentAbs(p),
                ));
            }
            // A well-defined lcm is a multiple of each nonzero input's abs.
            // Match only the selected operand; unrelated divisors do not qualify.
            if is_zero_obj(right) {
                if let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = left {
                    if let (Some((a, b)), Some(divisor)) =
                        (match_lcm(&rem.left), match_abs(&rem.right))
                    {
                        if divisor.ir() == a.ir() {
                            return Ok(Some(
                                EqualityIdentitiesWave5BuiltinRuleProof::LcmLeftAbsDivisibility(
                                    LcmLeftAbsDivisibilityProof::new(),
                                ),
                            ));
                        }
                        if divisor.ir() == b.ir() {
                            return Ok(Some(
                                EqualityIdentitiesWave5BuiltinRuleProof::LcmRightAbsDivisibility(
                                    LcmRightAbsDivisibilityProof::new(),
                                ),
                            ));
                        }
                    }
                }
            }
            if let Some(p) = self.try_gcd_commutative(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::GcdCommutative(p),
                ));
            }
            if let Some(p) = self.try_gcd_idempotent_abs(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::GcdIdempotentAbs(p),
                ));
            }
            if let Some(p) = self.try_gcd_right_zero_abs(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::GcdRightZeroAbs(p),
                ));
            }
            if let Some(p) = self.try_gcd_left_zero_abs(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::GcdLeftZeroAbs(p),
                ));
            }
            if let Some(p) = self.try_factorial_successor(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave5BuiltinRuleProof::FactorialSuccessor(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_quot_by_one(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<QuotByOneBuiltinRuleProof>> {
        let Some((dividend, divisor)) = match_quot(left) else {
            return Ok(None);
        };
        if is_one_obj(divisor) && dividend.ir() == right.ir() {
            return Ok(Some(QuotByOneBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_quot_self_one(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<QuotSelfOneBuiltinRuleProof>> {
        let Some((dividend, divisor)) = match_quot(left) else {
            return Ok(None);
        };
        if dividend.ir() != divisor.ir() || !is_one_obj(right) {
            return Ok(None);
        }
        // quot WD needs divisor in N+; N+ does not auto-prove != 0 today.
        let proof = self.verify_in_positive_natural(divisor, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(QuotSelfOneBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_lcm_commutative(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<LcmCommutativeBuiltinRuleProof>> {
        let Some((a, b)) = match_lcm(left) else {
            return Ok(None);
        };
        let Some((c, d)) = match_lcm(right) else {
            return Ok(None);
        };
        if a.ir() == d.ir() && b.ir() == c.ir() && a.ir() != b.ir() {
            return Ok(Some(LcmCommutativeBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_lcm_idempotent_abs(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<LcmIdempotentAbsBuiltinRuleProof>> {
        let Some((a, b)) = match_lcm(left) else {
            return Ok(None);
        };
        if a.ir() != b.ir() {
            return Ok(None);
        }
        let Some(abs_arg) = match_abs(right) else {
            return Ok(None);
        };
        if a.ir() == abs_arg.ir() {
            return Ok(Some(LcmIdempotentAbsBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_gcd_commutative(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<GcdCommutativeBuiltinRuleProof>> {
        let Some((a, b)) = match_gcd(left) else {
            return Ok(None);
        };
        let Some((c, d)) = match_gcd(right) else {
            return Ok(None);
        };
        if a.ir() == d.ir() && b.ir() == c.ir() && a.ir() != b.ir() {
            return Ok(Some(GcdCommutativeBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_gcd_idempotent_abs(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<GcdIdempotentAbsBuiltinRuleProof>> {
        let Some((a, b)) = match_gcd(left) else {
            return Ok(None);
        };
        if a.ir() != b.ir() {
            return Ok(None);
        }
        let Some(abs_arg) = match_abs(right) else {
            return Ok(None);
        };
        if a.ir() == abs_arg.ir() {
            return Ok(Some(GcdIdempotentAbsBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_gcd_right_zero_abs(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GcdRightZeroAbsBuiltinRuleProof>> {
        let Some((a, b)) = match_gcd(left) else {
            return Ok(None);
        };
        if !is_zero_obj(b) {
            return Ok(None);
        }
        let Some(abs_arg) = match_abs(right) else {
            return Ok(None);
        };
        if a.ir() != abs_arg.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonzero(a, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(GcdRightZeroAbsBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_gcd_left_zero_abs(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GcdLeftZeroAbsBuiltinRuleProof>> {
        let Some((a, b)) = match_gcd(left) else {
            return Ok(None);
        };
        if !is_zero_obj(a) {
            return Ok(None);
        }
        let Some(abs_arg) = match_abs(right) else {
            return Ok(None);
        };
        if b.ir() != abs_arg.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonzero(b, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(GcdLeftZeroAbsBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_factorial_successor(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FactorialSuccessorBuiltinRuleProof>> {
        let Some(arg) = match_factorial(left) else {
            return Ok(None);
        };
        let Some(n) = match_plus_one(arg) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: m1,
            right: m2,
        })) = right
        else {
            return Ok(None);
        };
        let candidates = [(m1.as_ref(), m2.as_ref()), (m2.as_ref(), m1.as_ref())];
        for (succ_side, fact_side) in candidates {
            if match_plus_one(succ_side).map(|x| x.ir()) != Some(n.ir()) {
                continue;
            }
            let Some(inner) = match_factorial(fact_side) else {
                continue;
            };
            if inner.ir() != n.ir() {
                continue;
            }
            let proof = self.verify_in_natural(n, verify_state.clone())?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(FactorialSuccessorBuiltinRuleProof {
                proof_of_requirement_facts: vec![proof],
            }));
        }
        Ok(None)
    }
}

fn match_quot(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Quot(Quot { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_gcd(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_lcm(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Lcm(Lcm { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_factorial(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Factorial(Factorial { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_plus_one(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            if is_one_obj(right.as_ref()) {
                Some(left.as_ref())
            } else if is_one_obj(left.as_ref()) {
                Some(right.as_ref())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}
