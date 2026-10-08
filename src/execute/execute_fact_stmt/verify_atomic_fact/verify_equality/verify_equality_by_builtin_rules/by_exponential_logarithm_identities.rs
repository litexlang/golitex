//! Fixed exp/ln identities and guarded inverse relations.
use super::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::ast::fact::{EqualFact, Fact, InFact};
use crate::ast::obj::{Add, ArithmeticOperator as A, Div, Exp, ExpLogOperator as E, Ln, Log, Obj, Pow, StandardSet, Sub};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
use crate::runtime::{Runtime, RuntimeResult};

pub enum ExponentialLogarithmIdentityProof {
    ExpDifference(ExpDifferenceProof),
    LnProduct(LnProductProof),
    LnQuotient(LnQuotientProof),
    ExpInjective(ExpInjectiveProof),
    LnInjective(LnInjectiveProof),
    LogFromKnownPower(LogFromKnownPowerProof),
    PowerFromKnownLog(PowerFromKnownLogProof),
}
// Parent equality WD owns all real/positive arguments and partial operations.
pub struct ExpDifferenceProof;
pub struct LnProductProof;
pub struct LnQuotientProof;
pub struct ExpInjectiveProof {
    pub left_real: VerifyFactResult,
    pub right_real: VerifyFactResult,
    pub image_equality: Box<EqualFactSearchedProof>,
}
impl ExpInjectiveProof {
    pub fn new(left_real: VerifyFactResult, right_real: VerifyFactResult, image_equality: EqualFactSearchedProof) -> Self {
        Self { left_real, right_real, image_equality: Box::new(image_equality) }
    }
}
pub struct LnInjectiveProof {
    pub left_positive: VerifyFactResult,
    pub right_positive: VerifyFactResult,
    pub image_equality: Box<EqualFactSearchedProof>,
}
impl LnInjectiveProof {
    pub fn new(left_positive: VerifyFactResult, right_positive: VerifyFactResult, image_equality: EqualFactSearchedProof) -> Self {
        Self { left_positive, right_positive, image_equality: Box::new(image_equality) }
    }
}
pub struct LogFromKnownPowerProof {
    pub base_proof: LogAlgebraBaseProof,
    pub exponent_integer: VerifyFactResult,
    pub power_equality: Box<EqualFactSearchedProof>,
}
impl LogFromKnownPowerProof {
    pub fn new(base_proof: LogAlgebraBaseProof, exponent_integer: VerifyFactResult, power_equality: EqualFactSearchedProof) -> Self {
        Self { base_proof, exponent_integer, power_equality: Box::new(power_equality) }
    }
}
pub struct PowerFromKnownLogProof {
    pub base_proof: LogAlgebraBaseProof,
    pub argument_positive: VerifyFactResult,
    pub exponent_integer: VerifyFactResult,
    pub logarithm_equality: Box<EqualFactSearchedProof>,
}
impl PowerFromKnownLogProof {
    pub fn new(base_proof: LogAlgebraBaseProof, argument_positive: VerifyFactResult, exponent_integer: VerifyFactResult, logarithm_equality: EqualFactSearchedProof) -> Self {
        Self { base_proof, argument_positive, exponent_integer, logarithm_equality: Box::new(logarithm_equality) }
    }
}
impl ExponentialLogarithmIdentityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::ExpDifference(_) => "ExpDifference",
            Self::LnProduct(_) => "LnProduct",
            Self::LnQuotient(_) => "LnQuotient",
            Self::ExpInjective(_) => "ExpInjective",
            Self::LnInjective(_) => "LnInjective",
            Self::LogFromKnownPower(_) => "LogFromKnownPower",
            Self::PowerFromKnownLog(_) => "PowerFromKnownLog",
        }
    }
}
impl Runtime {
    pub(super) fn search_exponential_logarithm_identity(
        &mut self, fact: &EqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<ExponentialLogarithmIdentityProof>> {
        use ExponentialLogarithmIdentityProof as P;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            // exp(a-b)=exp(a)/exp(b); the exponential denominator is nonzero.
            if let Obj::ExpLogOperator(E::Exp(exp)) = left {
                if let Obj::ArithmeticOperator(A::Sub(sub)) = &*exp.arg {
                    let expected = divide(exponential(&sub.left), exponential(&sub.right));
                    if objs_equal_by_rational_expression_evaluation(right, &expected) {
                        return Ok(Some(P::ExpDifference(ExpDifferenceProof)));
                    }
                }
            }
            // ln(a*b)=ln(a)+ln(b), ln(a/b)=ln(a)-ln(b), for positive a,b.
            if let Obj::ExpLogOperator(E::Ln(ln)) = left {
                match &*ln.arg {
                    Obj::ArithmeticOperator(A::Mul(product)) => {
                        let expected = Obj::ArithmeticOperator(A::Add(Add {
                            left: Box::new(logarithm(&product.left)), right: Box::new(logarithm(&product.right)),
                        }));
                        if objs_equal_by_rational_expression_evaluation(right, &expected) {
                            return Ok(Some(P::LnProduct(LnProductProof)));
                        }
                    }
                    Obj::ArithmeticOperator(A::Div(quotient)) => {
                        let expected = Obj::ArithmeticOperator(A::Sub(Sub {
                            left: Box::new(logarithm(&quotient.left)), right: Box::new(logarithm(&quotient.right)),
                        }));
                        if objs_equal_by_rational_expression_evaluation(right, &expected) {
                            return Ok(Some(P::LnQuotient(LnQuotientProof)));
                        }
                    }
                    _ => {}
                }
            }
            // a^n=x => log(a,x)=n, with a positive nonunit and n integer.
            if let Obj::ExpLogOperator(E::Log(log)) = left {
                let power = Obj::ArithmeticOperator(A::Pow(Pow { base: log.base.clone(), exponent: Box::new(right.clone()) }));
                if let Some(power_equality) = self.lookup_exact_property_obj_equality(&power, &log.arg) {
                    if let Some(base_proof) = self.verify_log_algebra_base_guard(&log.base, state)? {
                        let exponent_integer = self.exponential_logarithm_member(right, StandardSet::Z, state)?;
                        if !exponent_integer.is_failed() {
                            return Ok(Some(P::LogFromKnownPower(LogFromKnownPowerProof::new(base_proof, exponent_integer, power_equality))));
                        }
                    }
                }
            }
            // log(a,x)=n => a^n=x, including a literal log exponent proved in Z.
            if let Obj::ArithmeticOperator(A::Pow(power)) = left {
                let log = Obj::ExpLogOperator(E::Log(Log { base: power.base.clone(), arg: Box::new(right.clone()) }));
                if let Some(logarithm_equality) = self.lookup_exact_property_obj_equality(&log, &power.exponent) {
                    if let Some(base_proof) = self.verify_log_algebra_base_guard(&power.base, state)? {
                        let argument_positive = self.verify_log_algebra_positive(right, state)?;
                        let exponent_integer = self.exponential_logarithm_member(&power.exponent, StandardSet::Z, state)?;
                        if !argument_positive.is_failed() && !exponent_integer.is_failed() {
                            return Ok(Some(P::PowerFromKnownLog(PowerFromKnownLogProof::new(base_proof, argument_positive, exponent_integer, logarithm_equality))));
                        }
                    }
                }
            }
        }
        // Injectivity consumes the two exact image endpoints, never scans a graph.
        if let Some(image_equality) = self.lookup_exact_property_obj_equality(&exponential(&fact.left), &exponential(&fact.right)) {
            let left_real = self.exponential_logarithm_member(&fact.left, StandardSet::R, state)?;
            let right_real = self.exponential_logarithm_member(&fact.right, StandardSet::R, state)?;
            if !left_real.is_failed() && !right_real.is_failed() {
                return Ok(Some(P::ExpInjective(ExpInjectiveProof::new(left_real, right_real, image_equality))));
            }
        }
        if let Some(image_equality) = self.lookup_exact_property_obj_equality(&logarithm(&fact.left), &logarithm(&fact.right)) {
            let left_positive = self.exponential_logarithm_member(&fact.left, StandardSet::RPos, state)?;
            let right_positive = self.exponential_logarithm_member(&fact.right, StandardSet::RPos, state)?;
            if !left_positive.is_failed() && !right_positive.is_failed() {
                return Ok(Some(P::LnInjective(LnInjectiveProof::new(left_positive, right_positive, image_equality))));
            }
        }
        Ok(None)
    }

    fn exponential_logarithm_member(
        &mut self, element: &Obj, set: StandardSet, state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let requirement: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: element.clone(),
            set: Obj::StandardSet(set), line_file: None,
        }.into();
        self.verify_builtin_rule_premise(&requirement, state)
    }
}
fn exponential(arg: &Obj) -> Obj {
    Obj::ExpLogOperator(E::Exp(Exp { arg: Box::new(arg.clone()) }))
}
fn logarithm(arg: &Obj) -> Obj {
    Obj::ExpLogOperator(E::Ln(Ln { arg: Box::new(arg.clone()) }))
}
fn divide(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Div(Div { left: Box::new(left), right: Box::new(right) }))
}
